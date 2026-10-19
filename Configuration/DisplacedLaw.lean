import Riesz.Configuration.ShellLabels
import Riesz.Stationary.GaussianMoments
import Riesz.Stationary.NegativeDisplacement
import Mathlib.Probability.Independence.InfinitePi

/-!
Independent normalized heat displacement of every counting label, including
repeated labels at the same original site. The output is an ambient measure.
-/

noncomputable section
open MeasureTheory RieszShowcase Riesz.Stationary
open scoped ENNReal Classical
namespace Riesz.Configuration

abbrev DisplacementMarks (d : ℕ) := (ℕ × ℕ) → Rd d

def heatDisplacementLaw (d : ℕ) (t : ℝ) : Measure (Rd d) :=
  volume.withDensity (fun z => ENNReal.ofReal (originalHeatGaussian d t z))

theorem heatDisplacementLaw_probability (d : ℕ) (t : ℝ) (ht : 0 < t) :
    IsProbabilityMeasure (heatDisplacementLaw d t) := by
  constructor
  rw [heatDisplacementLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  simpa only [zero_sub, originalHeatGaussian, norm_neg] using
    lintegral_originalHeatGaussian d t ht (0 : Rd d)

theorem heatDisplacementLaw_nullSingletonClass
    (d : ℕ) (hd : 0 < d) (t : ℝ) :
    NullSingletonClass (heatDisplacementLaw d t) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact inferInstanceAs (NullSingletonClass (volume.withDensity
    (fun z : Rd d => ENNReal.ofReal (originalHeatGaussian d t z))))

def heatDisplacementMarksLaw (d : ℕ) (t : ℝ) :
    Measure (DisplacementMarks d) :=
  Measure.infinitePi (fun _ : ℕ × ℕ => heatDisplacementLaw d t)

theorem heatDisplacementMarksLaw_probability
    (d : ℕ) (t : ℝ) (ht : 0 < t) :
    IsProbabilityMeasure (heatDisplacementMarksLaw d t) := by
  letI := heatDisplacementLaw_probability d t ht
  exact inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi (fun _ : ℕ × ℕ => heatDisplacementLaw d t)))

private def displacedSite (d : ℕ) (ij : ℕ × ℕ)
    (p : CountingConfiguration d × DisplacementMarks d) : Rd d :=
  countingShellPosition d ij.1 ij.2 p.1 + p.2 ij

private theorem measurable_displacedSite (d : ℕ) (ij : ℕ × ℕ) :
    Measurable (displacedSite d ij) := by
  exact ((measurable_countingShellPosition d ij.1 ij.2).comp measurable_fst).add
    ((measurable_pi_apply ij).comp measurable_snd)

private def displacedShellAtom (d : ℕ) (ij : ℕ × ℕ)
    (p : CountingConfiguration d × DisplacementMarks d) : Measure (Rd d) :=
  if ij.2 < countingShellCount d ij.1 p.1 then
    Measure.dirac (displacedSite d ij p)
  else 0

def displacedAmbient (d : ℕ)
    (p : CountingConfiguration d × DisplacementMarks d) : Measure (Rd d) :=
  Measure.sum (fun ij : ℕ × ℕ => displacedShellAtom d ij p)

private theorem measurable_displacedShellAtom (d : ℕ) (ij : ℕ × ℕ) :
    Measurable (displacedShellAtom d ij) := by
  exact Measurable.ite
    (measurableSet_lt measurable_const
      ((measurable_countingShellCount d ij.1).comp measurable_fst))
    (Measure.measurable_dirac.comp (measurable_displacedSite d ij))
    measurable_const

theorem measurable_displacedAmbient (d : ℕ) :
    Measurable (displacedAmbient d) := by
  refine Measure.measurable_of_measurable_coe _ (fun D hD => ?_)
  simp only [displacedAmbient, Measure.sum_apply _ hD]
  exact Measurable.tsum (fun ij => (Measure.measurable_coe hD).comp
    (measurable_displacedShellAtom d ij))

def displacedLaw (d : ℕ) (t : ℝ) (P : Measure (CountingConfiguration d)) :
    ConfigurationLaw d :=
  (P.prod (heatDisplacementMarksLaw d t)).map (displacedAmbient d)

theorem displacedLaw_probability
    (d : ℕ) (t : ℝ) (ht : 0 < t) (P : Measure (CountingConfiguration d))
    [IsProbabilityMeasure P] : IsProbabilityMeasure (displacedLaw d t P) := by
  letI := heatDisplacementMarksLaw_probability d t ht
  exact Measure.isProbabilityMeasure_map (measurable_displacedAmbient d).aemeasurable

private theorem lintegral_displacedShellAtom_marks
    (d : ℕ) (t : ℝ) (ht : 0 < t) (μ : CountingConfiguration d)
    (h : Rd d → ℝ≥0∞) (hh : Measurable h) (ij : ℕ × ℕ) :
    (∫⁻ z, ∫⁻ y, h y ∂displacedShellAtom d ij (μ,z)
      ∂heatDisplacementMarksLaw d t) =
      if ij.2 < countingShellCount d ij.1 μ then
        ∫⁻ z, h (countingShellPosition d ij.1 ij.2 μ + z)
          ∂heatDisplacementLaw d t else 0 := by
  letI := heatDisplacementLaw_probability d t ht
  by_cases ha : ij.2 < countingShellCount d ij.1 μ
  · simp only [displacedShellAtom, ha, if_pos, lintegral_dirac, displacedSite]
    simpa only [heatDisplacementMarksLaw, Measure.infinitePi_map_eval,
      Function.comp_apply, Pi.add_apply, id_eq] using
      (lintegral_map (hh.comp (measurable_const.add measurable_id))
        (measurable_pi_apply ij)
        (μ := heatDisplacementMarksLaw d t)).symm
  · simp [displacedShellAtom, ha]

theorem lintegral_displacedAmbient_marks
    (d : ℕ) (t : ℝ) (ht : 0 < t) (μ : CountingConfiguration d)
    (h : Rd d → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ z, ∫⁻ y, h y ∂displacedAmbient d (μ,z)
      ∂heatDisplacementMarksLaw d t) =
      ∫⁻ x, ∫⁻ z, h (x + z) ∂heatDisplacementLaw d t ∂μ.val := by
  calc
    _ = ∫⁻ z, ∑' ij, ∫⁻ y, h y ∂displacedShellAtom d ij (μ,z)
        ∂heatDisplacementMarksLaw d t := by
      exact lintegral_congr (fun z => lintegral_sum_measure h _)
    _ = ∑' ij, ∫⁻ z, ∫⁻ y, h y ∂displacedShellAtom d ij (μ,z)
        ∂heatDisplacementMarksLaw d t := by
      exact lintegral_tsum (fun ij =>
        ((Measure.measurable_lintegral hh).comp
          ((measurable_displacedShellAtom d ij).comp
            (measurable_const.prodMk measurable_id))).aemeasurable)
    _ = ∑' ij : ℕ × ℕ, if ij.2 < countingShellCount d ij.1 μ then
        ∫⁻ z, h (countingShellPosition d ij.1 ij.2 μ + z)
          ∂heatDisplacementLaw d t else 0 := by
      exact tsum_congr (lintegral_displacedShellAtom_marks d t ht μ h hh)
    _ = _ := by
      rw [countingConfiguration_eq_sum_activeDirac d μ, lintegral_sum_measure]
      refine tsum_congr (fun ij => ?_)
      by_cases ha : ij.2 < countingShellCount d ij.1 μ <;>
        simp [countingShellAtom, ha]

theorem lintegral_displacedLaw
    (d : ℕ) (t : ℝ) (ht : 0 < t) (P : Measure (CountingConfiguration d))
    [IsProbabilityMeasure P] (h : Rd d → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ ν, ∫⁻ y, h y ∂ν ∂displacedLaw d t P) =
      ∫⁻ μ, ∫⁻ x, ∫⁻ z, h (x + z) ∂heatDisplacementLaw d t ∂μ.val ∂P := by
  letI := heatDisplacementMarksLaw_probability d t ht
  rw [displacedLaw, lintegral_map (Measure.measurable_lintegral hh)
    (measurable_displacedAmbient d)]
  rw [lintegral_prod _ (show AEMeasurable
      (fun p => ∫⁻ y, h y ∂displacedAmbient d p)
        (P.prod (heatDisplacementMarksLaw d t)) from
      ((Measure.measurable_lintegral hh).comp
        (measurable_displacedAmbient d)).aemeasurable)]
  exact lintegral_congr (fun μ => lintegral_displacedAmbient_marks d t ht μ h hh)

private theorem lintegral_displacedLaw_of_unitMean
    (d : ℕ) (t : ℝ) (ht : 0 < t) (P : Measure (CountingConfiguration d))
    [IsProbabilityMeasure P]
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d)))
    (h : Rd d → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ η, ∫⁻ y, h y ∂η ∂displacedLaw d t P) = ∫⁻ y, h y ∂volume := by
  letI := heatDisplacementLaw_probability d t ht
  let b : Rd d → ℝ≥0∞ :=
    fun x => ∫⁻ z, h (x + z) ∂heatDisplacementLaw d t
  have hb : Measurable b :=
    (hh.comp (measurable_fst.add measurable_snd)).lintegral_prod_right'
  calc
    _ = ∫⁻ μ, ∫⁻ x, b x ∂μ.val ∂P := lintegral_displacedLaw d t ht P h hh
    _ = ∫⁻ η, ∫⁻ x, b x ∂η ∂P.map Subtype.val :=
      (lintegral_map (Measure.measurable_lintegral hb) measurable_subtype_coe).symm
    _ = ∫⁻ x, b x ∂(P.map Subtype.val).join :=
      (Measure.lintegral_join hb.aemeasurable).symm
    _ = ∫⁻ x, b x ∂volume :=
      congrArg (fun M : Measure (Rd d) => ∫⁻ x, b x ∂M) hmean
    _ = ∫⁻ z, ∫⁻ x, h (x + z) ∂volume ∂heatDisplacementLaw d t :=
      lintegral_lintegral_swap
        ((hh.comp (measurable_fst.add measurable_snd)).aemeasurable)
    _ = ∫⁻ y, h y ∂volume := by
      simp only [lintegral_add_right_eq_self, lintegral_const, measure_univ, mul_one]

theorem displacedLaw_join_eq_volume
    (d : ℕ) (t : ℝ) (ht : 0 < t) (P : Measure (CountingConfiguration d))
    [IsProbabilityMeasure P]
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d))) :
    (displacedLaw d t P).join = (volume : Measure (Rd d)) := by
  ext D hD
  rw [Measure.join_apply hD]
  simpa only [lintegral_indicator hD, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul] using
    lintegral_displacedLaw_of_unitMean d t ht P hmean
      (D.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hD)

theorem displacedLaw_ae_closedBall_lt_top
    (d : ℕ) (t : ℝ) (ht : 0 < t) (P : Measure (CountingConfiguration d))
    [IsProbabilityMeasure P]
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d))) :
    ∀ᵐ η ∂displacedLaw d t P, ∀ n : ℕ,
      η (Metric.closedBall (0 : Rd d) (n : ℝ)) < ∞ := by
  refine ae_all_iff.mpr (fun n => ?_)
  apply ae_lt_top (Measure.measurable_coe measurableSet_closedBall)
  rw [← Measure.join_apply measurableSet_closedBall,
    displacedLaw_join_eq_volume d t ht P hmean]
  exact (isCompact_closedBall (0 : Rd d) (n : ℝ)).measure_ne_top

private theorem prod_ae_add_ne
    (d : ℕ) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (a b : Rd d) :
    ∀ᵐ q ∂ν.prod ν, a + q.1 ≠ b + q.2 := by
  have hC : MeasurableSet {q : Rd d × Rd d | q.2 = a + q.1 - b} :=
    measurableSet_eq_fun measurable_snd
      ((measurable_const.add measurable_fst).sub_const b)
  have hnull : (ν.prod ν) {q : Rd d × Rd d | q.2 = a + q.1 - b} = 0 :=
    (Measure.measure_prod_null hC).2 (Filter.Eventually.of_forall (fun u =>
      (show ν {a + u - b} = 0 from measure_singleton _)))
  have hae : ∀ᵐ q ∂ν.prod ν, q.2 ≠ a + q.1 - b := by
    simpa only [ae_iff, not_not] using hnull
  exact hae.mono (fun q hq heq =>
    hq ((eq_sub_iff_add_eq).2 ((add_comm q.2 b).trans heq.symm)))

private theorem heatDisplacementMarksLaw_ae_pair_ne
    (d : ℕ) (hd : 0 < d) (t : ℝ) (ht : 0 < t)
    (μ : CountingConfiguration d) (i j : ℕ × ℕ) (hij : i ≠ j) :
    ∀ᵐ z ∂heatDisplacementMarksLaw d t,
      displacedSite d i (μ,z) ≠ displacedSite d j (μ,z) := by
  letI := heatDisplacementLaw_probability d t ht
  letI := heatDisplacementLaw_nullSingletonClass d hd t
  exact ae_of_ae_map
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
    ((Measure.infinitePi_map_eval_prod
      (P := fun _ : ℕ × ℕ => heatDisplacementLaw d t) hij).symm ▸
        prod_ae_add_ne d (heatDisplacementLaw d t)
          (countingShellPosition d i.1 i.2 μ) (countingShellPosition d j.1 j.2 μ))

private theorem heatDisplacementMarksLaw_ae_injective
    (d : ℕ) (hd : 0 < d) (t : ℝ) (ht : 0 < t)
    (μ : CountingConfiguration d) :
    ∀ᵐ z ∂heatDisplacementMarksLaw d t,
      Function.Injective (fun ij => displacedSite d ij (μ,z)) := by
  have hpairs : ∀ i j : ℕ × ℕ, ∀ᵐ z ∂heatDisplacementMarksLaw d t,
      displacedSite d i (μ,z) = displacedSite d j (μ,z) → i = j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ _ => hij)
    · exact (heatDisplacementMarksLaw_ae_pair_ne d hd t ht μ i j hij).mono
        (fun _ hz heq => False.elim (hz heq))
  simpa only [Function.Injective] using
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hpairs i j))

private theorem measurableSet_displacedSite_injective (d : ℕ) :
    MeasurableSet {p : CountingConfiguration d × DisplacementMarks d |
      Function.Injective (fun ij => displacedSite d ij p)} := by
  simpa only [Function.Injective, Set.mem_setOf_eq] using
    (Measurable.forall (fun i : ℕ × ℕ => Measurable.forall (fun j : ℕ × ℕ =>
      (measurableSet_eq_fun (measurable_displacedSite d i)
        (measurable_displacedSite d j)).mem.imp
        (measurable_const (a := i = j))))).setOf

private theorem displacedSites_ae_injective
    (d : ℕ) (hd : 0 < d) (t : ℝ) (ht : 0 < t)
    (P : Measure (CountingConfiguration d)) [IsProbabilityMeasure P] :
    ∀ᵐ p ∂P.prod (heatDisplacementMarksLaw d t),
      Function.Injective (fun ij => displacedSite d ij p) := by
  letI := heatDisplacementMarksLaw_probability d t ht
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_displacedSite_injective d)).2
    (Filter.Eventually.of_forall (fun μ =>
      heatDisplacementMarksLaw_ae_injective d hd t ht μ))

private theorem simple_sum_dirac_of_closedBall_lt_top
    (d : ℕ) {ι : Type*} (x : ι → Rd d) (hx : Function.Injective x)
    (hlocal : ∀ n : ℕ,
      (Measure.sum (fun i => Measure.dirac (x i)))
        (Metric.closedBall (0 : Rd d) (n : ℝ)) < ∞) :
    IsSimpleConfiguration d (Measure.sum (fun i => Measure.dirac (x i))) := by
  refine ⟨Set.range x, ?_, ?_⟩
  · intro K hK
    obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
    obtain ⟨n,hn⟩ := exists_nat_ge R
    have hsub : K ⊆ Metric.closedBall (0 : Rd d) (n : ℝ) :=
      fun y hy => (Metric.mem_closedBall).2
        (by simpa only [dist_zero_right] using (hR y hy).trans hn)
    have hmass : (Measure.sum (fun i => Measure.dirac (x i))) K < ∞ :=
      (measure_mono hsub).trans_lt (hlocal n)
    have hsum : (∑' i, (Measure.dirac (x i)) K) ≠ ∞ :=
      (Measure.sum_apply _ hK.measurableSet) ▸ hmass.ne
    have hI := ENNReal.finite_const_le_of_tsum_ne_top hsum
      (show (1 : ℝ≥0∞) ≠ 0 from one_ne_zero)
    refine (hI.image x).subset ?_
    rintro y ⟨⟨i,rfl⟩,hi⟩
    refine ⟨i, ?_, rfl⟩
    simp [Measure.dirac_apply' _ hK.measurableSet, hi]
  · exact Measure.sum_comp_equiv (Equiv.ofInjective x hx)
      (fun y : Set.range x => Measure.dirac y.val)

private theorem displacedAmbient_simple_of_local
    (d : ℕ) (p : CountingConfiguration d × DisplacementMarks d)
    (hinj : Function.Injective (fun ij => displacedSite d ij p))
    (hlocal : ∀ n : ℕ, displacedAmbient d p
      (Metric.closedBall (0 : Rd d) (n : ℝ)) < ∞) :
    IsSimpleConfiguration d (displacedAmbient d p) := by
  let I := {ij : ℕ × ℕ // ij.2 < countingShellCount d ij.1 p.1}
  let x : I → Rd d := fun i => displacedSite d i.val p
  have hsum : displacedAmbient d p = Measure.sum (fun i : I => Measure.dirac (x i)) := by
    ext D hD
    rw [displacedAmbient, Measure.sum_apply _ hD, Measure.sum_apply _ hD]
    erw [tsum_subtype {ij : ℕ × ℕ | ij.2 < countingShellCount d ij.1 p.1}
      (fun ij => (Measure.dirac (displacedSite d ij p)) D)]
    refine tsum_congr (fun ij => ?_)
    by_cases ha : ij.2 < countingShellCount d ij.1 p.1 <;>
      simp [displacedShellAtom, Set.indicator, ha]
  exact hsum.symm ▸ simple_sum_dirac_of_closedBall_lt_top d x
    (hinj.comp Subtype.val_injective) (fun n => hsum ▸ hlocal n)

theorem displacedLaw_ae_simple
    (d : ℕ) (hd : 0 < d) (t : ℝ) (ht : 0 < t)
    (P : Measure (CountingConfiguration d)) [IsProbabilityMeasure P]
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d))) :
    ∀ᵐ η ∂displacedLaw d t P, IsSimpleConfiguration d η := by
  have hlocal : ∀ᵐ p ∂P.prod (heatDisplacementMarksLaw d t), ∀ n : ℕ,
      displacedAmbient d p (Metric.closedBall (0 : Rd d) (n : ℝ)) < ∞ :=
    ae_of_ae_map (measurable_displacedAmbient d).aemeasurable
      (displacedLaw_ae_closedBall_lt_top d t ht P hmean)
  rw [displacedLaw, ae_map_iff (measurable_displacedAmbient d).aemeasurable
    (measurableSet_isSimpleConfiguration d)]
  exact (hlocal.and (displacedSites_ae_injective d hd t ht P)).mono
    (fun p hp => displacedAmbient_simple_of_local d p hp.2 hp.1)

private theorem finite_dirac_siteFiber (d : ℕ) {ι : Type*}
    (x : ι → Rd d) (z : Rd d)
    (hfinite : (Measure.sum (fun i => Measure.dirac (x i))) {z} ≠ ∞) :
    {i | x i = z}.Finite := by
  have hs : (∑' i, (Measure.dirac (x i)) {z}) ≠ ∞ :=
    (Measure.sum_apply _ (measurableSet_singleton z)) ▸ hfinite
  exact (ENNReal.finite_const_le_of_tsum_ne_top hs one_ne_zero).subset
    (fun i hi => by simp [show x i = z from hi])

private theorem sum_dirac_singleton_eq_card (d : ℕ) {ι : Type*}
    (x : ι → Rd d) (z : Rd d) [Fintype {i // x i = z}] :
    (Measure.sum (fun i => Measure.dirac (x i))) {z} =
      (Fintype.card {i // x i = z} : ℝ≥0∞) := by
  calc
    _ = ∑' i : ι, (Measure.dirac (x i)) {z} :=
      Measure.sum_apply _ (measurableSet_singleton z)
    _ = ∑' _ : {i // x i = z}, (1 : ℝ≥0∞) := by
      erw [tsum_subtype {i | x i = z} (fun _ : ι => (1 : ℝ≥0∞))]
      refine tsum_congr (fun i => ?_)
      by_cases hi : x i = z <;> simp [Set.indicator, hi]
    _ = _ := by
      simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

private theorem exists_sitePreservingEquiv (d : ℕ) {ι κ : Type*}
    (x : ι → Rd d) (y : κ → Rd d)
    (hsum : Measure.sum (fun i => Measure.dirac (x i)) =
      Measure.sum (fun j => Measure.dirac (y j)))
    (hfinite : ∀ z, (Measure.sum (fun i => Measure.dirac (x i))) {z} ≠ ∞) :
    ∃ e : ι ≃ κ, ∀ i, y (e i) = x i := by
  let ef : ∀ z : Rd d, {i // x i = z} ≃ {j // y j = z} := fun z => by
    letI : Fintype {i // x i = z} :=
      (finite_dirac_siteFiber d x z (hfinite z)).fintype
    letI : Fintype {j // y j = z} :=
      (finite_dirac_siteFiber d y z (hsum ▸ hfinite z)).fintype
    apply Fintype.equivOfCardEq
    have hcard : (Fintype.card {i // x i = z} : ℝ≥0∞) =
        (Fintype.card {j // y j = z} : ℝ≥0∞) :=
      (sum_dirac_singleton_eq_card d x z).symm.trans
        ((congrArg (fun M : Measure (Rd d) => M {z}) hsum).trans
          (sum_dirac_singleton_eq_card d y z))
    exact_mod_cast hcard
  exact ⟨Equiv.ofFiberEquiv ef, fun i => Equiv.ofFiberEquiv_map ef i⟩

private abbrev ActiveShellIndex (d : ℕ) (μ : CountingConfiguration d) :=
  {ij : ℕ × ℕ // ij.2 < countingShellCount d ij.1 μ}

private def activeShellSite (d : ℕ) (μ : CountingConfiguration d)
    (i : ActiveShellIndex d μ) : Rd d :=
  countingShellPosition d i.val.1 i.val.2 μ

private theorem sum_activeShellSite_eq (d : ℕ) (μ : CountingConfiguration d) :
    Measure.sum (fun i : ActiveShellIndex d μ => Measure.dirac (activeShellSite d μ i)) =
      μ.val := by
  rw [countingConfiguration_eq_sum_activeDirac d μ]
  ext D hD
  simp only [Measure.sum_apply _ hD]
  erw [tsum_subtype {ij : ℕ × ℕ | ij.2 < countingShellCount d ij.1 μ}
    (fun ij => (Measure.dirac (countingShellPosition d ij.1 ij.2 μ)) D)]
  refine tsum_congr (fun ij => ?_)
  by_cases ha : ij.2 < countingShellCount d ij.1 μ <;>
    simp [countingShellAtom, Set.indicator, ha]

private def markedDiracSum (d : ℕ) {ι : Type*} (x : ι → Rd d)
    (z : ι → Rd d) : Measure (Rd d) :=
  Measure.sum (fun i => Measure.dirac (x i + z i))

private theorem measurable_markedDiracSum (d : ℕ) {ι : Type*} [Countable ι]
    (x : ι → Rd d) : Measurable (markedDiracSum d x) := by
  refine Measure.measurable_of_measurable_coe _ (fun D hD => ?_)
  simp only [markedDiracSum, Measure.sum_apply _ hD]
  exact Measurable.tsum (fun i => (Measure.measurable_coe hD).comp
    (Measure.measurable_dirac.comp (measurable_const.add (measurable_pi_apply i))))

private theorem displacedAmbient_eq_active_sum (d : ℕ)
    (μ : CountingConfiguration d) (z : DisplacementMarks d) :
    displacedAmbient d (μ,z) = markedDiracSum d (activeShellSite d μ)
      (fun i : ActiveShellIndex d μ => z i.val) := by
  ext D hD
  simp only [displacedAmbient, markedDiracSum, Measure.sum_apply _ hD]
  erw [tsum_subtype {ij : ℕ × ℕ | ij.2 < countingShellCount d ij.1 μ}
    (fun ij => (Measure.dirac (countingShellPosition d ij.1 ij.2 μ + z ij)) D)]
  refine tsum_congr (fun ij => ?_)
  by_cases ha : ij.2 < countingShellCount d ij.1 μ <;>
    simp [displacedShellAtom, displacedSite, Set.indicator, ha]

private theorem displacedAmbient_marks_eq_active (d : ℕ) (t : ℝ) (ht : 0 < t)
    (μ : CountingConfiguration d) :
    (heatDisplacementMarksLaw d t).map (fun z => displacedAmbient d (μ,z)) =
      (Measure.infinitePi (fun _ : ActiveShellIndex d μ => heatDisplacementLaw d t)).map
        (markedDiracSum d (activeShellSite d μ)) := by
  letI := heatDisplacementLaw_probability d t ht
  calc
    _ = (heatDisplacementMarksLaw d t).map
        ((markedDiracSum d (activeShellSite d μ)) ∘
          (fun z i => z (i : ℕ × ℕ))) :=
      congrArg (fun f => (heatDisplacementMarksLaw d t).map f)
        (funext (displacedAmbient_eq_active_sum d μ))
    _ = ((heatDisplacementMarksLaw d t).map
        (fun z (i : ActiveShellIndex d μ) => z i.val)).map
          (markedDiracSum d (activeShellSite d μ)) :=
      (Measure.map_map (measurable_markedDiracSum d _) (by fun_prop)).symm
    _ = _ := by
      rw [heatDisplacementMarksLaw,
        Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]

private theorem markedDiracSum_law_translate (d : ℕ)
    {ι κ : Type*} [Countable ι] [Countable κ]
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    (x : ι → Rd d) (y : κ → Rd d) (a : Rd d)
    (e : ι ≃ κ) (he : ∀ i, y (e i) = a + x i) :
    ((Measure.infinitePi (fun _ : ι => ν)).map (markedDiracSum d x)).map
      (fun M => M.map (fun q => a + q)) =
    (Measure.infinitePi (fun _ : κ => ν)).map (markedDiracSum d y) := by
  let r : (κ → Rd d) → (ι → Rd d) := fun z i => z (e i)
  have hr : (Measure.infinitePi (fun _ : κ => ν)).map r =
      Measure.infinitePi (fun _ : ι => ν) :=
    Measure.map_infinitePi_infinitePi_of_inj e.injective
  have htau : Measurable (fun q : Rd d => a + q) := measurable_const.add measurable_id
  have hT := Measure.measurable_map (fun q : Rd d => a + q) htau
  have hpoint : ∀ z : κ → Rd d,
      (markedDiracSum d x (r z)).map (fun q => a + q) = markedDiracSum d y z := by
    intro z
    calc
      _ = Measure.sum (fun i => Measure.dirac (a + (x i + z (e i)))) := by
        simp only [markedDiracSum, Measure.map_sum htau.aemeasurable,
          Measure.map_dirac' htau, r]
      _ = Measure.sum ((fun j => Measure.dirac (y j + z j)) ∘ e) := by
        exact congrArg Measure.sum (funext (fun i => by
          simp only [Function.comp_apply, he, add_assoc]))
      _ = _ := Measure.sum_comp_equiv e _
  rw [Measure.map_map hT (measurable_markedDiracSum d x), ← hr,
    Measure.map_map (hT.comp (measurable_markedDiracSum d x)) (by fun_prop)]
  exact congrArg (fun f => (Measure.infinitePi (fun _ : κ => ν)).map f) (funext hpoint)

private theorem displacedAmbient_marks_translate (d : ℕ) (t : ℝ) (ht : 0 < t)
    (μ : CountingConfiguration d) (a : Rd d) :
    ((heatDisplacementMarksLaw d t).map (fun z => displacedAmbient d (μ,z))).map
      (fun M => M.map (fun q => a + q)) =
    (heatDisplacementMarksLaw d t).map
      (fun z => displacedAmbient d (translateCounting d a μ,z)) := by
  let ν0 := translateCounting d a μ
  have htau : Measurable (fun q : Rd d => a + q) := measurable_const.add measurable_id
  have hx : Measure.sum (fun i => Measure.dirac (a + activeShellSite d μ i)) =
      μ.val.map (fun q => a + q) := by
    simpa only [Measure.map_sum htau.aemeasurable, Measure.map_dirac' htau] using
      congrArg (fun M : Measure (Rd d) => M.map (fun q => a + q))
        (sum_activeShellSite_eq d μ)
  have hsum : Measure.sum (fun i => Measure.dirac (a + activeShellSite d μ i)) =
      Measure.sum (fun j => Measure.dirac (activeShellSite d ν0 j)) :=
    hx.trans (sum_activeShellSite_eq d ν0).symm
  have hfinite : ∀ z, (Measure.sum
      (fun i => Measure.dirac (a + activeShellSite d μ i))) {z} ≠ ∞ := by
    intro z
    exact hx.symm ▸ (show ν0.val {z} ≠ ∞ from
      (isCompact_singleton : IsCompact ({z} : Set (Rd d))).measure_ne_top)
  obtain ⟨e,he⟩ := exists_sitePreservingEquiv d
    (fun i => a + activeShellSite d μ i) (activeShellSite d ν0) hsum hfinite
  letI := heatDisplacementLaw_probability d t ht
  rw [displacedAmbient_marks_eq_active d t ht μ,
    displacedAmbient_marks_eq_active d t ht (translateCounting d a μ)]
  exact markedDiracSum_law_translate d (heatDisplacementLaw d t)
    (activeShellSite d μ) (activeShellSite d ν0) a e he

private theorem map_prod_eq_of_section_map_eq
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (P : Measure α) (G : Measure β) [SFinite G]
    (f g : α × β → γ) (hf : Measurable f) (hg : Measurable g)
    (hsections : ∀ x, G.map (fun z => f (x,z)) = G.map (fun z => g (x,z))) :
    (P.prod G).map f = (P.prod G).map g := by
  ext D hD
  rw [Measure.map_apply hf hD, Measure.map_apply hg hD,
    Measure.prod_apply (hf hD), Measure.prod_apply (hg hD)]
  refine lintegral_congr (fun x => ?_)
  change G ((fun z => f (x,z)) ⁻¹' D) = G ((fun z => g (x,z)) ⁻¹' D)
  simpa only [Measure.map_apply
      (show Measurable (fun z => f (x,z)) from hf.comp measurable_prodMk_left) hD,
    Measure.map_apply
      (show Measurable (fun z => g (x,z)) from hg.comp measurable_prodMk_left) hD] using
    congrArg (fun M : Measure γ => M D) (hsections x)

theorem displacedLaw_isStationary (d : ℕ) (t : ℝ) (ht : 0 < t)
    (P : Measure (CountingConfiguration d)) [IsProbabilityMeasure P]
    (hstationary : IsStationary d (P.map Subtype.val)) :
    IsStationary d (displacedLaw d t P) := by
  letI := heatDisplacementMarksLaw_probability d t ht
  intro a
  have hT : Measurable (fun M : Measure (Rd d) => M.map (fun q => a + q)) :=
    Measure.measurable_map _ (measurable_const.add measurable_id)
  have hB : Measurable (Prod.map (translateCounting d a)
      (id : DisplacementMarks d → DisplacementMarks d)) :=
    (measurable_translateCounting d a).prodMap measurable_id
  have hprod : (P.prod (heatDisplacementMarksLaw d t)).map
      (Prod.map (translateCounting d a) id) =
      (P.map (translateCounting d a)).prod (heatDisplacementMarksLaw d t) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map P (heatDisplacementMarksLaw d t)
        (measurable_translateCounting d a) measurable_id).symm
  calc
    _ = (P.prod (heatDisplacementMarksLaw d t)).map
        ((fun M => M.map (fun q => a + q)) ∘ displacedAmbient d) :=
      Measure.map_map hT (measurable_displacedAmbient d)
    _ = (P.prod (heatDisplacementMarksLaw d t)).map
        (displacedAmbient d ∘ Prod.map (translateCounting d a) id) := by
      apply map_prod_eq_of_section_map_eq P (heatDisplacementMarksLaw d t)
        _ _ (hT.comp (measurable_displacedAmbient d))
        ((measurable_displacedAmbient d).comp hB)
      intro μ
      exact (Measure.map_map hT
        (show Measurable (fun z => displacedAmbient d (μ,z)) from
          (measurable_displacedAmbient d).comp measurable_prodMk_left)).symm.trans
        (displacedAmbient_marks_translate d t ht μ a)
    _ = ((P.prod (heatDisplacementMarksLaw d t)).map
        (Prod.map (translateCounting d a) id)).map (displacedAmbient d) :=
      (Measure.map_map (measurable_displacedAmbient d) hB).symm
    _ = displacedLaw d t P := by
      rw [hprod, map_translateCounting_eq_of_isStationary d P hstationary a]
      rfl

private theorem lintegral_iid_pair_sites (d : ℕ) {ι : Type*}
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] (x : ι → Rd d)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) (i j : ι) :
    (∫⁻ z, k (x i + z i, x j + z j)
      ∂Measure.infinitePi (fun _ : ι => ν)) =
      if i = j then ∫⁻ v, k (x i + v, x i + v) ∂ν
      else ∫⁻ v, ∫⁻ w, k (x i + v, x j + w) ∂ν ∂ν := by
  by_cases hij : i = j
  · subst j
    simpa only [eq_self, ite_true, Measure.infinitePi_map_eval] using
      (lintegral_map
        (show Measurable (fun v : Rd d => k (x i + v, x i + v)) from
          hk.comp ((measurable_const.add measurable_id).prodMk
            (measurable_const.add measurable_id)))
        (measurable_pi_apply i) (μ := Measure.infinitePi (fun _ : ι => ν))).symm
  · simp only [if_neg hij]
    have hf : Measurable (fun q : Rd d × Rd d => k (x i + q.1, x j + q.2)) :=
      hk.comp ((measurable_const.add measurable_fst).prodMk
        (measurable_const.add measurable_snd))
    calc
      _ = ∫⁻ q, k (x i + q.1, x j + q.2)
          ∂(Measure.infinitePi (fun _ : ι => ν)).map (fun z => (z i,z j)) :=
        (lintegral_map hf ((measurable_pi_apply i).prodMk
          (measurable_pi_apply j))).symm
      _ = ∫⁻ q, k (x i + q.1, x j + q.2) ∂ν.prod ν := by
        rw [Measure.infinitePi_map_eval_prod hij]
      _ = _ := lintegral_prod _ hf.aemeasurable

/-- NN Tonelli for iid marked ordered labels. Equal labels share one mark;
unequal labels use independent marks even when their original sites coincide. -/
theorem lintegral_iid_weighted_pair_sum (d : ℕ) {ι : Type*} [Countable ι]
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] (x : ι → Rd d)
    (c : ι × ι → ℝ≥0∞) (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ z, ∑' ij : ι × ι, c ij * k (x ij.1 + z ij.1, x ij.2 + z ij.2)
      ∂Measure.infinitePi (fun _ : ι => ν)) =
      ∑' ij : ι × ι, c ij *
        (if ij.1 = ij.2 then ∫⁻ v, k (x ij.1 + v, x ij.1 + v) ∂ν
         else ∫⁻ v, ∫⁻ w, k (x ij.1 + v, x ij.2 + w) ∂ν ∂ν) := by
  have hpair (ij : ι × ι) : Measurable (fun z : ι → Rd d =>
      k (x ij.1 + z ij.1, x ij.2 + z ij.2)) :=
    hk.comp ((measurable_const.add (measurable_pi_apply ij.1)).prodMk
      (measurable_const.add (measurable_pi_apply ij.2)))
  rw [lintegral_tsum (μ := Measure.infinitePi (fun _ : ι => ν)) (fun ij =>
    (show Measurable (fun z : ι → Rd d =>
        c ij * k (x ij.1 + z ij.1, x ij.2 + z ij.2)) from
      measurable_const.mul (hpair ij)).aemeasurable)]
  refine tsum_congr (fun ij => ?_)
  rw [lintegral_const_mul (c ij) (hpair ij),
    lintegral_iid_pair_sites d ν x k hk ij.1 ij.2]

private theorem displacedShellAtom_sFinite (d : ℕ) (i : ℕ × ℕ)
    (p : CountingConfiguration d × DisplacementMarks d) :
    SFinite (displacedShellAtom d i p) := by
  dsimp [displacedShellAtom]
  split_ifs <;> infer_instance

private theorem displacedAmbient_prod_lintegral_eq_tsum
    (d : ℕ) (μ : CountingConfiguration d) (z : DisplacementMarks d)
    (k : Rd d × Rd d → ℝ≥0∞) :
    (∫⁻ q, k q ∂(displacedAmbient d (μ,z)).prod (displacedAmbient d (μ,z))) =
      ∑' ij : (ℕ × ℕ) × (ℕ × ℕ),
        if ij.1.2 < countingShellCount d ij.1.1 μ ∧
            ij.2.2 < countingShellCount d ij.2.1 μ then
          k (countingShellPosition d ij.1.1 ij.1.2 μ + z ij.1,
             countingShellPosition d ij.2.1 ij.2.2 μ + z ij.2)
        else 0 := by
  letI (i : ℕ × ℕ) : SFinite (displacedShellAtom d i (μ,z)) :=
    displacedShellAtom_sFinite d i (μ,z)
  simp only [displacedAmbient, Measure.prod_sum, lintegral_sum_measure]
  refine tsum_congr (fun ij => ?_)
  by_cases hi : ij.1.2 < countingShellCount d ij.1.1 μ <;>
    by_cases hj : ij.2.2 < countingShellCount d ij.2.1 μ <;>
      simp [displacedShellAtom, displacedSite, hi, hj, Measure.dirac_prod_dirac]

/-- Actual conditional ordered-pair Campbell identity, with label multiplicities. -/
theorem lintegral_displacedAmbient_prod_marks
    (d : ℕ) (t : ℝ) (ht : 0 < t) (μ : CountingConfiguration d)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ z, ∫⁻ q, k q ∂(displacedAmbient d (μ,z)).prod
        (displacedAmbient d (μ,z)) ∂heatDisplacementMarksLaw d t) =
      ∑' ij : (ℕ × ℕ) × (ℕ × ℕ),
        (if ij.1.2 < countingShellCount d ij.1.1 μ ∧
            ij.2.2 < countingShellCount d ij.2.1 μ then (1 : ℝ≥0∞) else 0) *
        (if ij.1 = ij.2 then
          ∫⁻ v, k (countingShellPosition d ij.1.1 ij.1.2 μ + v,
            countingShellPosition d ij.1.1 ij.1.2 μ + v) ∂heatDisplacementLaw d t
         else ∫⁻ v, ∫⁻ w,
          k (countingShellPosition d ij.1.1 ij.1.2 μ + v,
            countingShellPosition d ij.2.1 ij.2.2 μ + w)
              ∂heatDisplacementLaw d t ∂heatDisplacementLaw d t) := by
  letI := heatDisplacementLaw_probability d t ht
  calc
    _ = ∫⁻ z, ∑' ij : (ℕ × ℕ) × (ℕ × ℕ),
        (if ij.1.2 < countingShellCount d ij.1.1 μ ∧
            ij.2.2 < countingShellCount d ij.2.1 μ then (1 : ℝ≥0∞) else 0) *
          k (countingShellPosition d ij.1.1 ij.1.2 μ + z ij.1,
            countingShellPosition d ij.2.1 ij.2.2 μ + z ij.2)
          ∂heatDisplacementMarksLaw d t := by
      exact lintegral_congr (fun z => by
        simpa only [ite_mul, one_mul, zero_mul] using
          displacedAmbient_prod_lintegral_eq_tsum d μ z k)
    _ = _ := lintegral_iid_weighted_pair_sum d (ι := ℕ × ℕ)
      (heatDisplacementLaw d t) (fun ij => countingShellPosition d ij.1 ij.2 μ)
      (fun ij => if ij.1.2 < countingShellCount d ij.1.1 μ ∧
        ij.2.2 < countingShellCount d ij.2.1 μ then 1 else 0) k hk
    _ = _ := tsum_congr (fun ij => by
      by_cases hij : ij.1 = ij.2 <;> simp only [hij, ↓reduceIte])

end Riesz.Configuration
