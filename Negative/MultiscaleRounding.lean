import Riesz.Negative.ScheduledRounding
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
Finite composition of cell rounding passes. A sequence of masks is part of
the measurable input, so sampled sites may determine the cells at each scale.
The estimates use the existing shifted quadratic budget and do not assume a
general conditional signed-measure orthogonality theorem.
-/

noncomputable section

open MeasureTheory RieszShowcase ProbabilityTheory
open scoped ENNReal Classical ProbabilityTheory

namespace Riesz.Negative

abbrev RoundingMasks (n : ℕ) := ℕ → (Fin n × Fin n → Bool)

def multiscaleRoundingLaw {n : ℕ} :
    ℕ → RoundingMasks n → (Fin n → ℝ) → Measure (Fin n → ℝ)
  | 0, _, w => Measure.dirac w
  | k + 1, masks, w =>
      (scheduledRoundingLaw (masks 0) (allPairsSchedule n) w).bind
        (multiscaleRoundingLaw k (fun j => masks (j + 1)))

theorem multiscaleRoundingLaw_measurable_probability {n : ℕ} (k : ℕ) :
    Measurable (fun a : RoundingMasks n × (Fin n → ℝ) =>
      multiscaleRoundingLaw k a.1 a.2) ∧
      ∀ (masks : RoundingMasks n) (w : Fin n → ℝ),
        IsProbabilityMeasure (multiscaleRoundingLaw k masks w) := by
  induction k with
  | zero =>
      exact ⟨Measure.measurable_dirac.comp measurable_snd,
        fun _ w => inferInstanceAs (IsProbabilityMeasure (Measure.dirac w))⟩
  | succ k ih =>
      have hinner (masks : RoundingMasks n) :
          Measurable (multiscaleRoundingLaw k (fun j => masks (j + 1))) :=
        ih.1.comp (measurable_const.prodMk measurable_id)
      let κ : Kernel (RoundingMasks n × (Fin n → ℝ)) (Fin n → ℝ) :=
        (scheduledRoundingKernel (allPairsSchedule n)).comap
          (fun a => (a.1 0, a.2)) (by fun_prop)
      haveI : IsMarkovKernel κ := inferInstance
      constructor
      · refine Measure.measurable_of_measurable_coe _ (fun D hD => ?_)
        have hbind (a : RoundingMasks n × (Fin n → ℝ)) :
            (multiscaleRoundingLaw (k + 1) a.1 a.2) D =
              ∫⁻ v, (multiscaleRoundingLaw k (fun j => a.1 (j + 1)) v) D ∂κ a :=
          Measure.bind_apply hD (hinner a.1).aemeasurable
        have hf : Measurable (fun b : (RoundingMasks n × (Fin n → ℝ)) × (Fin n → ℝ) =>
            (multiscaleRoundingLaw k (fun j => b.1.1 (j + 1)) b.2) D) :=
          (Measure.measurable_coe hD).comp (ih.1.comp
            (show Measurable (fun b : (RoundingMasks n × (Fin n → ℝ)) × (Fin n → ℝ) =>
              ((fun j => b.1.1 (j + 1)), b.2)) from by fun_prop))
        simpa only [hbind] using hf.lintegral_kernel_prod_right' (κ := κ)
      · intro masks w
        haveI : IsProbabilityMeasure (scheduledRoundingLaw (masks 0) (allPairsSchedule n) w) :=
          scheduledRoundingLaw_isProbability _ _ _
        exact isProbabilityMeasure_bind (hinner masks).aemeasurable
          (Filter.Eventually.of_forall (fun v => ih.2 _ v))

def multiscaleRoundingKernel {n : ℕ} (k : ℕ) :
    Kernel (RoundingMasks n × (Fin n → ℝ)) (Fin n → ℝ) where
  toFun a := multiscaleRoundingLaw k a.1 a.2
  measurable' := (multiscaleRoundingLaw_measurable_probability k).1

instance multiscaleRoundingKernel_isMarkov {n : ℕ} (k : ℕ) :
    IsMarkovKernel (multiscaleRoundingKernel (n := n) k) where
  isProbabilityMeasure a := (multiscaleRoundingLaw_measurable_probability k).2 a.1 a.2

def fixedMultiscaleRoundingKernel {n : ℕ} (k : ℕ) (masks : RoundingMasks n) :
    Kernel (Fin n → ℝ) (Fin n → ℝ) :=
  (multiscaleRoundingKernel k).comap (fun w => (masks, w))
    (measurable_const.prodMk measurable_id)

instance fixedMultiscaleRoundingKernel_isMarkov {n : ℕ} (k : ℕ) (masks : RoundingMasks n) :
    IsMarkovKernel (fixedMultiscaleRoundingKernel k masks) := by
  exact inferInstanceAs (IsMarkovKernel ((multiscaleRoundingKernel k).comap
    (fun w => (masks, w)) (measurable_const.prodMk measurable_id)))

def cellRoundingKernel {n : ℕ} (enabled : Fin n × Fin n → Bool) :
    Kernel (Fin n → ℝ) (Fin n → ℝ) :=
  (scheduledRoundingKernel (allPairsSchedule n)).comap (fun w => (enabled, w))
    (measurable_const.prodMk measurable_id)

instance cellRoundingKernel_isMarkov {n : ℕ} (enabled : Fin n × Fin n → Bool) :
    IsMarkovKernel (cellRoundingKernel enabled) := by
  exact inferInstanceAs (IsMarkovKernel ((scheduledRoundingKernel (allPairsSchedule n)).comap
    (fun w => (enabled, w)) (measurable_const.prodMk measurable_id)))

theorem multiscaleRoundingLaw_succ {n : ℕ} (k : ℕ) (masks : RoundingMasks n)
    (w : Fin n → ℝ) :
    multiscaleRoundingLaw (k + 1) masks w =
      (fixedMultiscaleRoundingKernel k (fun j => masks (j + 1)) ∘ₖ
        cellRoundingKernel (masks 0)) w := rfl

theorem integrable_multiscaleRoundingLaw {n : ℕ} (k : ℕ) (masks : RoundingMasks n)
    (w : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    Integrable f (multiscaleRoundingLaw k masks w) := by
  induction k generalizing masks w with
  | zero => exact integrable_dirac (by simp)
  | succ k ih =>
      rw [multiscaleRoundingLaw_succ]
      exact (ProbabilityTheory.integrable_comp_iff hf.aestronglyMeasurable).2
        ⟨Filter.Eventually.of_forall (fun v => ih (fun j => masks (j + 1)) v),
          integrable_scheduledRoundingLaw (masks 0) (allPairsSchedule n) w
            (fun v => ∫ z, ‖f z‖ ∂fixedMultiscaleRoundingKernel k (fun j => masks (j + 1)) v)⟩

theorem integral_multiscaleRoundingLaw_succ {n : ℕ} (k : ℕ) (masks : RoundingMasks n)
    (w : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    (∫ v, f v ∂multiscaleRoundingLaw (k + 1) masks w) =
      ∫ u, (∫ v, f v ∂multiscaleRoundingLaw k (fun j => masks (j + 1)) u)
        ∂scheduledRoundingLaw (masks 0) (allPairsSchedule n) w := by
  exact Kernel.integral_comp (κ := cellRoundingKernel (masks 0))
    (η := fixedMultiscaleRoundingKernel k (fun j => masks (j + 1))) (a := w)
    (integrable_multiscaleRoundingLaw (k + 1) masks w f hf)

theorem multiscaleRoundingLaw_coordinate_mean {n : ℕ} (k : ℕ) (masks : RoundingMasks n)
    (w : Fin n → ℝ) (i : Fin n) :
    (∫ v, v i ∂multiscaleRoundingLaw k masks w) = w i := by
  induction k generalizing masks w with
  | zero => simp [multiscaleRoundingLaw]
  | succ k ih =>
      rw [integral_multiscaleRoundingLaw_succ k masks w _ (measurable_pi_apply i)]
      simpa only [ih] using
        scheduledRoundingLaw_coordinate_mean (masks 0) (allPairsSchedule n) w i

theorem multiscaleRoundingLaw_preserves {n : ℕ} (k : ℕ) (masks : RoundingMasks n)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) :
    ∀ᵐ v ∂multiscaleRoundingLaw k masks w,
      (∀ i, 0 ≤ v i ∧ v i ≤ 1) ∧ (∑ i, v i = ∑ i, w i) ∧
        (∀ i, w i = 0 ∨ w i = 1 → v i = w i) := by
  induction k generalizing masks w with
  | zero => simpa [multiscaleRoundingLaw] using hw
  | succ k ih =>
      rw [multiscaleRoundingLaw_succ]
      refine Kernel.ae_comp_of_ae_ae (by measurability) ?_
      filter_upwards [scheduledRoundingLaw_preserves (masks 0) (allPairsSchedule n) w hw]
        with u hu
      exact (ih (fun j => masks (j + 1)) u hu.1).mono fun v hv =>
        ⟨hv.1, hv.2.1.trans hu.2.1,
          fun i hi => (hv.2.2 i ((hu.2.2 i hi).symm ▸ hi)).trans (hu.2.2 i hi)⟩

theorem multiscaleRoundingLaw_shifted_energy_le {n d : ℕ}
    (k : ℕ) (masks : RoundingMasks n) (q : ℝ) (hq : 0 < q)
    (D cap : ℕ → ℝ) (hD : ∀ j < k, 0 ≤ D j)
    (x : Fin n → Rd d) (hx : Function.Injective x)
    (hdiam : ∀ j < k, ∀ i l, masks j (i, l) = true → ‖x i - x l‖ ≤ D j)
    (hcap : ∀ j < k, ∀ u : Fin n → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ 1) →
      ∀ᵐ v ∂scheduledRoundingLaw (masks j) (allPairsSchedule n) u,
        totalFractionalBudget v ≤ cap (j + 1))
    (w z : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hbudget : totalFractionalBudget w ≤ cap 0) :
    (∫ v, weightQuadratic d n q x (fun i => v i - z i)
      ∂multiscaleRoundingLaw k masks w) ≤
        weightQuadratic d n q x (fun i => w i - z i) +
          ∑ j ∈ Finset.range k, D j ^ q / q * cap j := by
  induction k generalizing masks D cap w with
  | zero => simp [multiscaleRoundingLaw]
  | succ k ih =>
      rw [integral_multiscaleRoundingLaw_succ k masks w _
        (measurable_weightQuadratic_diff d n q x z)]
      have htail : ∀ᵐ u ∂scheduledRoundingLaw (masks 0) (allPairsSchedule n) w,
          (∫ v, weightQuadratic d n q x (fun i => v i - z i)
            ∂multiscaleRoundingLaw k (fun j => masks (j + 1)) u) ≤
              weightQuadratic d n q x (fun i => u i - z i) +
                ∑ j ∈ Finset.range k, D (j + 1) ^ q / q * cap (j + 1) := by
        filter_upwards [scheduledRoundingLaw_preserves (masks 0) (allPairsSchedule n) w hw,
          hcap 0 (Nat.zero_lt_succ k) w hw] with u hu hbu
        exact ih (fun j => masks (j + 1)) (fun j => D (j + 1)) (fun j => cap (j + 1))
          (fun j hj => hD (j + 1) (Nat.succ_lt_succ hj))
          (fun j hj => hdiam (j + 1) (Nat.succ_lt_succ hj))
          (fun j hj u hu => hcap (j + 1) (Nat.succ_lt_succ hj) u hu) u hu.1 hbu
      haveI : IsProbabilityMeasure (scheduledRoundingLaw (masks 0) (allPairsSchedule n) w) :=
        scheduledRoundingLaw_isProbability _ _ _
      have hinter := integral_mono_ae
        (integrable_scheduledRoundingLaw (masks 0) (allPairsSchedule n) w
          (fun u => ∫ v, weightQuadratic d n q x (fun i => v i - z i)
            ∂multiscaleRoundingLaw k (fun j => masks (j + 1)) u))
        ((integrable_scheduledRoundingLaw (masks 0) (allPairsSchedule n) w
          (fun u => weightQuadratic d n q x (fun i => u i - z i))).add
            (integrable_const (∑ j ∈ Finset.range k, D (j + 1) ^ q / q * cap (j + 1)))) htail
      simp only [Pi.add_apply] at hinter
      rw [integral_add (integrable_scheduledRoundingLaw (masks 0) (allPairsSchedule n) w
        (fun u => weightQuadratic d n q x (fun i => u i - z i))) (integrable_const _),
        integral_const, probReal_univ, one_smul] at hinter
      have hfirst := scheduledRoundingLaw_shifted_energy_budget (masks 0) (allPairsSchedule n)
        q (D 0) hq x hx (hdiam 0 (Nat.zero_lt_succ k)) w z hw
      have hpost : 0 ≤ ∫ v, totalFractionalBudget v
          ∂scheduledRoundingLaw (masks 0) (allPairsSchedule n) w :=
        integral_nonneg_of_ae ((scheduledRoundingLaw_preserves (masks 0) (allPairsSchedule n) w hw).mono
          (fun v hv => Finset.sum_nonneg
            (fun i _ => mul_nonneg (hv.1 i).1 (sub_nonneg.mpr (hv.1 i).2))))
      have hcoeff : 0 ≤ D 0 ^ q / q :=
        div_nonneg (Real.rpow_nonneg (hD 0 (Nat.zero_lt_succ k)) q) hq.le
      rw [Finset.sum_range_succ']
      nlinarith [mul_le_mul_of_nonneg_left hbudget hcoeff]

theorem multiscaleRoundingLaw_integral_final {n : ℕ} (k : ℕ) (masks : RoundingMasks n)
    (hroot : ∀ i j, masks k (i, j) = true) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (M : ℕ) (hM : ∑ i, w i = M) :
    ∀ᵐ v ∂multiscaleRoundingLaw (k + 1) masks w, ∀ i, v i = 0 ∨ v i = 1 := by
  induction k generalizing masks w with
  | zero =>
      have hmask : masks 0 = fun _ => true := funext (fun p => hroot p.1 p.2)
      simpa [multiscaleRoundingLaw, Measure.bind_dirac, hmask] using
        scheduledRoundingLaw_integral_final w hw M hM
  | succ k ih =>
      rw [multiscaleRoundingLaw_succ]
      refine Kernel.ae_comp_of_ae_ae (by measurability) ?_
      filter_upwards [scheduledRoundingLaw_preserves (masks 0) (allPairsSchedule n) w hw]
        with u hu
      exact ih (fun j => masks (j + 1)) hroot u hu.1 (hu.2.1.trans hM)

theorem multiscaleRoundingLaw_coordinate_lintegral {n : ℕ} (k : ℕ) (masks : RoundingMasks n)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (i : Fin n) :
    (∫⁻ v, ENNReal.ofReal (v i) ∂multiscaleRoundingLaw k masks w) = ENNReal.ofReal (w i) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_multiscaleRoundingLaw k masks w _ (measurable_pi_apply i))
    ((multiscaleRoundingLaw_preserves k masks w hw).mono (fun v hv => (hv.1 i).1))).symm.trans
      (congrArg ENNReal.ofReal (multiscaleRoundingLaw_coordinate_mean k masks w i))

theorem multiscaleRoundingLaw_weightedAtomic_mean {d n : ℕ}
    (k : ℕ) (masks : RoundingMasks n) (x : Fin n → Rd d) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (D : Set (Rd d)) :
    (∫⁻ v, weightedAtomicMeasure d n x v D ∂multiscaleRoundingLaw k masks w) =
      weightedAtomicMeasure d n x w D := by
  simp_rw [weightedAtomicMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_finsetSum (f := fun (i : Fin n) (v : Fin n → ℝ) =>
    ENNReal.ofReal (v i) * Measure.dirac (x i) D) Finset.univ (fun i _ =>
      (ENNReal.measurable_ofReal.comp (measurable_pi_apply i)).mul measurable_const)]
  exact Finset.sum_congr rfl (fun i _ =>
    (lintegral_mul_const (Measure.dirac (x i) D)
      (ENNReal.measurable_ofReal.comp (measurable_pi_apply i))).trans
      (congrArg (fun a => a * Measure.dirac (x i) D)
        (multiscaleRoundingLaw_coordinate_lintegral k masks w hw i)))

theorem multiscaleRoundingLaw_occupiedSites_spec {n d : ℕ}
    (k : ℕ) (masks : RoundingMasks n) (hroot : ∀ i j, masks k (i, j) = true)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (M : ℕ) (hM : ∑ i, w i = M) (x : Fin n → Rd d) (hx : Function.Injective x) :
    ∀ᵐ v ∂multiscaleRoundingLaw (k + 1) masks w,
      (occupiedSites x v).card = M ∧
        weightedAtomicMeasure d n x v = ∑ y ∈ occupiedSites x v, Measure.dirac y := by
  filter_upwards [multiscaleRoundingLaw_preserves (k + 1) masks w hw,
    multiscaleRoundingLaw_integral_final k masks hroot w hw M hM] with v hv h01
  exact ⟨by simpa [occupiedSites, Finset.card_image_of_injective _ hx] using
    occupied_card_eq_of_integral_weights v h01 M (hv.2.1.trans hM),
    weightedAtomicMeasure_eq_occupiedSites x hx v h01⟩

theorem exists_multiscaleRounding_sampler {n : ℕ} (k : ℕ) :
    ∃ f : (RoundingMasks n × (Fin n → ℝ)) → unitInterval → (Fin n → ℝ),
      Measurable (Function.uncurry f) ∧ ∀ a,
        volume.map (f a) = multiscaleRoundingLaw k a.1 a.2 := by
  exact (multiscaleRoundingKernel (n := n) k).exists_measurable_map_eq_unitInterval

theorem multiscaleRoundingLaw_expected_energy_le {n d : ℕ}
    (k : ℕ) (masks : RoundingMasks n) (q : ℝ) (hq : 0 < q)
    (D cap : ℕ → ℝ) (hD : ∀ j < k, 0 ≤ D j)
    (x : Fin n → Rd d) (hx : Function.Injective x)
    (hdiam : ∀ j < k, ∀ i l, masks j (i, l) = true → ‖x i - x l‖ ≤ D j)
    (hcap : ∀ j < k, ∀ u : Fin n → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ 1) →
      ∀ᵐ v ∂scheduledRoundingLaw (masks j) (allPairsSchedule n) u,
        totalFractionalBudget v ≤ cap (j + 1))
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hbudget : totalFractionalBudget w ≤ cap 0) :
    (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun i => v i - w i))
      ∂multiscaleRoundingLaw k masks w) ≤
        ∑ j ∈ Finset.range k, D j ^ q / q * cap j := by
  simp_rw [weightedSignedMeasure_energy d n q x hx]
  simpa [weightQuadratic] using
    multiscaleRoundingLaw_shifted_energy_le k masks q hq D cap hD x hx hdiam hcap w w hw hbudget

def partitionRoundingMasks {n : ℕ} {ι : Type*} [DecidableEq ι]
    (label : ℕ → Fin n → ι) : RoundingMasks n :=
  fun j p => decide (label j p.1 = label j p.2)

def partitionRoundingCap {n : ℕ} {ι : Type*} [DecidableEq ι]
    (label : ℕ → Fin n → ι) (w : Fin n → ℝ) : ℕ → ℝ
  | 0 => totalFractionalBudget w
  | j + 1 => (Finset.univ.image (label j)).card / (4 : ℝ)

theorem partitionRoundingLaw_expected_energy_le {n d : ℕ} {ι : Type*} [DecidableEq ι]
    (k : ℕ) (label : ℕ → Fin n → ι) (q : ℝ) (hq : 0 < q)
    (D : ℕ → ℝ) (hD : ∀ j < k + 1, 0 ≤ D j)
    (x : Fin n → Rd d) (hx : Function.Injective x)
    (hdiam : ∀ j < k + 1, ∀ i l, label j i = label j l → ‖x i - x l‖ ≤ D j)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) :
    (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun i => v i - w i))
      ∂multiscaleRoundingLaw (k + 1) (partitionRoundingMasks label) w) ≤
        D 0 ^ q / q * totalFractionalBudget w +
          ∑ j ∈ Finset.range k,
            D (j + 1) ^ q / q * ((Finset.univ.image (label j)).card / (4 : ℝ)) := by
  have hcap (j : ℕ) (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) :=
    scheduledRoundingLaw_partition_budget (partitionRoundingMasks label j) (label j) u hu
      (fun i l he _ => by simp [partitionRoundingMasks, he])
  have henergy := multiscaleRoundingLaw_expected_energy_le (k + 1)
    (partitionRoundingMasks label) q hq D (partitionRoundingCap label w) hD x hx
    (fun j hj i l he => hdiam j hj i l (of_decide_eq_true he))
    (fun j _ u hu => hcap j u hu) w hw le_rfl
  simpa only [Finset.sum_range_succ', partitionRoundingCap, add_comm] using henergy

end Riesz.Negative
