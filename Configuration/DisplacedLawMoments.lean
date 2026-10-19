import Riesz.Configuration.DisplacedLaw

/-!
Local second moments for the actual independently heat-displaced law.

The conditional count-square formula retains repeated original labels. A stationary
count-mixture bound transfers local second moments without requiring input simplicity
or an energy hypothesis. Together with the existing displacement properties, this
gives an admissible law from a stationary unit-intensity counting probability law.
-/

noncomputable section
open MeasureTheory RieszShowcase Riesz.Stationary
open scoped ENNReal Classical
namespace Riesz.Configuration

private theorem ennreal_mul_le_sq_add_sq (a b : ℝ≥0∞) :
    a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with hab | hba
  · exact (mul_le_mul' hab (le_refl b)).trans
      ((pow_two b).symm.le.trans (le_add_of_nonneg_left bot_le))
  · exact (mul_le_mul' (le_refl a) hba).trans
      ((pow_two a).symm.le.trans (le_add_of_nonneg_right bot_le))

private theorem sq_lintegral_le_twice_lintegral_sq
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (f : α → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂ν) ^ 2 ≤ 2 * (∫⁻ z, (f z) ^ 2 ∂ν) := by
  have hinner (z : α) :
      (∫⁻ w, (f z) ^ 2 + (f w) ^ 2 ∂ν) =
        (f z) ^ 2 + (∫⁻ w, (f w) ^ 2 ∂ν) := by
    rw [lintegral_add_left measurable_const, lintegral_const,
      measure_univ, mul_one]
  calc
    _ = ∫⁻ z, ∫⁻ w, f z * f w ∂ν ∂ν := by
      rw [lintegral_lintegral_mul hf.aemeasurable hf.aemeasurable, pow_two]
    _ ≤ ∫⁻ z, ∫⁻ w, (f z) ^ 2 + (f w) ^ 2 ∂ν ∂ν :=
      lintegral_mono (fun z => lintegral_mono
        (fun w => ennreal_mul_le_sq_add_sq (f z) (f w)))
    _ = (∫⁻ z, (f z) ^ 2 ∂ν) + (∫⁻ z, (f z) ^ 2 ∂ν) := by
      simp_rw [hinner]
      rw [lintegral_add_left (hf.pow_const 2), lintegral_const,
        measure_univ, mul_one]
    _ = _ := (two_mul _).symm

private theorem pair_sum_diagonal_le {I : Type*} [Countable I] [DecidableEq I]
    (p : I → ℝ≥0∞) :
    (∑' ij : I × I, if ij.1 = ij.2 then p ij.1 else p ij.1 * p ij.2) ≤
      (∑' i, p i) + (∑' i, p i) ^ 2 := by
  have hdiag :
      (∑' ij : I × I, if ij.1 = ij.2 then p ij.1 else 0) = ∑' i, p i := by
    rw [ENNReal.tsum_prod']
    refine tsum_congr (fun i => ?_)
    simpa only using (tsum_ite_eq' i (fun _ : I => p i))
  have hprod : (∑' ij : I × I, p ij.1 * p ij.2) = (∑' i, p i) ^ 2 := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, pow_two]
  calc
    _ ≤ ∑' ij : I × I,
        ((if ij.1 = ij.2 then p ij.1 else 0) + p ij.1 * p ij.2) :=
      ENNReal.tsum_le_tsum (fun ij => by
        by_cases hij : ij.1 = ij.2
        · simp only [if_pos hij]
          exact le_add_of_nonneg_right bot_le
        · simp only [if_neg hij, zero_add, le_refl])
    _ = _ := by rw [ENNReal.tsum_add, hdiag, hprod]

private theorem displacedAmbient_sFinite (d : ℕ)
    (p : CountingConfiguration d × DisplacementMarks d) :
    SFinite (displacedAmbient d p) := by
  let atoms : (ℕ × ℕ) → Measure (Rd d) := fun i =>
    if i.2 < countingShellCount d i.1 p.1 then
      Measure.dirac (countingShellPosition d i.1 i.2 p.1 + p.2 i) else 0
  have hrepr : displacedAmbient d p = Measure.sum atoms := rfl
  letI (i : ℕ × ℕ) : SFinite (atoms i) := by
    dsimp [atoms]
    split_ifs <;> infer_instance
  rw [hrepr]
  infer_instance

private theorem integral_indicator_count_translated (d : ℕ)
    (μ : CountingConfiguration d) (K : Set (Rd d)) (hK : MeasurableSet K)
    (z : Rd d) :
    (∫⁻ x, K.indicator (fun _ => (1 : ℝ≥0∞)) (x + z) ∂μ.val) =
      (translateCounting d z μ).val K := by
  have hf : Measurable (K.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hK
  calc
    _ = ∫⁻ x, K.indicator (fun _ => (1 : ℝ≥0∞)) (z + x) ∂μ.val :=
      lintegral_congr (fun x => congrArg _ (add_comm x z))
    _ = ∫⁻ y, K.indicator (fun _ => (1 : ℝ≥0∞)) y
        ∂μ.val.map (fun x => z + x) :=
      (lintegral_map hf (measurable_const.add measurable_id)).symm
    _ = _ := by
      rw [translateCounting_val]
      exact lintegral_indicator_fun_one hK

private theorem lintegral_displacedAmbient_count_sq_le
    (d : ℕ) (t : ℝ) (ht : 0 < t) (μ : CountingConfiguration d)
    (K : Set (Rd d)) (hK : MeasurableSet K) :
    (∫⁻ z, (displacedAmbient d (μ,z) K) ^ 2 ∂heatDisplacementMarksLaw d t) ≤
      (∫⁻ z, (translateCounting d z μ).val K ∂heatDisplacementLaw d t) +
        (∫⁻ z, (translateCounting d z μ).val K ∂heatDisplacementLaw d t) ^ 2 := by
  let ν := heatDisplacementLaw d t
  letI : IsProbabilityMeasure ν := heatDisplacementLaw_probability d t ht
  let f : Rd d → ℝ≥0∞ := K.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hK
  let A : (ℕ × ℕ) → Prop := fun i => i.2 < countingShellCount d i.1 μ
  let x : (ℕ × ℕ) → Rd d := fun i => countingShellPosition d i.1 i.2 μ
  let p : (ℕ × ℕ) → ℝ≥0∞ := fun i =>
    if A i then ∫⁻ v, f (x i + v) ∂ν else 0
  let k : Rd d × Rd d → ℝ≥0∞ := fun q => f q.1 * f q.2
  have hk : Measurable k := (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  have hdiag (y : Rd d) : f y * f y = f y := by
    by_cases hy : y ∈ K <;> simp [f, hy]
  have hfactor (i j : ℕ × ℕ) :
      (∫⁻ v, ∫⁻ w, f (x i + v) * f (x j + w) ∂ν ∂ν) =
        (∫⁻ v, f (x i + v) ∂ν) * (∫⁻ w, f (x j + w) ∂ν) :=
    lintegral_lintegral_mul
      (hf.comp (measurable_const.add measurable_id)).aemeasurable
      (hf.comp (measurable_const.add measurable_id)).aemeasurable
  have hpair :
      (∫⁻ z, (displacedAmbient d (μ,z) K) ^ 2 ∂heatDisplacementMarksLaw d t) =
        ∑' ij : (ℕ × ℕ) × (ℕ × ℕ),
          if ij.1 = ij.2 then p ij.1 else p ij.1 * p ij.2 := by
    calc
      _ = ∫⁻ z, ∫⁻ q, k q ∂(displacedAmbient d (μ,z)).prod
          (displacedAmbient d (μ,z)) ∂heatDisplacementMarksLaw d t := by
        refine lintegral_congr (fun z => ?_)
        letI : SFinite (displacedAmbient d (μ,z)) := displacedAmbient_sFinite d (μ,z)
        symm
        calc
          _ = (∫⁻ y, f y ∂displacedAmbient d (μ,z)) *
              (∫⁻ y, f y ∂displacedAmbient d (μ,z)) :=
            lintegral_prod_mul hf.aemeasurable hf.aemeasurable
          _ = _ := by rw [lintegral_indicator_fun_one hK, pow_two]
      _ = ∑' ij : (ℕ × ℕ) × (ℕ × ℕ),
          (if A ij.1 ∧ A ij.2 then (1 : ℝ≥0∞) else 0) *
          (if ij.1 = ij.2 then ∫⁻ v, k (x ij.1 + v, x ij.1 + v) ∂ν
            else ∫⁻ v, ∫⁻ w, k (x ij.1 + v, x ij.2 + w) ∂ν ∂ν) :=
        lintegral_displacedAmbient_prod_marks d t ht μ k hk
      _ = _ := by
        refine tsum_congr ?_
        rintro ⟨i,j⟩
        by_cases hij : i = j
        · subst j
          by_cases hi : A i <;> simp [p, k, hi, hdiag]
        · by_cases hi : A i <;> by_cases hj : A j <;>
            simp [p, k, hi, hj, hij, hfactor]
  have hmass : (∑' i, p i) =
      ∫⁻ z, (translateCounting d z μ).val K ∂ν := by
    calc
      _ = ∫⁻ y, ∫⁻ z, f (y + z) ∂ν ∂μ.val := by
        rw [countingConfiguration_eq_sum_activeDirac d μ, lintegral_sum_measure]
        refine tsum_congr (fun i => ?_)
        by_cases hi : i.2 < countingShellCount d i.1 μ <;>
          simp [p, A, x, countingShellAtom, hi]
      _ = ∫⁻ z, ∫⁻ y, f (y + z) ∂μ.val ∂ν :=
        lintegral_lintegral_swap
          (hf.comp (measurable_fst.add measurable_snd)).aemeasurable
      _ = _ := lintegral_congr (fun z =>
        integral_indicator_count_translated d μ K hK z)
  rw [hpair]
  simpa only [hmass] using pair_sum_diagonal_le p

private theorem measurable_translatedCount (d : ℕ) (K : Set (Rd d))
    (hK : MeasurableSet K) :
    Measurable (fun p : CountingConfiguration d × Rd d =>
      (translateCounting d p.2 p.1).val K) := by
  let f : Rd d → ℝ≥0∞ := K.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hK
  have hrepr : (fun p : CountingConfiguration d × Rd d =>
      (translateCounting d p.2 p.1).val K) =
      (fun p => ∑' ij : ℕ × ℕ,
        if ij.2 < countingShellCount d ij.1 p.1 then
          f (p.2 + countingShellPosition d ij.1 ij.2 p.1) else 0) := by
    funext p
    rw [translateCounting_val, ← lintegral_indicator_fun_one hK,
      lintegral_map
        (show Measurable (K.indicator (fun _ => (1 : ℝ≥0∞))) from hf)
        (show Measurable (fun z : Rd d => p.2 + z) from
          measurable_const.add measurable_id),
      countingConfiguration_eq_sum_activeDirac d p.1, lintegral_sum_measure]
    refine tsum_congr (fun ij => ?_)
    by_cases hi : ij.2 < countingShellCount d ij.1 p.1 <;>
      simp [countingShellAtom, hi, f]
  rw [hrepr]
  exact Measurable.tsum (fun ij => Measurable.ite
    (measurableSet_lt measurable_const
      ((measurable_countingShellCount d ij.1).comp measurable_fst))
    (hf.comp (measurable_snd.add
      ((measurable_countingShellPosition d ij.1 ij.2).comp measurable_fst)))
    measurable_const)

private theorem lintegral_translatedCount_pow_of_stationary
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hstationary : IsStationary d (P.map Subtype.val))
    (K : Set (Rd d)) (hK : MeasurableSet K) (r : ℕ) (z : Rd d) :
    (∫⁻ μ, ((translateCounting d z μ).val K) ^ r ∂P) =
      ∫⁻ μ, (μ.val K) ^ r ∂P := by
  have htest : Measurable (fun μ : CountingConfiguration d => (μ.val K) ^ r) :=
    ((Measure.measurable_coe hK).comp measurable_subtype_coe).pow_const r
  exact (lintegral_map htest (measurable_translateCounting d z)).symm.trans
    (congrArg (fun Q : Measure (CountingConfiguration d) =>
        ∫⁻ μ, (μ.val K) ^ r ∂Q)
      (map_translateCounting_eq_of_isStationary d P hstationary z))

theorem lintegral_displacedLaw_count_sq_le
    (d : ℕ) (t : ℝ) (ht : 0 < t) (P : Measure (CountingConfiguration d))
    [IsProbabilityMeasure P]
    (hstationary : IsStationary d (P.map Subtype.val))
    (K : Set (Rd d)) (hK : MeasurableSet K) :
    (∫⁻ η, (η K) ^ 2 ∂displacedLaw d t P) ≤
      (∫⁻ μ, μ.val K ∂P) + 2 * (∫⁻ μ, (μ.val K) ^ 2 ∂P) := by
  let ν := heatDisplacementLaw d t
  letI : IsProbabilityMeasure ν := heatDisplacementLaw_probability d t ht
  letI := heatDisplacementMarksLaw_probability d t ht
  let c : CountingConfiguration d × Rd d → ℝ≥0∞ := fun p =>
    (translateCounting d p.2 p.1).val K
  have hc : Measurable c := measurable_translatedCount d K hK
  let m : CountingConfiguration d → ℝ≥0∞ := fun μ => ∫⁻ z, c (μ,z) ∂ν
  have hm : Measurable m := hc.lintegral_prod_right'
  have hfirst : (∫⁻ μ, m μ ∂P) = ∫⁻ μ, μ.val K ∂P := by
    calc
      _ = ∫⁻ z, ∫⁻ μ, c (μ,z) ∂P ∂ν :=
        lintegral_lintegral_swap hc.aemeasurable
      _ = ∫⁻ _z, ∫⁻ μ, μ.val K ∂P ∂ν := by
        refine lintegral_congr (fun z => ?_)
        simpa only [pow_one] using
          lintegral_translatedCount_pow_of_stationary d P hstationary K hK 1 z
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  have hsecond : (∫⁻ μ, (m μ) ^ 2 ∂P) ≤ 2 * (∫⁻ μ, (μ.val K) ^ 2 ∂P) := by
    calc
      _ ≤ ∫⁻ μ, 2 * (∫⁻ z, (c (μ,z)) ^ 2 ∂ν) ∂P :=
        lintegral_mono (fun μ => sq_lintegral_le_twice_lintegral_sq ν
          (fun z => c (μ,z))
          (show Measurable (fun z => c (μ,z)) from hc.comp measurable_prodMk_left))
      _ = 2 * (∫⁻ μ, ∫⁻ z, (c (μ,z)) ^ 2 ∂ν ∂P) :=
        lintegral_const_mul 2 (hc.pow_const 2).lintegral_prod_right'
      _ = 2 * (∫⁻ z, ∫⁻ μ, (c (μ,z)) ^ 2 ∂P ∂ν) :=
        congrArg (fun a : ℝ≥0∞ => 2 * a)
          (lintegral_lintegral_swap (hc.pow_const 2).aemeasurable)
      _ = _ := by
        congr 1
        calc
          _ = ∫⁻ _z, ∫⁻ μ, (μ.val K) ^ 2 ∂P ∂ν :=
            lintegral_congr (fun z =>
              lintegral_translatedCount_pow_of_stationary d P hstationary K hK 2 z)
          _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  calc
    _ = ∫⁻ μ, ∫⁻ z, (displacedAmbient d (μ,z) K) ^ 2
        ∂heatDisplacementMarksLaw d t ∂P := by
      rw [displacedLaw, lintegral_map
        ((Measure.measurable_coe hK).pow_const 2) (measurable_displacedAmbient d)]
      exact lintegral_prod _ (show AEMeasurable
          (fun q : CountingConfiguration d × DisplacementMarks d =>
            (displacedAmbient d q K) ^ 2)
          (P.prod (heatDisplacementMarksLaw d t)) from
        (((Measure.measurable_coe hK).comp
          (measurable_displacedAmbient d)).pow_const 2).aemeasurable)
    _ ≤ ∫⁻ μ, m μ + (m μ) ^ 2 ∂P :=
      lintegral_mono (fun μ => lintegral_displacedAmbient_count_sq_le d t ht μ K hK)
    _ = (∫⁻ μ, m μ ∂P) + (∫⁻ μ, (m μ) ^ 2 ∂P) := lintegral_add_left hm _
    _ ≤ _ := add_le_add (le_of_eq hfirst) hsecond

theorem displacedLaw_localSecondMoments
    (d : ℕ) (t : ℝ) (ht : 0 < t) (P : Measure (CountingConfiguration d))
    [IsProbabilityMeasure P]
    (hstationary : IsStationary d (P.map Subtype.val))
    (hsecond : ∀ K : Set (Rd d), MeasurableSet K → Bornology.IsBounded K →
      (∫⁻ μ, (μ.val K) ^ 2 ∂P) < ∞) :
    ∀ K : Set (Rd d), MeasurableSet K → Bornology.IsBounded K →
      (∫⁻ η, (η K) ^ 2 ∂displacedLaw d t P) < ∞ := by
  intro K hK hbounded
  have hfirst : (∫⁻ μ, μ.val K ∂P) < ∞ := by
    calc
      _ ≤ ∫⁻ μ, 1 + (μ.val K) ^ 2 ∂P := lintegral_mono (fun μ => by
        by_cases h : μ.val K ≤ 1
        · exact h.trans (le_add_of_nonneg_right bot_le)
        · exact (le_self_pow₀ (le_of_not_ge h) (by decide : (2 : ℕ) ≠ 0)).trans
            (le_add_of_nonneg_left bot_le))
      _ < ∞ := by
        rw [lintegral_add_left measurable_const, lintegral_const]
        simpa only [measure_univ, mul_one] using
          ENNReal.add_lt_top.mpr ⟨by simp, hsecond K hK hbounded⟩
  exact (lintegral_displacedLaw_count_sq_le d t ht P hstationary K hK).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hfirst,
      ENNReal.mul_lt_top (by simp) (hsecond K hK hbounded)⟩)

theorem displacedLaw_admissible
    (d : ℕ) (hd : 0 < d) (t : ℝ) (ht : 0 < t)
    (P : Measure (CountingConfiguration d)) [IsProbabilityMeasure P]
    (hstationary : IsStationary d (P.map Subtype.val))
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d)))
    (hsecond : ∀ K : Set (Rd d), MeasurableSet K → Bornology.IsBounded K →
      (∫⁻ μ, (μ.val K) ^ 2 ∂P) < ∞) : Admissible d (displacedLaw d t P) := by
  refine ⟨displacedLaw_probability d t ht P,
    displacedLaw_ae_simple d hd t ht P hmean,
    displacedLaw_isStationary d t ht P hstationary, ?_,
    displacedLaw_localSecondMoments d t ht P hstationary hsecond⟩
  intro K hK _hbounded
  rw [← Measure.join_apply hK, displacedLaw_join_eq_volume d t ht P hmean]

end Riesz.Configuration
