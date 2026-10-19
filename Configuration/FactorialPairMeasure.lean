import Riesz.Configuration.ShellLabels
import Riesz.Stationary.FactorialEnergy

/-!
Actual unequal-label pairs and the original expected factorial measure.

The shell-label Dirac sum retains distinct labels at coincident sites. Its
additive diagonal identity recovers the raw product measure without subtracting
infinite measures. Finite real compact tests then identify its mean with the
original RMK factorial measure and give the nonnegative Campbell identity.

The identification requires only integer-ball second moments of the input
measure. No probability, stationarity, simplicity or SFinite input-law premise
is used; nonnegative integration uses the measurable bind directly.
-/

noncomputable section
open MeasureTheory RieszShowcase
open scoped ENNReal Topology Classical CompactlySupported
namespace Riesz.Configuration

private theorem countingShellAtom_sFinite (d : ℕ) (i : ℕ × ℕ)
    (μ : CountingConfiguration d) : SFinite (countingShellAtom d i μ) := by
  unfold countingShellAtom
  split_ifs <;> infer_instance

/-- Remove equal labels, retaining every unequal label at coincident sites. -/
def countingUnequalLabelPairs (d : ℕ) (μ : CountingConfiguration d) :
    Measure (Rd d × Rd d) :=
  Measure.sum (fun ij : (ℕ × ℕ) × (ℕ × ℕ) =>
    if ij.1 = ij.2 then 0 else
      (countingShellAtom d ij.1 μ).prod (countingShellAtom d ij.2 μ))

private theorem measurable_countingShellAtom_prod (d : ℕ)
    (i j : ℕ × ℕ) :
    Measurable (fun μ : CountingConfiguration d =>
      (countingShellAtom d i μ).prod (countingShellAtom d j μ)) := by
  have hrepr : (fun μ : CountingConfiguration d =>
      (countingShellAtom d i μ).prod (countingShellAtom d j μ)) =
      (fun μ => if i.2 < countingShellCount d i.1 μ ∧
          j.2 < countingShellCount d j.1 μ then
        Measure.dirac (countingShellPosition d i.1 i.2 μ,
          countingShellPosition d j.1 j.2 μ) else 0) := by
    funext μ
    by_cases hi : i.2 < countingShellCount d i.1 μ <;>
      by_cases hj : j.2 < countingShellCount d j.1 μ <;>
        simp [countingShellAtom, hi, hj, Measure.dirac_prod_dirac]
  rw [hrepr]
  exact Measurable.ite
    ((measurableSet_lt measurable_const (measurable_countingShellCount d i.1)).inter
      (measurableSet_lt measurable_const (measurable_countingShellCount d j.1)))
    (Measure.measurable_dirac.comp
      ((measurable_countingShellPosition d i.1 i.2).prodMk
        (measurable_countingShellPosition d j.1 j.2))) measurable_const

theorem measurable_countingUnequalLabelPairs (d : ℕ) :
    Measurable (countingUnequalLabelPairs d) := by
  refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
  simp only [countingUnequalLabelPairs, Measure.sum_apply _ hA]
  refine Measurable.tsum (fun ij => ?_)
  by_cases hij : ij.1 = ij.2
  · simpa only [if_pos hij, Measure.coe_zero, Pi.zero_apply] using
      (measurable_const : Measurable (fun _ : CountingConfiguration d => (0 : ℝ≥0∞)))
  · simpa only [if_neg hij, Function.comp_def] using
      (Measure.measurable_coe hA).comp (measurable_countingShellAtom_prod d ij.1 ij.2)

private theorem countingUnequalLabelPairs_add_diagonal (d : ℕ)
    (μ : CountingConfiguration d) :
    countingUnequalLabelPairs d μ + μ.val.map (fun x : Rd d => (x,x)) =
      μ.val.prod μ.val := by
  let atom : (ℕ × ℕ) → Measure (Rd d) := fun i => countingShellAtom d i μ
  letI (i : ℕ × ℕ) : SFinite (atom i) := countingShellAtom_sFinite d i μ
  have hprod : μ.val.prod μ.val = Measure.sum
      (fun ij : (ℕ × ℕ) × (ℕ × ℕ) => (atom ij.1).prod (atom ij.2)) := by
    rw [countingConfiguration_eq_sum_activeDirac d μ, Measure.prod_sum]
  ext A hA
  let F : (ℕ × ℕ) → (ℕ × ℕ) → ℝ≥0∞ := fun i j => (atom i).prod (atom j) A
  have hdiag : μ.val.map (fun x : Rd d => (x,x)) A = ∑' i, F i i := by
    rw [countingConfiguration_eq_sum_activeDirac d μ,
      Measure.map_sum (show Measurable (fun x : Rd d => (x, x)) from
        measurable_id.prodMk measurable_id).aemeasurable,
      Measure.sum_apply _ hA]
    refine tsum_congr (fun i => ?_)
    by_cases hi : i.2 < countingShellCount d i.1 μ <;>
      simp [F, atom, countingShellAtom, hi, Measure.dirac_prod_dirac]
  have huneq : countingUnequalLabelPairs d μ A =
      ∑' ij : (ℕ × ℕ) × (ℕ × ℕ), if ij.1 = ij.2 then 0 else F ij.1 ij.2 := by
    rw [countingUnequalLabelPairs, Measure.sum_apply _ hA]
    exact tsum_congr (fun ij => by
      by_cases hij : ij.1 = ij.2 <;> simp [hij, F, atom])
  rw [Measure.add_apply, huneq, hdiag, hprod, Measure.sum_apply _ hA]
  symm
  change (∑' ij : (ℕ × ℕ) × (ℕ × ℕ), F ij.1 ij.2) = _
  rw [ENNReal.tsum_prod']
  calc
    _ = ∑' i, (F i i + ∑' j, if j = i then 0 else F i j) :=
      tsum_congr (fun i =>
        (ENNReal.tsum_eq_add_tsum_ite (f := F i) i).trans
          (congrArg (fun a : ℝ≥0∞ => F i i + a)
            (tsum_congr (fun j => by
              by_cases hji : j = i <;> simp [hji]))))
    _ = (∑' i, F i i) + ∑' i, ∑' j, if j = i then 0 else F i j := ENNReal.tsum_add
    _ = (∑' i, F i i) +
        ∑' ij : (ℕ × ℕ) × (ℕ × ℕ), if ij.1 = ij.2 then 0 else F ij.1 ij.2 := by
      congr 1
      rw [ENNReal.tsum_prod' (f := fun ij : (ℕ × ℕ) × (ℕ × ℕ) =>
        if ij.1 = ij.2 then 0 else F ij.1 ij.2)]
      exact tsum_congr (fun i => tsum_congr (fun j => by
        by_cases hij : i = j <;> simp [hij, eq_comm]))
    _ = _ := add_comm _ _

private theorem countingUnequalLabelPairs_le_prod (d : ℕ)
    (μ : CountingConfiguration d) : countingUnequalLabelPairs d μ ≤ μ.val.prod μ.val := by
  rw [← countingUnequalLabelPairs_add_diagonal d μ]
  exact le_add_of_nonneg_right bot_le

private theorem countingFactorialIntegral_eq_integral_unequalLabelPairs
    (d : ℕ) (μ : CountingConfiguration d) (f : C_c(Rd d × Rd d, ℝ)) :
    countingFactorialIntegral d μ f = ∫ p, f p ∂countingUnequalLabelPairs d μ := by
  have hfprod : Integrable (f : Rd d × Rd d → ℝ) (μ.val.prod μ.val) := f.integrable
  have hfuneq : Integrable (f : Rd d × Rd d → ℝ) (countingUnequalLabelPairs d μ) :=
    hfprod.mono_measure (countingUnequalLabelPairs_le_prod d μ)
  have hdiagle : μ.val.map (fun x : Rd d => (x,x)) ≤ μ.val.prod μ.val := by
    rw [← countingUnequalLabelPairs_add_diagonal d μ]
    exact le_add_of_nonneg_left bot_le
  have hfdiag : Integrable (f : Rd d × Rd d → ℝ)
      (μ.val.map (fun x : Rd d => (x,x))) := hfprod.mono_measure hdiagle
  have hadd : (∫ p, f p ∂μ.val.prod μ.val) =
      (∫ p, f p ∂countingUnequalLabelPairs d μ) +
        (∫ p, f p ∂μ.val.map (fun x : Rd d => (x,x))) := by
    rw [← countingUnequalLabelPairs_add_diagonal d μ]
    exact integral_add_measure hfuneq hfdiag
  have hdiag : (∫ p, f p ∂μ.val.map (fun x : Rd d => (x,x))) =
      ∫ x, f (x,x) ∂μ.val :=
    integral_map_of_stronglyMeasurable (measurable_id.prodMk measurable_id)
      f.continuous.stronglyMeasurable
  unfold countingFactorialIntegral
  rw [hadd, hdiag]
  ring

/-- The actual mean of multiplicity-preserving unequal-label pair measures. -/
def countingUnequalLabelPairMean (d : ℕ) (P : Measure (CountingConfiguration d)) :
    Measure (Rd d × Rd d) := P.bind (countingUnequalLabelPairs d)

private theorem countingUnequalLabelPairMean_finiteOnCompacts (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞) :
    IsFiniteMeasureOnCompacts (countingUnequalLabelPairMean d P) := by
  constructor
  intro A hA
  obtain ⟨R, hR⟩ := ((hA.image continuous_fst).union
    (hA.image continuous_snd)).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_ge R
  let K := Metric.closedBall (0 : Rd d) (n : ℝ)
  have hAK : A ⊆ K ×ˢ K := fun p hp =>
    ⟨Metric.mem_closedBall.mpr ((dist_zero_right p.1).trans_le
        ((hR p.1 (Or.inl ⟨p,hp,rfl⟩)).trans hn)),
      Metric.mem_closedBall.mpr ((dist_zero_right p.2).trans_le
        ((hR p.2 (Or.inr ⟨p,hp,rfl⟩)).trans hn))⟩
  refine (Measure.bind_apply_le (m := P) (countingUnequalLabelPairs d)
    hA.measurableSet).trans_lt ?_
  refine (lintegral_mono (fun μ => ?_)).trans_lt (hsecond n)
  exact (countingUnequalLabelPairs_le_prod d μ A).trans
    ((measure_mono hAK).trans ((Measure.prod_prod_le K K).trans_eq (pow_two (μ.val K)).symm))

private theorem integral_countingUnequalLabelPairMean_of_nonneg
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (f : C_c(Rd d × Rd d, ℝ)) (hf : ∀ p, 0 ≤ f p) :
    (∫ p, f p ∂countingUnequalLabelPairMean d P) =
      ∫ μ, countingFactorialIntegral d μ f ∂P := by
  letI := countingUnequalLabelPairMean_finiteOnCompacts d P hsecond
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg hf)
    (integral_nonneg (fun μ => countingFactorialIntegral_nonneg d μ f hf))).mp
  rw [ofReal_integral_eq_lintegral_ofReal
      (f.integrable (μ := countingUnequalLabelPairMean d P)) (Filter.Eventually.of_forall hf),
    countingUnequalLabelPairMean,
    Measure.lintegral_bind (measurable_countingUnequalLabelPairs d).aemeasurable
      (show Measurable (fun p : Rd d × Rd d => ENNReal.ofReal (f p)) from
        f.continuous.measurable.ennreal_ofReal).aemeasurable,
    ofReal_integral_eq_lintegral_ofReal
      (integrable_countingFactorialIntegral d P hsecond f)
      (Filter.Eventually.of_forall (fun μ => countingFactorialIntegral_nonneg d μ f hf))]
  exact lintegral_congr (fun μ =>
    (ofReal_integral_eq_lintegral_ofReal
      ((f.integrable (μ := μ.val.prod μ.val)).mono_measure
        (countingUnequalLabelPairs_le_prod d μ)) (Filter.Eventually.of_forall hf)).symm.trans
      (congrArg ENNReal.ofReal
        (countingFactorialIntegral_eq_integral_unequalLabelPairs d μ f).symm))

/-- The original RMK factorial measure is the actual mean unequal-label measure. -/
theorem expectedFactorialMeasure_eq_countingUnequalLabelPairMean
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞) :
    expectedFactorialMeasure d P hsecond = countingUnequalLabelPairMean d P := by
  letI := countingUnequalLabelPairMean_finiteOnCompacts d P hsecond
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  simpa only [CompactlySupportedContinuousMap.toReal_apply] using
    (integral_expectedFactorialMeasure d P hsecond f.toReal).trans
      (integral_countingUnequalLabelPairMean_of_nonneg d P hsecond
        f.toReal CompactlySupportedContinuousMap.toReal_nonneg).symm

/-- NN Campbell identity with unequal LABELS, including coincident original sites. -/
theorem lintegral_expectedFactorialMeasure_eq_unequalLabel_tsum
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ p, k p ∂expectedFactorialMeasure d P hsecond) =
      ∫⁻ μ, ∑' ij : (ℕ × ℕ) × (ℕ × ℕ),
        if ij.1.2 < countingShellCount d ij.1.1 μ ∧
            ij.2.2 < countingShellCount d ij.2.1 μ ∧ ij.1 ≠ ij.2 then
          k (countingShellPosition d ij.1.1 ij.1.2 μ,
            countingShellPosition d ij.2.1 ij.2.2 μ) else 0 ∂P := by
  rw [expectedFactorialMeasure_eq_countingUnequalLabelPairMean d P hsecond,
    countingUnequalLabelPairMean,
    Measure.lintegral_bind (measurable_countingUnequalLabelPairs d).aemeasurable hk.aemeasurable]
  refine lintegral_congr (fun μ => ?_)
  rw [countingUnequalLabelPairs, lintegral_sum_measure]
  refine tsum_congr (fun ij => ?_)
  by_cases hij : ij.1 = ij.2 <;>
    by_cases hi : ij.1.2 < countingShellCount d ij.1.1 μ <;>
      by_cases hj : ij.2.2 < countingShellCount d ij.2.1 μ <;>
        simp [countingShellAtom, hij, hi, hj, Measure.dirac_prod_dirac]

end Riesz.Configuration
