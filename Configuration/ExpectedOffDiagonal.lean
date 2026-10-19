import Riesz.Configuration.ExpectedFactorial
import Riesz.Stationary.GridGaussian
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal

/-!
# Expected factorial pairs on simple laws

Coordinate off-diagonal restriction represents unequal labels only after
simplicity is established. This module connects that restriction to the
expected factorial measure and the pair kernel in the exact Showcase.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Configuration

/-- The coordinate off-diagonal part of the product measure. -/
def offDiagonalPairs (d : ℕ) (μ : Measure (Rd d)) : Measure (Rd d × Rd d) :=
  (μ.prod μ).restrict {p | p.1 ≠ p.2}

theorem measurable_offDiagonalPairs_simple (d : ℕ) :
    Measurable (fun μ : SimpleMeasure d => offDiagonalPairs d μ.val) := by
  refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
  let D : Set (Rd d × Rd d) := {p | p.1 ≠ p.2}
  have hD : MeasurableSet D :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  let k : Rd d × Rd d → ℝ≥0∞ := (A ∩ D).indicator (fun _ => 1)
  have hk : Measurable k := measurable_const.indicator (hA.inter hD)
  have heval (μ : SimpleMeasure d) : offDiagonalPairs d μ.val A =
      ∫⁻ x, ∫⁻ y, k (x, y) ∂μ.val ∂μ.val := by
    letI : SFinite μ.val := simple_isSFinite d μ.val μ.property
    exact (Measure.restrict_apply (μ := μ.val.prod μ.val) (s := D) hA).trans
      ((lintegral_indicator_one (μ := μ.val.prod μ.val) (hA.inter hD)).symm.trans
        (lintegral_prod k hk.aemeasurable))
  simpa only [heval] using measurable_simple_pair_lintegral d k hk

theorem aemeasurable_counting_offDiagonalPairs_of_simple (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val) :
    AEMeasurable (fun μ : CountingConfiguration d => offDiagonalPairs d μ.val) P := by
  obtain ⟨F, hF, hleft⟩ :=
    (MeasurableEmbedding.subtype_coe (measurableSet_isSimpleConfiguration d)).exists_measurable_extend
      (measurable_offDiagonalPairs_simple d) (fun _ => ⟨0⟩)
  exact ((hF.comp measurable_subtype_coe).aemeasurable).congr
    (hsimple.mono (fun μ hμ => congr_fun hleft ⟨μ.val, hμ⟩))

/-- On a simple configuration, removing equal labels removes exactly the diagonal. -/
theorem countingFactorialIntegral_eq_integral_offDiagonal_of_simple
    (d : ℕ) (μ : CountingConfiguration d)
    (hμ : IsSimpleConfiguration d μ.val)
    (f : C_c(Rd d × Rd d, ℝ)) :
    countingFactorialIntegral d μ f = ∫ p, f p ∂offDiagonalPairs d μ.val := by
  letI : SFinite μ.val := simple_isSFinite d μ.val hμ
  obtain ⟨R, hR⟩ :=
    ((f.hasCompactSupport.image continuous_fst).union
      (f.hasCompactSupport.image continuous_snd)).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ) ×ˢ
      Metric.closedBall (0 : Rd d) (n : ℝ) := fun p hp =>
    ⟨Metric.mem_closedBall.mpr ((dist_zero_right p.1).trans_le
        ((hR p.1 (Or.inl ⟨p, hp, rfl⟩)).trans hn)),
      Metric.mem_closedBall.mpr ((dist_zero_right p.2).trans_le
        ((hR p.2 (Or.inr ⟨p, hp, rfl⟩)).trans hn))⟩
  obtain ⟨m, x, hx, hrest⟩ := (simple_locallySimple d μ.val hμ) n
  let K := Metric.closedBall (0 : Rd d) (n : ℝ)
  let D : Set (Rd d × Rd d) := {p | p.1 ≠ p.2}
  have hD : MeasurableSet D :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hlocal : (∫ p, f p ∂offDiagonalPairs d μ.val) =
      ∫ p, f p ∂((μ.val.restrict K).prod (μ.val.restrict K)).restrict D := by
    change (∫ p, f p ∂(μ.val.prod μ.val).restrict D) = _
    rw [Measure.prod_restrict, Measure.restrict_comm hD]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (μ.val.prod μ.val).restrict D) (s := K ×ˢ K)
      (fun p hp => image_eq_zero_of_notMem_tsupport
        (fun hs => hp (hf hs)))).symm
  have htuple :
      (∫ p, f p ∂((Riesz.Negative.tupleCounting d m x).prod
        (Riesz.Negative.tupleCounting d m x)).restrict D) =
        ∑ i : Fin m, ∑ j : Fin m, if i = j then 0 else f (x i, x j) := by
    letI := Riesz.Negative.tupleCounting_isFiniteMeasure d m x
    have hfi : Integrable (f : Rd d × Rd d → ℝ)
        ((Riesz.Negative.tupleCounting d m x).prod
          (Riesz.Negative.tupleCounting d m x)) := f.integrable
    rw [← integral_indicator hD, integral_prod _ (hfi.indicator hD)]
    simp_rw [integral_tupleCounting]
    simp only [Set.indicator, D, Set.mem_setOf_eq, ne_eq, hx.eq_iff, ite_not]
  exact (countingFactorialIntegral_eq_sum_of_restrict_eq_tupleCounting
    d n m μ x f hrest hf).trans (htuple.symm.trans
      (hlocal.trans (congrArg (fun ν : Measure (Rd d) =>
        ∫ p, f p ∂(ν.prod ν).restrict D) hrest)).symm)

/-- The mean of the actual coordinate off-diagonal pair measures. -/
def countingOffDiagonalPairMean (d : ℕ) (P : Measure (CountingConfiguration d)) :
    Measure (Rd d × Rd d) := P.bind (fun μ => offDiagonalPairs d μ.val)

theorem countingOffDiagonalPairMean_finiteOnCompacts (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞) :
    IsFiniteMeasureOnCompacts (countingOffDiagonalPairMean d P) := by
  constructor
  intro A hA
  obtain ⟨R, hR⟩ := ((hA.image continuous_fst).union
    (hA.image continuous_snd)).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_ge R
  let K := Metric.closedBall (0 : Rd d) (n : ℝ)
  have hAK : A ⊆ K ×ˢ K := fun p hp =>
    ⟨Metric.mem_closedBall.mpr ((dist_zero_right p.1).trans_le
        ((hR p.1 (Or.inl ⟨p, hp, rfl⟩)).trans hn)),
      Metric.mem_closedBall.mpr ((dist_zero_right p.2).trans_le
        ((hR p.2 (Or.inr ⟨p, hp, rfl⟩)).trans hn))⟩
  refine (Measure.bind_apply_le (m := P) (s := A)
    (fun μ : CountingConfiguration d => offDiagonalPairs d μ.val) hA.measurableSet).trans_lt ?_
  refine (lintegral_mono (fun μ => ?_)).trans_lt (hsecond n)
  exact (Measure.restrict_apply (μ := μ.val.prod μ.val)
    (s := {p | p.1 ≠ p.2}) hA.measurableSet).le.trans
      ((measure_mono (Set.inter_subset_left.trans hAK)).trans
        ((Measure.prod_prod_le K K).trans_eq (pow_two (μ.val K)).symm))

theorem integral_countingOffDiagonalPairMean_of_nonneg (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val)
    (f : C_c(Rd d × Rd d, ℝ)) (hf : ∀ p, 0 ≤ f p) :
    (∫ p, f p ∂countingOffDiagonalPairMean d P) =
      ∫ μ, countingFactorialIntegral d μ f ∂P := by
  letI := countingOffDiagonalPairMean_finiteOnCompacts d P hsecond
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg hf)
    (integral_nonneg (fun μ => countingFactorialIntegral_nonneg d μ f hf))).mp
  rw [ofReal_integral_eq_lintegral_ofReal
      (f.integrable (μ := countingOffDiagonalPairMean d P)) (Filter.Eventually.of_forall hf),
    countingOffDiagonalPairMean,
    Measure.lintegral_bind
      (aemeasurable_counting_offDiagonalPairs_of_simple d P hsimple)
      (show Measurable (fun p : Rd d × Rd d => ENNReal.ofReal (f p)) from
        f.continuous.measurable.ennreal_ofReal).aemeasurable,
    ofReal_integral_eq_lintegral_ofReal
      (integrable_countingFactorialIntegral d P hsecond f)
      (Filter.Eventually.of_forall (fun μ => countingFactorialIntegral_nonneg d μ f hf))]
  exact lintegral_congr_ae (hsimple.mono (fun μ hμ =>
    (ofReal_integral_eq_lintegral_ofReal
      (f.integrable (μ := (μ.val.prod μ.val).restrict {p | p.1 ≠ p.2}))
      (Filter.Eventually.of_forall hf)).symm.trans
        (congrArg ENNReal.ofReal
          (countingFactorialIntegral_eq_integral_offDiagonal_of_simple d μ hμ f).symm)))

/-- For simple laws, the RMK factorial measure is the mean off-diagonal measure. -/
theorem expectedFactorialMeasure_eq_countingOffDiagonalPairMean (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val) :
    expectedFactorialMeasure d P hsecond = countingOffDiagonalPairMean d P := by
  letI := countingOffDiagonalPairMean_finiteOnCompacts d P hsecond
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  simpa only [CompactlySupportedContinuousMap.toReal_apply] using
    (integral_expectedFactorialMeasure d P hsecond f.toReal).trans
      (integral_countingOffDiagonalPairMean_of_nonneg d P hsecond hsimple
        f.toReal CompactlySupportedContinuousMap.toReal_nonneg).symm

theorem lintegral_expectedFactorialMeasure_eq_pair_lintegral (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ p, k p ∂expectedFactorialMeasure d P hsecond) =
      ∫⁻ μ, ∫⁻ x, ∫⁻ y, if x = y then 0 else k (x, y) ∂μ.val ∂μ.val ∂P := by
  rw [expectedFactorialMeasure_eq_countingOffDiagonalPairMean d P hsecond hsimple,
    countingOffDiagonalPairMean,
    Measure.lintegral_bind
      (aemeasurable_counting_offDiagonalPairs_of_simple d P hsimple) hk.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hsimple] with μ hμ
  letI : SFinite μ.val := simple_isSFinite d μ.val hμ
  have hD : MeasurableSet {p : Rd d × Rd d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  rw [offDiagonalPairs, ← lintegral_indicator hD,
    lintegral_prod _ (hk.indicator hD).aemeasurable]
  refine lintegral_congr (fun x => lintegral_congr (fun y => ?_))
  by_cases hxy : x = y
  all_goals simp [Set.indicator, hxy]

/-- The Showcase's exact Gaussian profile is an anchored factorial integral. -/
theorem Q_map_val_eq_expectedFactorialMeasure (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val) (u : ℝ) :
    Q d (P.map Subtype.val) u =
      ∫⁻ p, Riesz.Stationary.anchoredGaussianKernel d u p
        ∂expectedFactorialMeasure d P hsecond := by
  have hP0 : ∀ᵐ μ ∂P.map Subtype.val, IsSimpleConfiguration d μ :=
    (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_isSimpleConfiguration d)).2 hsimple
  simp_rw [Q, Riesz.Stationary.anchored_offSite_pair_lintegral]
  rw [lintegral_map'
    (aemeasurable_pair_lintegral_of_simple d (P.map Subtype.val) hP0 _
      (Riesz.Stationary.measurable_offSiteAnchoredGaussianKernel d u))
    measurable_subtype_coe.aemeasurable]
  simpa only [Riesz.Stationary.offSiteAnchoredGaussianKernel] using
    (lintegral_expectedFactorialMeasure_eq_pair_lintegral d P hsecond hsimple
      (Riesz.Stationary.anchoredGaussianKernel d u)
      (Riesz.Stationary.measurable_anchoredGaussianKernel d u)).symm

end Riesz.Configuration
