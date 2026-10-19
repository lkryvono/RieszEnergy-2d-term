import Riesz.Configuration.Topology
import Riesz.Analysis.WeakExpectations
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Local second moments of weak limits

Continuous compact-test integrals transfer squared moment bounds through weak
convergence. Ball counts themselves need not be continuous.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Asymptotics

/-- Portmanteau applies directly to squared compact-test integrals. -/
theorem countingLaw_test_second_moment_le_liminf (d : ℕ)
    (P : ℕ → ProbabilityMeasure (CountingConfiguration d))
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto P atTop (𝓝 Q)) (f : C_c(Rd d, ℝ)) :
    (∫⁻ μ, ENNReal.ofReal ((∫ x, f x ∂μ.val) ^ 2) ∂Q.toMeasure) ≤
      atTop.liminf (fun n =>
        ∫⁻ μ, ENNReal.ofReal ((∫ x, f x ∂μ.val) ^ 2) ∂(P n).toMeasure) := by
  exact lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    ((continuous_countingIntegral d f).pow 2) (fun μ => sq_nonneg _)
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hQ hG)

/-- A common squared compact-test bound survives weak convergence. -/
theorem countingLaw_test_second_moment_le_of_bound (d : ℕ)
    (P : ℕ → ProbabilityMeasure (CountingConfiguration d))
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto P atTop (𝓝 Q)) (f : C_c(Rd d, ℝ)) (C : ℝ≥0∞)
    (hbound : ∀ n,
      (∫⁻ μ, ENNReal.ofReal ((∫ x, f x ∂μ.val) ^ 2) ∂(P n).toMeasure) ≤ C) :
    (∫⁻ μ, ENNReal.ofReal ((∫ x, f x ∂μ.val) ^ 2) ∂Q.toMeasure) ≤ C := by
  simpa only [Filter.liminf_const] using
    (countingLaw_test_second_moment_le_liminf d P Q hQ f).trans
      (Filter.liminf_le_liminf (Eventually.of_forall hbound))

/-- A nonnegative compact-test square is controlled by a local count square. -/
theorem countingIntegral_sq_ofReal_le_ball (d n : ℕ) (μ : CountingConfiguration d)
    (f : C_c(Rd d, ℝ)) (hf0 : ∀ x, 0 ≤ f x)
    (hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ)) :
    ENNReal.ofReal ((∫ x, f x ∂μ.val) ^ 2) ≤
      ENNReal.ofReal (‖f.toBoundedContinuousFunction‖ ^ 2) *
        (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 := by
  have hbound : |∫ x, f x ∂μ.val| ≤
      ‖f.toBoundedContinuousFunction‖ *
        μ.val.real (Metric.closedBall (0 : Rd d) (n : ℝ)) := by
    simpa using countingIntegral_sub_le d n μ f 0 ‖f.toBoundedContinuousFunction‖ hf
      (by simp) (fun x => by simpa only [CompactlySupportedContinuousMap.zero_apply, sub_zero,
        Real.norm_eq_abs, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply]
        using f.toBoundedContinuousFunction.norm_coe_le_norm x)
  have hle : ENNReal.ofReal (∫ x, f x ∂μ.val) ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        μ.val (Metric.closedBall (0 : Rd d) (n : ℝ)) :=
    (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hbound)).trans
      ((ENNReal.ofReal_mul (norm_nonneg _)).trans_le
        (mul_le_mul_right ENNReal.ofReal_toReal_le _))
  rw [ENNReal.ofReal_pow (integral_nonneg hf0), ENNReal.ofReal_pow (norm_nonneg _)]
  exact (pow_le_pow_left' hle 2).trans_eq (mul_pow _ _ 2)

/-- Uniform local count squares bound a compact test along the sequence and its limit. -/
theorem exists_countingLaw_nonneg_test_second_moment_bound (d : ℕ)
    (P : ℕ → ProbabilityMeasure (CountingConfiguration d))
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto P atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2 ∂(P n).toMeasure) ≤ C)
    (f : C_c(Rd d, ℝ)) (hf0 : ∀ x, 0 ≤ f x) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      (∀ n, (∫⁻ μ, ENNReal.ofReal ((∫ x, f x ∂μ.val) ^ 2) ∂(P n).toMeasure) ≤ C) ∧
      (∫⁻ μ, ENNReal.ofReal ((∫ x, f x ∂μ.val) ^ 2) ∂Q.toMeasure) ≤ C := by
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isBounded.exists_norm_le
  obtain ⟨k, hk⟩ := exists_nat_ge (max 1 R)
  have hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) (k : ℝ) :=
    fun y hy => by simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hR y hy).trans ((le_max_right 1 R).trans hk)
  obtain ⟨C, hC, hmoment⟩ := hball (k : ℝ)
    (lt_of_lt_of_le zero_lt_one ((le_max_left 1 R).trans hk))
  have hbound (n : ℕ) :
      (∫⁻ μ, ENNReal.ofReal ((∫ x, f x ∂μ.val) ^ 2) ∂(P n).toMeasure) ≤
        ENNReal.ofReal (‖f.toBoundedContinuousFunction‖ ^ 2) * C :=
    (lintegral_mono (fun μ => countingIntegral_sq_ofReal_le_ball d k μ f hf0 hf)).trans
      ((lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans_le
        (mul_le_mul_right (hmoment n) _))
  exact ⟨_, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC, hbound,
    countingLaw_test_second_moment_le_of_bound d P Q hQ f _ hbound⟩

/-- Weak limits retain the bounded-set second-moment condition in admissibility. -/
theorem countingLaw_limit_local_second_moments (d : ℕ)
    (P : ℕ → ProbabilityMeasure (CountingConfiguration d))
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto P atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2 ∂(P n).toMeasure) ≤ C) :
    ∀ D : Set (Rd d), MeasurableSet D → Bornology.IsBounded D →
      (∫⁻ μ, (μ.val D) ^ 2 ∂Q.toMeasure) < ∞ := by
  intro D _hD hbounded
  obtain ⟨R, hR⟩ := hbounded.exists_norm_le
  obtain ⟨k, hk⟩ := exists_nat_ge R
  have hDball : D ⊆ Metric.closedBall (0 : Rd d) (k : ℝ) :=
    fun y hy => by simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hR y hy).trans hk
  obtain ⟨C, hC, _, hlimit⟩ := exists_countingLaw_nonneg_test_second_moment_bound
    d P Q hQ hball (countingMassCutoff d k) (countingMassCutoff_spec d k).1
  have hle (μ : CountingConfiguration d) : μ.val D ≤
      ENNReal.ofReal (∫ x, countingMassCutoff d k x ∂μ.val) :=
    (measure_mono hDball).trans
      ((countingMassCutoff d k).integrable.measure_le_integral
        (Eventually.of_forall (countingMassCutoff_spec d k).1)
        (fun x hx => ((countingMassCutoff_spec d k).2 hx).ge))
  exact (lintegral_mono (fun μ => (pow_le_pow_left' (hle μ) 2).trans_eq
    (ENNReal.ofReal_pow (integral_nonneg (countingMassCutoff_spec d k).1) 2).symm)).trans_lt
      (hlimit.trans_lt (lt_top_iff_ne_top.mpr hC))

/-- The same moment condition holds on the original ambient space of measure laws. -/
theorem countingLaw_limit_ambient_local_second_moments (d : ℕ)
    (P : ℕ → ProbabilityMeasure (CountingConfiguration d))
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto P atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2 ∂(P n).toMeasure) ≤ C) :
    ∀ D : Set (Rd d), MeasurableSet D → Bornology.IsBounded D →
      (∫⁻ μ, (μ D) ^ 2 ∂(Q.toMeasure.map (fun μ => μ.val))) < ∞ := by
  intro D hD hbounded
  rw [lintegral_map ((Measure.measurable_coe hD).pow_const 2) measurable_subtype_coe]
  exact countingLaw_limit_local_second_moments d P Q hQ hball D hD hbounded

/-- Uniform local second moments let compact-test expectations pass to the weak
limit. This is the first-moment identity needed to identify limiting intensity. -/
theorem countingLaw_nonneg_test_expectations_tendsto (d : ℕ)
    (P : ℕ → ProbabilityMeasure (CountingConfiguration d))
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto P atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2 ∂(P n).toMeasure) ≤ C)
    (f : C_c(Rd d, ℝ)) (hf0 : ∀ x, 0 ≤ f x) :
    Tendsto (fun n => ∫ μ, (∫ x, f x ∂μ.val) ∂(P n).toMeasure) atTop
      (𝓝 (∫ μ, (∫ x, f x ∂μ.val) ∂Q.toMeasure)) := by
  obtain ⟨C, hC, hpre, hlimit⟩ :=
    exists_countingLaw_nonneg_test_second_moment_bound d P Q hQ hball f hf0
  exact Riesz.Analysis.tendsto_integral_of_weak_nonneg_second_moment_bound P Q hQ
    (fun μ => ∫ x, f x ∂μ.val) (continuous_countingIntegral d f)
    (fun μ => integral_nonneg hf0) C hC hpre hlimit

end Riesz.Asymptotics
