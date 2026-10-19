import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Linarith

/-!
# Expectations under weak convergence with bounded second moments

Bounded truncations transfer nonnegative continuous observables through weak
convergence. Their tails are controlled by a common squared-moment bound.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Riesz.Analysis

/-- The expectation lost by truncation is bounded by the second moment divided
by the positive truncation level. -/
theorem nonneg_truncation_expectation_bound
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hF : Continuous F) (hF0 : ∀ x, 0 ≤ F x)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : (∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ) ≤ C)
    (M : ℝ) (hM : 0 < M) :
    |(∫ x, F x ∂μ) - ∫ x, min (F x) M ∂μ| ≤ C.toReal / M := by
  have hsq : Integrable (fun x => F x ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hF.pow 2).measurable.aestronglyMeasurable
      (Eventually.of_forall (fun x => sq_nonneg (F x)))).mp
        (ne_top_of_le_ne_top hC hbound)
  have hFi : Integrable F μ := ((integrable_const (1 : ℝ)).add hsq).mono_nonneg
    hF.measurable.aestronglyMeasurable (Eventually.of_forall hF0)
    (Eventually.of_forall (fun x => by
      change F x ≤ 1 + F x ^ 2
      nlinarith [sq_nonneg (F x - 1)]))
  have hmin : Integrable (fun x => min (F x) M) μ := hFi.inf (integrable_const M)
  have hsqC : (∫ x, F x ^ 2 ∂μ) ≤ C.toReal := (ENNReal.ofReal_le_iff_le_toReal hC).mp
    ((ofReal_integral_eq_lintegral_ofReal hsq
      (Eventually.of_forall (fun x => sq_nonneg (F x)))).trans_le hbound)
  have hpoint (x : X) : F x - min (F x) M ≤ F x ^ 2 / M := by
    by_cases hx : F x ≤ M
    · simpa only [min_eq_left hx, sub_self] using div_nonneg (sq_nonneg (F x)) hM.le
    · rw [min_eq_right (le_of_not_ge hx), le_div_iff₀ hM]
      nlinarith [sq_nonneg (F x - M), mul_nonneg (hF0 x) hM.le]
  rw [← integral_sub hFi hmin,
    abs_of_nonneg (integral_nonneg (fun x => sub_nonneg.mpr (min_le_left (F x) M)))]
  apply (integral_mono (hFi.sub hmin) (hsq.div_const M) hpoint).trans
  simpa only [integral_div] using div_le_div_of_nonneg_right hsqC hM.le

/-- A common finite second-moment bound makes nonnegative continuous
expectations converge with the probability laws. -/
theorem tendsto_integral_of_weak_nonneg_second_moment_bound
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hQ : Tendsto P atTop (𝓝 Q))
    (F : X → ℝ) (hF : Continuous F) (hF0 : ∀ x, 0 ≤ F x)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hpre : ∀ n, (∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂(P n).toMeasure) ≤ C)
    (hlimit : (∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂Q.toMeasure) ≤ C) :
    Tendsto (fun n => ∫ x, F x ∂(P n).toMeasure) atTop (𝓝 (∫ x, F x ∂Q.toMeasure)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_lt (by linarith : 0 < ε / 3) C.toReal
  let G : BoundedContinuousFunction X ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min (F x) δ⁻¹) (hF.min continuous_const) δ⁻¹
    (fun x => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (le_min (hF0 x) (inv_pos.mpr hδ).le)]
        using (min_le_right (F x) δ⁻¹))
  have hG := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction G).tendsto Q |>.comp hQ
  filter_upwards [Metric.tendsto_nhds.mp hG (ε / 3) (by linarith)] with n hn
  have hPn := nonneg_truncation_expectation_bound (P n).toMeasure F hF hF0 C hC
    (hpre n) δ⁻¹ (inv_pos.mpr hδ)
  have hQn := nonneg_truncation_expectation_bound Q.toMeasure F hF hF0 C hC
    hlimit δ⁻¹ (inv_pos.mpr hδ)
  have htri := dist_triangle4 (∫ x, F x ∂(P n).toMeasure)
    (∫ x, min (F x) δ⁻¹ ∂(P n).toMeasure)
    (∫ x, min (F x) δ⁻¹ ∂Q.toMeasure) (∫ x, F x ∂Q.toMeasure)
  simp only [Real.dist_eq, Function.comp_apply, div_inv_eq_mul] at hn htri hPn hQn ⊢
  change |(∫ x, min (F x) δ⁻¹ ∂(P n).toMeasure) -
    ∫ x, min (F x) δ⁻¹ ∂Q.toMeasure| < ε / 3 at hn
  rw [abs_sub_comm (∫ x, min (F x) δ⁻¹ ∂Q.toMeasure)] at htri
  linarith

end Riesz.Analysis
