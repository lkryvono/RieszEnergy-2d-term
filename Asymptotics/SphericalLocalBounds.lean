import Riesz.Geometry.NormalCoordinates

/-!
# Coarse spherical local first-moment bounds

These bounds transport the certified Problem 1 cap estimate to the exact
sphere and normal coordinates used in the Showcase. They do not use a sharp
cap asymptotic or an identification of chart area.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped Classical ENNReal

namespace Riesz.Geometry

/-- Transport a chord cap to the certified Problem 1 sphere. -/
theorem sphericalMeasure_chordCap_eq (d : ℕ) (x : Sphere d) (r : ℝ) :
    sphericalMeasure d {y : Sphere d | chord d x y ≤ r} =
      Problem1.sigma d {y : Problem1.Sphere d |
        dist (problem1SphereEquiv d x) y ≤ r} := by
  rw [sphericalMeasure, Measure.map_apply
    (problem1SphereIsometryEquiv d).symm.continuous.measurable
    (show MeasurableSet {y : Sphere d | chord d x y ≤ r} from
      (isClosed_le (continuous_const.sub continuous_subtype_val).norm
        continuous_const).measurableSet)]
  change Problem1.sigma d {y : Problem1.Sphere d |
    chord d x ((problem1SphereEquiv d).symm y) ≤ r} = _
  simp only [← problem1SphereEquiv_dist, Equiv.apply_symm_apply]

/-- The certified coarse cap estimate for the exact Showcase sphere. -/
theorem sphericalMeasure_chordCap_le (d : ℕ) (hd : 2 ≤ d)
    (x : Sphere d) (r : ℝ) (hr : 0 < r) (hr2 : r ≤ 2) :
    sphericalMeasure d {y : Sphere d | chord d x y ≤ r} ≤
      ENNReal.ofReal (Problem1.capConstant d * r ^ d) := by
  rw [sphericalMeasure_chordCap_eq]
  exact Problem1.spherical_cap_estimate d hd (problem1SphereEquiv d x) r hr hr2

/-- A fixed normal-coordinate ball has a uniform Haar-averaged count bound
at the enlargement scale `sphericalRadius d N`. -/
theorem sphericalMeasure_normalBall_mul_le (d N : ℕ) (hd : 2 ≤ d)
    (hN : 0 < N) (T : ℝ) (hT : 0 < T)
    (hTpi : T < Real.pi * sphericalRadius d N / 2) :
    (N : ℝ≥0∞) * sphericalMeasure d
      {y : Sphere d | y ∈ northHemisphere d ∧
        normalInverse d (sphericalRadius d N) y.val ∈
          Metric.closedBall (0 : Rd d) T} ≤
      ENNReal.ofReal (omega d * Problem1.capConstant d * T ^ d) := by
  rw [normalInverse_closedBall_preimage d
    (sphericalRadius_pos d N hN) hT.le hTpi]
  refine (mul_le_mul_right
    (sphericalMeasure_chordCap_le d hd (normalPoint d (sphericalRadius d N) 0) _
      (normalCapRadius_bounds (sphericalRadius_pos d N hN) hT hTpi).1
      (normalCapRadius_bounds (sphericalRadius_pos d N hN) hT hTpi).2.1)
    (N : ℝ≥0∞)).trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀
        (normalCapRadius_bounds (sphericalRadius_pos d N hN) hT hTpi).1.le
        (normalCapRadius_bounds (sphericalRadius_pos d N hN) hT hTpi).2.2 d)
      (Problem1.cap_constant_positive d hd).le)
    (Nat.cast_nonneg N)).trans_eq ?_)
  rw [div_pow, sphericalRadius_pow_dimension d N (by omega)]
  field_simp [(Nat.cast_pos.mpr hN).ne', (sphericalArea_pos d).ne']

end Riesz.Geometry
