import Riesz.Geometry.NormalCoordinates
import Riesz.Asymptotics.SphericalLocalBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Small spherical caps and the limiting local mean

The cap integral and its normalization are reused from the certified Problem 1
proofs. This supplies the unit-ball normalization for the local lower limit
without first identifying the normal-coordinate surface Jacobian.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase
open scoped Topology

namespace Riesz.Geometry

/-- The model integral used on both sides of the small-cap squeeze. -/
theorem cap_model_integral (d : ℕ) (hd : 2 ≤ d) (r : ℝ) (hr : 0 < r) :
    (∫ t in Set.Icc (1 - r ^ 2 / 2) 1,
      Real.rpow (2 - 2 * t) (Problem1.coordinateExponent d) ∂volume) = r ^ d / (d : ℝ) := by
  have ha := (Problem1.coordinate_parameters d 0 hd).1
  have hab : 1 - r ^ 2 / 2 ≤ 1 := by nlinarith [sq_nonneg r]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_mul
      (fun t : ℝ => Real.rpow t (Problem1.coordinateExponent d))
      (by norm_num : (2 : ℝ) ≠ 0) 2]
  simp only [mul_one, sub_self, show (2 : ℝ) - 2 * (1 - r ^ 2 / 2) = r ^ 2 by ring,
    Real.rpow_eq_pow,
    integral_rpow (Or.inl (by linarith : -1 < Problem1.coordinateExponent d)),
    Real.zero_rpow (by linarith : Problem1.coordinateExponent d + 1 ≠ 0),
    sub_zero, smul_eq_mul]
  rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, Nat.cast_ofNat,
    show (2 : ℝ) * (Problem1.coordinateExponent d + 1) = (d : ℝ) by
      dsimp [Problem1.coordinateExponent]; ring,
    Real.rpow_natCast]
  rw [show Problem1.coordinateExponent d + 1 = (d : ℝ) / 2 by
    dsimp [Problem1.coordinateExponent]; ring, div_div_eq_mul_div]
  ring

theorem cap_integrand_base_lower (r t : ℝ)
    (ht : 1 - r ^ 2 / 2 ≤ t) (ht1 : t ≤ 1) :
    (2 - 2 * t) * (1 - r ^ 2 / 4) ≤ 1 - t ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht)]

theorem cap_integrand_lower (a r t : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ht : 1 - r ^ 2 / 2 ≤ t) (ht1 : t ≤ 1) :
    (2 - 2 * t) ^ a * (1 - r ^ 2 / 4) ^ a ≤ (1 - t ^ 2) ^ a := by
  have hb : 0 ≤ 1 - r ^ 2 / 4 := by
    nlinarith [(sq_le_sq₀ hr zero_le_one).mpr hr1]
  rw [← Real.mul_rpow (by linarith : 0 ≤ 2 - 2 * t) hb]
  exact Real.rpow_le_rpow (mul_nonneg (by linarith) hb)
    (cap_integrand_base_lower r t ht ht1) ha

/-- The lower half of the sharp scalar small-cap squeeze. -/
theorem cap_scalar_lower (d : ℕ) (hd : 2 ≤ d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    r ^ d / (d : ℝ) * (1 - r ^ 2 / 4) ^ Problem1.coordinateExponent d ≤
      ∫ t in Set.Icc (1 - r ^ 2 / 2) 1,
        Real.rpow (1 - t ^ 2) (Problem1.coordinateExponent d) ∂volume := by
  have ha := (Problem1.coordinate_parameters d 0 hd).1
  have hf : Continuous (fun t : ℝ => (2 - 2 * t) ^ Problem1.coordinateExponent d) :=
    (Real.continuous_rpow_const ha).comp
      (continuous_const.sub (continuous_const.mul continuous_id))
  have hint := setIntegral_mono_on
    (hf.mul_const ((1 - r ^ 2 / 4) ^ Problem1.coordinateExponent d)).integrableOn_Icc
    (Problem1.cap_scalar_bound d hd r hr (by linarith)).1 measurableSet_Icc
    (fun t ht => cap_integrand_lower (Problem1.coordinateExponent d) r t ha hr.le hr1 ht.1 ht.2)
  simpa only [integral_mul_const, ← Real.rpow_eq_pow, cap_model_integral d hd r hr] using hint

/-- Two-sided estimates with the exact leading small-cap coefficient. -/
theorem spherical_cap_ratio_bounds (d : ℕ) (hd : 2 ≤ d) (x : Sphere d)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    Problem1.capConstant d * (1 - r ^ 2 / 4) ^ Problem1.coordinateExponent d ≤
        (sphericalMeasure d {y | chord d x y ≤ r}).toReal / r ^ d ∧
      (sphericalMeasure d {y | chord d x y ≤ r}).toReal / r ^ d ≤ Problem1.capConstant d := by
  rw [sphericalMeasure_chordCap_eq,
    Problem1.cap_integral d hd (problem1SphereEquiv d x) r hr (by linarith)]
  have hl := mul_le_mul_of_nonneg_left (cap_scalar_lower d hd r hr hr1)
    (Problem1.coordinate_normalizer_gamma d hd).2.1.le
  have hu := mul_le_mul_of_nonneg_left (Problem1.cap_scalar_bound d hd r hr (by linarith)).2
    (Problem1.coordinate_normalizer_gamma d hd).2.1.le
  constructor
  · apply (le_div_iff₀ (pow_pos hr d)).mpr
    simpa only [Problem1.capConstant, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hl
  · apply (div_le_iff₀ (pow_pos hr d)).mpr
    simpa only [Problem1.capConstant, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hu

theorem omega_capConstant_eq_unitBall_volume (d : ℕ) (hd : 2 ≤ d) :
    omega d * Problem1.capConstant d =
      (volume : Measure (Rd d)).real (Metric.closedBall (0 : Rd d) 1) := by
  have hD : 0 < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  rw [Measure.real, EuclideanSpace.volume_closedBall]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (Real.Gamma_pos_of_pos (by linarith : 0 < (d : ℝ) / 2 + 1)).le)]
  rw [← Real.rpow_natCast (Real.sqrt Real.pi) d,
    ← Real.rpow_div_two_eq_sqrt (d : ℝ) Real.pi_nonneg,
    Real.Gamma_add_one (by positivity : (d : ℝ) / 2 ≠ 0)]
  have hc := (eq_div_iff (sphericalArea_pos d).ne').mp
    (problem1GaussianAverageConstant_eq d hd)
  rw [← hc, Problem1.gaussianAverageConstant, Problem1.capConstant]
  field_simp [hD.ne', (Real.Gamma_pos_of_pos (by positivity : 0 < (d : ℝ) / 2)).ne']

theorem tendsto_scaled_normalUnitCapRadius :
    Tendsto (fun R : ℝ => R * (2 * Real.sin (1 / (2 * R)))) atTop (𝓝 1) := by
  have harg : Tendsto (fun R : ℝ => 1 / (2 * R)) atTop (𝓝 0) := by
    simpa only [one_div, mul_inv_rev, mul_zero, zero_mul, mul_comm] using
      tendsto_inv_atTop_zero.const_mul (2 : ℝ)⁻¹
  have hsinc : Tendsto (fun R : ℝ => Real.sinc (1 / (2 * R))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sinc_zero] using
      (Real.continuous_sinc.tendsto 0).comp harg
  apply hsinc.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [Real.sinc_of_ne_zero (by positivity : 1 / (2 * R) ≠ 0)]
  simp only [div_div_eq_mul_div, div_one, mul_comm, mul_assoc]

theorem tendsto_spherical_cap_ratio (d : ℕ) (hd : 2 ≤ d)
    {α : Type*} {l : Filter α} (x : α → Sphere d) (r : α → ℝ)
    (hr : Tendsto r l (𝓝 0)) (hpos : ∀ᶠ i in l, 0 < r i) :
    Tendsto (fun i => (sphericalMeasure d {y | chord d (x i) y ≤ r i}).toReal / r i ^ d)
      l (𝓝 (Problem1.capConstant d)) := by
  have hbase : Tendsto (fun i => 1 - r i ^ 2 / 4) l (𝓝 1) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] using
      (tendsto_const_nhds.sub ((hr.pow 2).div_const 4))
  have hlower : Tendsto
      (fun i => Problem1.capConstant d * (1 - r i ^ 2 / 4) ^ Problem1.coordinateExponent d)
      l (𝓝 (Problem1.capConstant d)) := by
    simpa only [Real.one_rpow, mul_one] using
      (hbase.rpow_const (Or.inl one_ne_zero)).const_mul (Problem1.capConstant d)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [hpos, hr.eventually (gt_mem_nhds zero_lt_one)] with i hi hi1
    exact (spherical_cap_ratio_bounds d hd (x i) (r i) hi hi1.le).1
  · filter_upwards [hpos, hr.eventually (gt_mem_nhds zero_lt_one)] with i hi hi1
    exact (spherical_cap_ratio_bounds d hd (x i) (r i) hi hi1.le).2

theorem tendsto_enlargedSphere_unitCap_mean (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (fun N : ℕ => (N : ℝ) *
      (sphericalMeasure d {y : Sphere d | chord d (normalPoint d (sphericalRadius d N) 0) y ≤
        2 * Real.sin (1 / (2 * sphericalRadius d N))}).toReal)
      atTop (𝓝 ((volume : Measure (Rd d)).real (Metric.closedBall (0 : Rd d) 1))) := by
  rw [← omega_capConstant_eq_unitBall_volume d hd]
  have hR := sphericalRadius_tendsto_atTop d (show 0 < d by omega)
  have harg : Tendsto (fun N => 1 / (2 * sphericalRadius d N)) atTop (𝓝 0) := by
    simpa only [one_div, mul_inv_rev, mul_zero, zero_mul, mul_comm, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hR).const_mul (2 : ℝ)⁻¹
  have hr : Tendsto (fun N => 2 * Real.sin (1 / (2 * sphericalRadius d N))) atTop (𝓝 0) := by
    simpa only [Real.sin_zero, mul_zero, Function.comp_apply] using
      (Real.continuous_sin.tendsto 0 |>.comp harg).const_mul 2
  have hpos : ∀ᶠ N in atTop, 0 < 2 * Real.sin (1 / (2 * sphericalRadius d N)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      hR.eventually (eventually_gt_atTop (2 / Real.pi))] with N hN hRN
    exact (normalCapRadius_bounds (sphericalRadius_pos d N hN) zero_lt_one
      (by nlinarith [Real.pi_pos, (div_lt_iff₀ Real.pi_pos).mp hRN])).1
  have hratio := tendsto_spherical_cap_ratio d hd
    (fun N => normalPoint d (sphericalRadius d N) 0)
    (fun N => 2 * Real.sin (1 / (2 * sphericalRadius d N))) hr hpos
  have hscaled := (tendsto_scaled_normalUnitCapRadius.comp hR).pow d
  have hprod : Tendsto (fun N => omega d *
      (sphericalRadius d N * (2 * Real.sin (1 / (2 * sphericalRadius d N)))) ^ d *
      ((sphericalMeasure d {y : Sphere d | chord d (normalPoint d (sphericalRadius d N) 0) y ≤
        2 * Real.sin (1 / (2 * sphericalRadius d N))}).toReal /
        (2 * Real.sin (1 / (2 * sphericalRadius d N))) ^ d))
      atTop (𝓝 (omega d * Problem1.capConstant d)) := by
    simpa only [Function.comp_apply, one_pow, one_mul, mul_assoc] using
      (hscaled.mul hratio).const_mul (omega d)
  apply hprod.congr'
  filter_upwards [hpos] with N hN
  rw [mul_pow, sphericalRadius_pow_dimension d N (by omega)]
  field_simp [(sphericalArea_pos d).ne', hN.ne']

/-- Rotationally averaged counts in the pulled-back unit ball have the
Euclidean unit-ball volume as their limit. -/
theorem tendsto_enlargedSphere_normalUnitBall_mean (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (fun N : ℕ => (N : ℝ) *
      (sphericalMeasure d {y : Sphere d | y ∈ northHemisphere d ∧
        normalInverse d (sphericalRadius d N) y.val ∈
          Metric.closedBall (0 : Rd d) 1}).toReal)
      atTop (𝓝 ((volume : Measure (Rd d)).real (Metric.closedBall (0 : Rd d) 1))) := by
  have hd0 : 0 < d := by omega
  apply (tendsto_enlargedSphere_unitCap_mean d hd).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (sphericalRadius_tendsto_atTop d hd0).eventually (eventually_gt_atTop (2 / Real.pi))]
    with N hN hR
  rw [normalInverse_closedBall_preimage d (sphericalRadius_pos d N hN) zero_le_one
    (by nlinarith [Real.pi_pos,
      (div_lt_iff₀ Real.pi_pos).mp hR])]

end Riesz.Geometry
