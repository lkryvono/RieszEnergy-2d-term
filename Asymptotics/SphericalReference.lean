import Riesz.Geometry.SphereFromProblem1
import Riesz.Stationary.GridEnergyPositive

/-! Convergence of the scalar reference term in the spherical remainder formula. -/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Geometry
open scoped Topology

namespace Riesz.Asymptotics

theorem measurable_sphericalGaussianBackground (d N : ℕ) (hd : 2 ≤ d) :
    Measurable (sphericalGaussianBackground d N) := by
  exact measurable_const.mul ((Problem1.part5_J_continuous d hd).2.1.comp
    (measurable_id.mul_const ((sphericalRadius d N) ^ 2)))

theorem sphericalGaussianBackground_nonneg (d N : ℕ) (u : ℝ) :
    0 ≤ sphericalGaussianBackground d N u := by
  exact mul_nonneg (Nat.cast_nonneg N) (integral_nonneg (fun _ => Real.exp_nonneg _))

def weightedSphericalPositiveReference (d N : ℕ) (s u : ℝ) : ℝ :=
  u ^ (s / 2 - 1) * min 1 (sphericalGaussianBackground d N u)

def weightedSphericalNegativeReference (d N : ℕ) (s u : ℝ) : ℝ :=
  u ^ (s / 2 - 1) * max (1 - sphericalGaussianBackground d N u) 0

def sphericalReferenceConstant (d N : ℕ) (s : ℝ) : ℝ :=
  if 0 < s then
    -gamma_s s * ∫ u in Set.Ioi (0 : ℝ), weightedSphericalPositiveReference d N s u
  else gamma_s s * ∫ u in Set.Ioi (0 : ℝ), weightedSphericalNegativeReference d N s u

theorem gaussianAverage_antitone (d : ℕ) (hd : 2 ≤ d) :
    Antitone (Problem1.gaussianAverage d) := by
  exact fun u v huv => integral_mono
    (Problem1.gaussian_center d hd v (Problem1.northPole d)).1
    (Problem1.gaussian_center d hd u (Problem1.northPole d)).1
    (fun y => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg huv) (sq_nonneg _)))

theorem sphericalGaussianBackground_antitone (d N : ℕ) (hd : 2 ≤ d) :
    Antitone (sphericalGaussianBackground d N) := by
  exact fun u v huv => mul_le_mul_of_nonneg_left
    (gaussianAverage_antitone d hd (mul_le_mul_of_nonneg_right huv (sq_nonneg _)))
    (Nat.cast_nonneg N)

theorem one_lt_B_half_pi (d : ℕ) (hd : 2 ≤ d) : 1 < B d (Real.pi / 2) := by
  rw [B, show Real.pi / (Real.pi / 2) = (2 : ℝ) by field_simp]
  exact Real.one_lt_rpow (by norm_num)
    (div_pos (Nat.cast_pos.mpr (by omega : 0 < d)) (by norm_num))

theorem tendsto_integral_weightedSphericalPositiveReference (d : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) :
    Tendsto (fun N : ℕ => ∫ u in Set.Ioi (0 : ℝ), weightedSphericalPositiveReference d N s u)
      atTop (nhds (∫ u in Set.Ioi (0 : ℝ), Riesz.Stationary.weightedPositiveReference d s u)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (Riesz.Stationary.weightedPositiveReference d s) ?_ ?_
    (Riesz.Stationary.weightedPositiveReference_integrable d s hs hsd) ?_
  · exact Eventually.of_forall (fun N =>
      ((measurable_id.pow_const _).mul
        (measurable_const.min (measurable_sphericalGaussianBackground d N hd))).aestronglyMeasurable)
  case refine_3 =>
    exact ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu =>
      (tendsto_const_nhds.min (tendsto_sphericalGaussianBackground d hd u hu)).const_mul
        (u ^ (s / 2 - 1)))
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa only [weightedSphericalPositiveReference, Riesz.Stationary.weightedPositiveReference,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.le _)
      (le_min zero_le_one (sphericalGaussianBackground_nonneg d N u)))] using
    mul_le_mul_of_nonneg_left (min_le_min_left 1 (sphericalGaussianBackground_le d N hd hN u hu))
      (Real.rpow_nonneg hu.le (s / 2 - 1))

theorem tendsto_integral_weightedSphericalNegativeReference (d : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : s < 0) :
    Tendsto (fun N : ℕ => ∫ u in Set.Ioi (0 : ℝ), weightedSphericalNegativeReference d N s u)
      atTop (nhds (∫ u in Set.Ioi (0 : ℝ), Riesz.Stationary.weightedGaussianCorrection d s u)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    ((Set.Ioi (Real.pi / 2)).indicator (fun u : ℝ => u ^ (s / 2 - 1))) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (fun N =>
      ((measurable_id.pow_const _).mul
        ((measurable_const.sub (measurable_sphericalGaussianBackground d N hd)).max
          measurable_const)).aestronglyMeasurable)
  case refine_3 =>
    exact ((integrableOn_Ioi_rpow_of_lt (by linarith : s / 2 - 1 < -1)
      (div_pos Real.pi_pos (by norm_num))).integrable_indicator measurableSet_Ioi).mono_measure
        Measure.restrict_le_self
  case refine_4 =>
    exact ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu =>
      ((tendsto_const_nhds.sub (tendsto_sphericalGaussianBackground d hd u hu)).max
        tendsto_const_nhds).const_mul (u ^ (s / 2 - 1)))
  filter_upwards [(tendsto_sphericalGaussianBackground d hd (Real.pi / 2)
    (div_pos Real.pi_pos (by norm_num))).eventually
      (lt_mem_nhds (one_lt_B_half_pi d hd))] with N hN
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [weightedSphericalNegativeReference, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.le _) (le_max_right _ _))]
  by_cases hcut : Real.pi / 2 < u
  case neg =>
    have hbg : 1 ≤ sphericalGaussianBackground d N u :=
      hN.le.trans (sphericalGaussianBackground_antitone d N hd (le_of_not_gt hcut))
    simp [Set.indicator_of_notMem (show u ∉ Set.Ioi (Real.pi / 2) from hcut),
      max_eq_right (sub_nonpos.mpr hbg)]
  simpa only [Set.indicator_of_mem (show u ∈ Set.Ioi (Real.pi / 2) from hcut), mul_one] using
    mul_le_mul_of_nonneg_left
      (max_le (sub_le_self 1 (sphericalGaussianBackground_nonneg d N u)) zero_le_one)
      (Real.rpow_nonneg hu.le (s / 2 - 1))

/-- The finite-sphere scalar reference converges to the exact shift in `W`. -/
theorem tendsto_sphericalReferenceConstant (d : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hsd : s < (d : ℝ)) (hs_ne : s ≠ 0) :
    Tendsto (fun N : ℕ => sphericalReferenceConstant d N s) atTop (nhds (c0 d s)) := by
  rcases lt_or_gt_of_ne hs_ne with hs_neg | hs_pos
  · simpa only [sphericalReferenceConstant, if_neg (not_lt_of_ge hs_neg.le),
      Riesz.Stationary.gamma_correction_eq_c0 d s hs_neg] using
      (tendsto_integral_weightedSphericalNegativeReference d hd s hs_neg).const_mul
        (gamma_s s)
  · simpa only [sphericalReferenceConstant, if_pos hs_pos, neg_mul,
      Riesz.Stationary.gamma_positive_reference_eq_neg_c0 d s hs_pos hsd, neg_neg] using
      (tendsto_integral_weightedSphericalPositiveReference d hd s hs_pos hsd).const_mul
        (-gamma_s s)

end Riesz.Asymptotics
