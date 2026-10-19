import Riesz.Analysis.Gaussian

/-! The finite scalar correction between the negative-exponent covariance
formula and the nonnegative extended energy in the showcase. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Stationary

def gaussianCorrection (d : ℕ) (t : ℝ) : ℝ := max (1 - B d t) 0

def weightedGaussianCorrection (d : ℕ) (s t : ℝ) : ℝ :=
  t ^ (s / 2 - 1) * gaussianCorrection d t

theorem B_le_one_of_pi_le (d : ℕ) (t : ℝ) (ht : Real.pi ≤ t) : B d t ≤ 1 := by
  exact Real.rpow_le_one (div_nonneg Real.pi_pos.le (Real.pi_pos.trans_le ht).le)
    ((div_le_one (Real.pi_pos.trans_le ht)).mpr ht) (by positivity)

theorem one_le_B_of_le_pi (d : ℕ) (t : ℝ) (ht : 0 < t) (hpi : t ≤ Real.pi) :
    1 ≤ B d t := by
  exact Real.one_le_rpow ((one_le_div ht).mpr hpi) (by positivity)

theorem weightedGaussianCorrection_tail (d : ℕ) (s t : ℝ) (ht : Real.pi < t) :
    weightedGaussianCorrection d s t =
      t ^ (s / 2 - 1) - Real.pi ^ ((d : ℝ) / 2) * t ^ ((s - (d : ℝ)) / 2 - 1) := by
  rw [weightedGaussianCorrection, gaussianCorrection,
    max_eq_left (sub_nonneg.mpr (B_le_one_of_pi_le d t ht.le)), mul_sub, mul_one, B]
  rw [Real.div_rpow Real.pi_pos.le (Real.pi_pos.trans ht).le,
    div_eq_mul_inv (Real.pi ^ ((d : ℝ) / 2)) (t ^ ((d : ℝ) / 2)),
    ← Real.rpow_neg (Real.pi_pos.trans ht).le]
  rw [mul_left_comm _ (Real.pi ^ ((d : ℝ) / 2)), ← Real.rpow_add (Real.pi_pos.trans ht)]
  rw [show s / 2 - 1 + -((d : ℝ) / 2) = (s - (d : ℝ)) / 2 - 1 by ring]

theorem weightedGaussianCorrection_indicator (d : ℕ) (s : ℝ) :
    (fun t => weightedGaussianCorrection d s t) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (Set.Ioi Real.pi).indicator (fun t =>
        t ^ (s / 2 - 1) - Real.pi ^ ((d : ℝ) / 2) * t ^ ((s - (d : ℝ)) / 2 - 1)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rcases le_or_gt t Real.pi with hpi | hpi
  · simp only [Set.indicator_of_notMem (show t ∉ Set.Ioi Real.pi from not_lt.mpr hpi),
      weightedGaussianCorrection, gaussianCorrection,
      max_eq_right (sub_nonpos.mpr (one_le_B_of_le_pi d t ht hpi)), mul_zero]
  · rw [weightedGaussianCorrection_tail d s t hpi,
      Set.indicator_of_mem (show t ∈ Set.Ioi Real.pi from hpi)]

theorem weightedGaussianCorrection_integrable (d : ℕ) (s : ℝ) (hs : s < 0) :
    IntegrableOn (weightedGaussianCorrection d s) (Set.Ioi 0) := by
  have htail : IntegrableOn (fun t : ℝ =>
      t ^ (s / 2 - 1) - Real.pi ^ ((d : ℝ) / 2) * t ^ ((s - (d : ℝ)) / 2 - 1))
      (Set.Ioi Real.pi) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : s / 2 - 1 < -1) Real.pi_pos).sub
      ((integrableOn_Ioi_rpow_of_lt
        (by linarith [Nat.cast_nonneg (α := ℝ) d] : (s - (d : ℝ)) / 2 - 1 < -1)
        Real.pi_pos).const_mul _)
  refine Integrable.congr ?_ (weightedGaussianCorrection_indicator d s).symm
  rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_left Real.pi_pos.le]
  exact htail

theorem integral_weightedGaussianCorrection_tail (d : ℕ) (s : ℝ) :
    (∫ t : ℝ in Set.Ioi 0, weightedGaussianCorrection d s t) =
      ∫ t : ℝ in Set.Ioi Real.pi,
        t ^ (s / 2 - 1) - Real.pi ^ ((d : ℝ) / 2) * t ^ ((s - (d : ℝ)) / 2 - 1) := by
  rw [integral_congr_ae (weightedGaussianCorrection_indicator d s), integral_indicator measurableSet_Ioi]
  simp only [Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi,
    max_eq_left Real.pi_pos.le]

theorem integral_weightedGaussianCorrection (d : ℕ) (s : ℝ) (hs : s < 0) :
    (∫ t : ℝ in Set.Ioi 0, weightedGaussianCorrection d s t) =
      -(2 * (d : ℝ) * Real.pi ^ (s / 2)) / (s * ((d : ℝ) - s)) := by
  rw [integral_weightedGaussianCorrection_tail]
  have hA : s / 2 - 1 < -1 := by linarith
  have hB : (s - (d : ℝ)) / 2 - 1 < -1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  rw [integral_sub (integrableOn_Ioi_rpow_of_lt hA Real.pi_pos)
    ((integrableOn_Ioi_rpow_of_lt hB Real.pi_pos).const_mul _), integral_const_mul,
    integral_Ioi_rpow_of_lt hA Real.pi_pos, integral_Ioi_rpow_of_lt hB Real.pi_pos]
  simp only [sub_add_cancel]
  rw [← mul_div_assoc, mul_neg, ← Real.rpow_add Real.pi_pos]
  rw [show (d : ℝ) / 2 + (s - (d : ℝ)) / 2 = s / 2 by ring]
  field_simp [hs.ne, (sub_pos.mpr (hs.trans_le (Nat.cast_nonneg d))).ne',
    (sub_neg.mpr (hs.trans_le (Nat.cast_nonneg d))).ne]
  ring

/-- The finite shift in `W` is exactly the integrated covariance correction. -/
theorem gamma_correction_eq_c0 (d : ℕ) (s : ℝ) (hs_neg : s < 0) :
    gamma_s s * (∫ t : ℝ in Set.Ioi 0, weightedGaussianCorrection d s t) = c0 d s := by
  rw [integral_weightedGaussianCorrection d s hs_neg, gamma_s, c0]
  field_simp

theorem gaussianCorrection_measurable (d : ℕ) : Measurable (gaussianCorrection d) := by
  exact (measurable_const.sub
    ((measurable_const.div measurable_id).pow_const ((d : ℝ) / 2))).max measurable_const

theorem weightedGaussianCorrection_measurable (d : ℕ) (s : ℝ) :
    Measurable (weightedGaussianCorrection d s) := by
  exact (measurable_id.pow_const _).mul (gaussianCorrection_measurable d)

theorem weightedGaussianCorrection_nonneg (d : ℕ) (s t : ℝ) (ht : 0 ≤ t) :
    0 ≤ weightedGaussianCorrection d s t := by
  exact mul_nonneg (Real.rpow_nonneg ht _) (le_max_right _ _)

theorem weightedGaussianCorrection_lintegral (d : ℕ) (s : ℝ) (hs : s < 0) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (s / 2 - 1)) *
      ENNReal.ofReal (gaussianCorrection d t)) =
      ENNReal.ofReal (∫ t : ℝ in Set.Ioi 0, weightedGaussianCorrection d s t) := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] weightedGaussianCorrection d s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
      weightedGaussianCorrection_nonneg d s t ht.le
  rw [ofReal_integral_eq_lintegral_ofReal (weightedGaussianCorrection_integrable d s hs) hnonneg]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
    (ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)).symm

theorem gamma_correction_lintegral_eq_c0 (d : ℕ) (s : ℝ)
    (hs_lower : -2 < s) (hs_neg : s < 0) :
    ENNReal.ofReal (gamma_s s) *
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (s / 2 - 1)) *
        ENNReal.ofReal (gaussianCorrection d t)) = ENNReal.ofReal (c0 d s) := by
  rw [weightedGaussianCorrection_lintegral d s hs_neg,
    ← ENNReal.ofReal_mul (Riesz.Analysis.gamma_s_pos s hs_lower).le, gamma_correction_eq_c0 d s hs_neg]

end Riesz.Stationary
