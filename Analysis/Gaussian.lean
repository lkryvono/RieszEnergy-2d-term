import Riesz.Definitions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar Gaussian representation of the Riesz kernels

These are the scalar identities in the paper's Lemma `lem:gamma`, using
the exact kernel and Gamma normalization from the showcase.
-/

noncomputable section
open MeasureTheory RieszShowcase Filter
open scoped Topology

namespace Riesz.Analysis

/-- The Gamma normalization is positive throughout the theorem's range. -/
theorem gamma_s_pos (s : ℝ) (hs : -2 < s) : 0 < gamma_s s := by
  unfold gamma_s
  have harg : 0 < 1 + s / 2 := by linarith
  positivity

/-- Positive-exponent scalar Gaussian representation, with the paper's
coefficient `1 / (2 * Gamma (1 + s / 2))`. -/
theorem gamma_kernel_pos (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    K_s s r = gamma_s s *
      ∫ t : ℝ in Set.Ioi 0, t ^ (s / 2 - 1) * Real.exp (-(t * r ^ (2 : ℕ))) := by
  have hscale :
      (∫ t : ℝ in Set.Ioi 0, t ^ (s / 2 - 1) * Real.exp (-(t * r ^ (2 : ℕ)))) =
      (1 / r ^ (2 : ℕ)) ^ (s / 2) * Real.Gamma (s / 2) := by
    simpa only [mul_comm] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi (half_pos hs) (sq_pos_of_pos hr)
  rw [hscale, K_s, gamma_s]
  rw [add_comm (1 : ℝ) (s / 2), Real.Gamma_add_one (half_pos hs).ne']
  have hpow : (1 / r ^ (2 : ℕ)) ^ (s / 2) = r ^ (-s) := by
    rw [one_div, Real.inv_rpow (sq_nonneg r), ← Real.rpow_natCast_mul hr.le 2]
    norm_num [Real.rpow_neg hr.le, show (2 : ℝ) * (s / 2) = s from by ring]
  rw [hpow]
  field_simp [hs.ne', (Real.Gamma_pos_of_pos (half_pos hs)).ne']

/-- The cancellation estimate needed at zero and the uniform tail estimate
for the negative-exponent Gaussian integral. -/
theorem norm_exp_neg_sub_one_le (x : ℝ) (hx : 0 ≤ x) :
    ‖Real.exp (-x) - 1‖ ≤ min x 1 := by
  have hneg : Real.exp (-x) - 1 ≤ 0 :=
    sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))
  rw [Real.norm_eq_abs, abs_of_nonpos hneg]
  exact le_min (by linarith [Real.add_one_le_exp (-x)]) (by linarith [Real.exp_pos (-x)])

/-- Absolute convergence of the cancellation integral for `-1 < a < 0`.
The integrand has order `x^a` at zero and `x^(a-1)` at infinity. -/
theorem integrable_negative_gamma (a : ℝ) (ha_lower : -1 < a) (ha_upper : a < 0) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * (Real.exp (-x) - 1)) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one), integrableOn_union]
  constructor
  · have hbase : IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' ha_lower)
    refine hbase.mono' ((measurable_id.pow_const (a - 1)).mul
      (measurable_id.neg.exp.sub_const 1)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    have hpower : x ^ (a - 1) * x = x ^ a := by
      rw [← Real.rpow_add_one hx.1.ne', sub_add_cancel]
    exact (mul_le_mul_of_nonneg_left
      ((norm_exp_neg_sub_one_le x hx.1.le).trans (min_le_left x 1))
      (Real.rpow_nonneg hx.1.le (a - 1))).trans_eq hpower
  · have hbase : IntegrableOn (fun x : ℝ => x ^ (a - 1)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hbase.mono' ((measurable_id.pow_const (a - 1)).mul
      (measurable_id.neg.exp.sub_const 1)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := zero_le_one.trans hx.le
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hx0 _)
      ((norm_exp_neg_sub_one_le x hx0).trans (min_le_right x 1))

/-- The primitive used in integration by parts vanishes at zero. This bound
retains the cancellation instead of separating the two divergent terms. -/
theorem norm_negative_gamma_boundary_le (a x : ℝ) (hx : 0 ≤ x) :
    ‖x ^ a * (Real.exp (-x) - 1)‖ ≤ x ^ (a + 1) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx a)]
  exact (mul_le_mul_of_nonneg_left
    ((norm_exp_neg_sub_one_le x hx).trans (min_le_left x 1))
    (Real.rpow_nonneg hx a)).trans
    (by simpa only [Real.rpow_one] using Real.le_rpow_add hx a 1)

/-- Continuity of the negative-Gamma integration-by-parts primitive at `0+`. -/
theorem continuousWithinAt_negative_gamma_boundary (a : ℝ) (ha : -1 < a) :
    ContinuousWithinAt (fun x : ℝ => x ^ a * (Real.exp (-x) - 1)) (Set.Ici 0) 0 := by
  simp only [ContinuousWithinAt, neg_zero, Real.exp_zero, sub_self, mul_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg _))
    (g := fun x : ℝ => x ^ (a + 1)) ?_ ?_
  swap
  · have hpos : 0 < a + 1 := by linarith
    simpa only [Real.zero_rpow hpos.ne'] using
      ((Real.continuous_rpow_const hpos.le).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact norm_negative_gamma_boundary_le a x hx

/-- The same integration-by-parts primitive vanishes at infinity for `a < 0`. -/
theorem tendsto_negative_gamma_boundary_atTop (a : ℝ) (ha : a < 0) :
    Tendsto (fun x : ℝ => x ^ a * (Real.exp (-x) - 1)) atTop (nhds 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ a) atTop (nhds 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr ha)
  simpa only [zero_mul, Function.comp_def] using
    hpow.mul ((Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).sub_const 1)

/-- Derivative of the primitive used for the convergent negative-Gamma integral. -/
theorem hasDerivAt_negative_gamma_boundary (a x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => u ^ a * (Real.exp (-u) - 1))
      (a * (x ^ (a - 1) * (Real.exp (-x) - 1)) - x ^ a * Real.exp (-x)) x := by
  convert! (Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne')).mul
    ((hasDerivAt_neg x).exp.sub_const 1) using 1
  ring

/-- The convergent Gamma integral after subtracting the constant term.
This is the integration-by-parts identity for `-1 < a < 0`. -/
theorem integral_negative_gamma (a : ℝ) (ha_lower : -1 < a) (ha_upper : a < 0) :
    (∫ x : ℝ in Set.Ioi 0, x ^ (a - 1) * (Real.exp (-x) - 1)) =
      Real.Gamma (1 + a) / a := by
  have ha_arg : 0 < a + 1 := by linarith
  have hg : IntegrableOn (fun x : ℝ => x ^ a * Real.exp (-x)) (Set.Ioi 0) := by
    simpa only [add_sub_cancel_right, mul_comm] using Real.GammaIntegral_convergent ha_arg
  have hdint : IntegrableOn
      (fun x : ℝ => a * (x ^ (a - 1) * (Real.exp (-x) - 1)) - x ^ a * Real.exp (-x))
      (Set.Ioi 0) :=
    ((integrable_negative_gamma a ha_lower ha_upper).const_mul a).sub hg
  have hz := integral_Ioi_of_hasDerivAt_of_tendsto
    (continuousWithinAt_negative_gamma_boundary a ha_lower)
    (fun x hx => hasDerivAt_negative_gamma_boundary a x hx)
    hdint (tendsto_negative_gamma_boundary_atTop a ha_upper)
  rw [integral_sub ((integrable_negative_gamma a ha_lower ha_upper).const_mul a) hg,
    integral_const_mul] at hz
  have hgamma : (∫ x : ℝ in Set.Ioi 0, x ^ a * Real.exp (-x)) = Real.Gamma (a + 1) := by
    simpa only [add_sub_cancel_right, mul_comm] using (Real.Gamma_eq_integral ha_arg).symm
  simp only [hgamma, neg_zero, Real.exp_zero, sub_self, mul_zero] at hz
  exact (eq_div_iff ha_upper.ne).mpr (by simpa only [add_comm, mul_comm] using sub_eq_zero.mp hz)

/-- Scaling the convergent negative-Gamma integral by a positive factor. -/
theorem integral_negative_gamma_scaled (a b : ℝ) (ha_lower : -1 < a)
    (ha_upper : a < 0) (hb : 0 < b) :
    (∫ x : ℝ in Set.Ioi 0, x ^ (a - 1) * (Real.exp (-(x * b)) - 1)) =
      b ^ (-a) * (Real.Gamma (1 + a) / a) := by
  have hfactor :
      (∫ x : ℝ in Set.Ioi 0, (b⁻¹ * x) ^ (a - 1) * (Real.exp (-x) - 1)) =
        b⁻¹ ^ (a - 1) * (∫ x : ℝ in Set.Ioi 0, x ^ (a - 1) * (Real.exp (-x) - 1)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change (b⁻¹ * x) ^ (a - 1) * (Real.exp (-x) - 1) =
      b⁻¹ ^ (a - 1) * (x ^ (a - 1) * (Real.exp (-x) - 1))
    rw [Real.mul_rpow (inv_pos.mpr hb).le (Set.mem_Ioi.mp hx).le, mul_assoc]
  have hchange :
      (∫ x : ℝ in Set.Ioi 0, x ^ (a - 1) * (Real.exp (-(x * b)) - 1)) =
        b⁻¹ * (∫ x : ℝ in Set.Ioi 0, (b⁻¹ * x) ^ (a - 1) * (Real.exp (-x) - 1)) := by
    simpa only [inv_mul_cancel_left₀ hb.ne', mul_zero, smul_eq_mul, mul_comm] using
      integral_comp_mul_left_Ioi
        (fun x : ℝ => (b⁻¹ * x) ^ (a - 1) * (Real.exp (-x) - 1)) 0 hb
  rw [hchange, hfactor, integral_negative_gamma a ha_lower ha_upper, ← mul_assoc]
  rw [mul_comm b⁻¹ (b⁻¹ ^ (a - 1)), ← Real.rpow_add_one (inv_pos.mpr hb).ne',
    sub_add_cancel, Real.inv_rpow hb.le, Real.rpow_neg hb.le]

/-- The Gaussian representation of `K_s` for the negative exponents in the paper. -/
theorem gamma_kernel_neg (s r : ℝ) (hs_lower : -2 < s) (hs_upper : s < 0)
    (hr : 0 < r) :
    K_s s r = gamma_s s *
      (∫ t : ℝ in Set.Ioi 0, t ^ (s / 2 - 1) * (Real.exp (-(t * r ^ 2)) - 1)) := by
  have hhalf_lower : -1 < s / 2 := by linarith
  have hscale := integral_negative_gamma_scaled (s / 2) (r ^ 2) hhalf_lower
    (div_neg_of_neg_of_pos hs_upper zero_lt_two) (sq_pos_of_pos hr)
  have hpow : (r ^ 2) ^ (-(s / 2)) = r ^ (-s) := by
    rw [← Real.rpow_natCast_mul hr.le 2]
    norm_num [show (2 : ℝ) * -(s / 2) = -s from by ring]
  rw [hscale, hpow, K_s, gamma_s]
  field_simp [hs_upper.ne]
  exact (div_self (Real.Gamma_pos_of_pos (show 0 < (2 + s) / 2 by linarith)).ne').symm

/-- The negative-exponent formula extends to zero distance, as in Lemma `gamma`. -/
theorem gamma_kernel_neg_nonneg (s r : ℝ) (hs_lower : -2 < s) (hs_upper : s < 0)
    (hr : 0 ≤ r) :
    K_s s r = gamma_s s *
      (∫ t : ℝ in Set.Ioi 0, t ^ (s / 2 - 1) * (Real.exp (-(t * r ^ 2)) - 1)) := by
  rcases eq_or_lt_of_le hr with hzero | hpos
  · subst r
    simp [K_s, Real.zero_rpow (neg_pos.mpr hs_upper).ne']
  · exact gamma_kernel_neg s r hs_lower hs_upper hpos

/-- The scaled improper integral is an ordinary integrable function on `(0,∞)`. -/
theorem integrable_negative_gamma_scaled (a b : ℝ) (ha_lower : -1 < a)
    (ha_upper : a < 0) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * (Real.exp (-(x * b)) - 1))
      (Set.Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_negative_gamma_scaled a b ha_lower ha_upper hb]
  exact mul_ne_zero (Real.rpow_pos_of_pos hb _).ne'
    (div_ne_zero (Real.Gamma_pos_of_pos (show 0 < 1 + a by linarith)).ne' ha_upper.ne)

end Riesz.Analysis
