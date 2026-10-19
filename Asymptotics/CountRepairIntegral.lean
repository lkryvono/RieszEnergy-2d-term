import Riesz.Geometry.CountRepairFromProblem1
import Mathlib.Probability.Moments.Variance

/-!
# Integration of deterministic spherical count repair

The positive upper construction needs a scalar optimal-value inequality,
integrated against its original input law. No repaired configuration law is
constructed here. The count error is controlled by its first and second
moments before the radius normalization is taken.
-/

noncomputable section

open MeasureTheory RieszShowcase Filter
open scoped Topology

namespace Riesz.Asymptotics

/-- For exponents at most one, the overcount cost is controlled by the first
two moments of the deviation from the desired positive count. -/
theorem countRepairCost_le_moments (N M p : ℝ) (hN : 0 < N) (hM : 0 ≤ M)
    (hp : p ≤ 1) :
    max (M - N) 0 * M ^ p ≤
      N ^ p * |M - N| + N ^ (p - 1) * (M - N) ^ 2 := by
  by_cases hMN : M ≤ N
  case neg =>
    have hNM : N < M := lt_of_not_ge hMN
    have hpow : M ^ (p - 1) ≤ N ^ (p - 1) :=
      Real.rpow_le_rpow_of_nonpos hN hNM.le (by linarith)
    have hpowM : M ^ p = M ^ (p - 1) * M := by
      simpa only [sub_add_cancel] using Real.rpow_add_one (hN.trans hNM).ne' (p - 1)
    have hpowN : N ^ p = N ^ (p - 1) * N := by
      simpa only [sub_add_cancel] using Real.rpow_add_one hN.ne' (p - 1)
    rw [max_eq_left (sub_nonneg.mpr hNM.le), abs_of_pos (sub_pos.mpr hNM), hpowM, hpowN]
    nlinarith only [mul_le_mul_of_nonneg_left hpow (mul_nonneg (sub_nonneg.mpr hNM.le) hM)]
  rw [max_eq_right (sub_nonpos.mpr hMN), zero_mul]
  positivity

/-- A probability-law first absolute moment is bounded by its second moment. -/
theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂μ) ≤ Real.sqrt (∫ ω, (f ω) ^ 2 ∂μ) := by
  apply Real.le_sqrt_of_sq_le
  have habs : MemLp (fun ω => |f ω|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hvar := ProbabilityTheory.variance_nonneg (fun ω => |f ω|) μ
  rw [ProbabilityTheory.variance_eq_sub habs] at hvar
  simpa only [Pi.pow_apply, sq_abs] using (sub_nonneg.mp hvar)

/-- Integrate deterministic count repair against the original input law.
Only the input energy and the second count-error moment are needed. -/
theorem positive_sphere_count_repair_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (N : ℕ) (hN : 2 ≤ N)
    (M : Ω → ℕ) (x : ∀ ω, SphereConfiguration d (M ω))
    (hcount : MemLp (fun ω => (M ω : ℝ) - (N : ℝ)) 2 μ)
    (henergy : Integrable (fun ω => Riesz.Energy.kernelEnergy d s (M ω) (x ω) -
      V_K d s * (M ω : ℝ) ^ 2) μ) :
    E_K d s N - V_K d s * (N : ℝ) ^ 2 ≤
      (∫ ω, Riesz.Energy.kernelEnergy d s (M ω) (x ω) -
        V_K d s * (M ω : ℝ) ^ 2 ∂μ) +
      2 * Problem1.part5_energy_constants_positive d s *
        ((N : ℝ) ^ (s / (d : ℝ)) *
          Real.sqrt (∫ ω, ((M ω : ℝ) - (N : ℝ)) ^ 2 ∂μ) +
        (N : ℝ) ^ (s / (d : ℝ) - 1) *
          (∫ ω, ((M ω : ℝ) - (N : ℝ)) ^ 2 ∂μ)) := by
  have hdpos : 0 < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hp : s / (d : ℝ) ≤ 1 := (div_lt_one hdpos).mpr hsd |>.le
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hC : 0 ≤ 2 * Problem1.part5_energy_constants_positive d s :=
    mul_nonneg (by norm_num) ((Problem1.part5_energy_constant_signs d hd).1 s hs hsd).le
  have hpoint : ∀ ω, E_K d s N - V_K d s * (N : ℝ) ^ 2 ≤
      (Riesz.Energy.kernelEnergy d s (M ω) (x ω) - V_K d s * (M ω : ℝ) ^ 2) +
      (2 * Problem1.part5_energy_constants_positive d s) *
        ((N : ℝ) ^ (s / (d : ℝ)) * |(M ω : ℝ) - (N : ℝ)| +
          (N : ℝ) ^ (s / (d : ℝ) - 1) * ((M ω : ℝ) - (N : ℝ)) ^ 2) := by
    intro ω
    nlinarith only [Riesz.Geometry.positive_sphere_count_repair_bound
      d hd s hs hsd N (M ω) hN (x ω),
      mul_le_mul_of_nonneg_left (countRepairCost_le_moments (N : ℝ) (M ω : ℝ)
        (s / (d : ℝ)) hNpos (Nat.cast_nonneg _) hp) hC]
  have habs : Integrable (fun ω => |(M ω : ℝ) - (N : ℝ)|) μ := by
    simpa only [Real.norm_eq_abs] using
      (MemLp.integrable (q := 2) (by norm_num) hcount).norm
  have hmoments : Integrable (fun ω =>
      (N : ℝ) ^ (s / (d : ℝ)) * |(M ω : ℝ) - (N : ℝ)| +
        (N : ℝ) ^ (s / (d : ℝ) - 1) * ((M ω : ℝ) - (N : ℝ)) ^ 2) μ :=
    (habs.const_mul _).add (hcount.integrable_sq.const_mul _)
  have hint := integral_mono (integrable_const (E_K d s N - V_K d s * (N : ℝ) ^ 2))
    (henergy.add (hmoments.const_mul (2 * Problem1.part5_energy_constants_positive d s)))
    hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_const, probReal_univ, one_smul,
    integral_add henergy (hmoments.const_mul (2 * Problem1.part5_energy_constants_positive d s)),
    integral_const_mul,
    integral_add (habs.const_mul _) (hcount.integrable_sq.const_mul _),
    integral_const_mul, integral_const_mul] at hint
  exact hint.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left
      (integral_abs_le_sqrt_integral_sq μ _ hcount) (Real.rpow_nonneg hNpos.le _)) le_rfl)
    hC))

/-- A linear second-moment bound makes the count-repair correction negligible
in the exact `N^(1+p)` normalization. -/
theorem countRepairMomentRatio_tendsto_zero (p K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun N : ℕ =>
      ((N : ℝ) ^ p * Real.sqrt (K * (N : ℝ)) +
        (N : ℝ) ^ (p - 1) * (K * (N : ℝ))) / (N : ℝ) ^ (1 + p))
      atTop (nhds 0) := by
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) / (N : ℝ)) atTop (nhds 0) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hNat))
  have hlim : Tendsto (fun N : ℕ =>
      Real.sqrt K * (Real.sqrt (N : ℝ) / (N : ℝ)) + K / (N : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (hsqrt.const_mul (Real.sqrt K)).add (hNat.const_div_atTop K)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [add_comm (1 : ℝ) p, Real.rpow_add_one hNpos.ne',
    Real.rpow_sub_one hNpos.ne', Real.sqrt_mul hK]
  field_simp [hNpos.ne', (Real.rpow_pos_of_pos hNpos p).ne']

end Riesz.Asymptotics
