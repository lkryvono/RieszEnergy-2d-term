import Riesz.Definitions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A compactness estimate for the spherical local lower bound

The proof of `paper.tex`, Proposition `prop:lower`, bounds local factorial
second moments of pulled-back spherical point processes by a Gaussian pair
energy. This file isolates the deterministic estimate behind that step.
The remaining probabilistic and geometric ingredients are not assumed here.
-/

noncomputable section

open RieszShowcase

namespace Riesz.Asymptotics

/-- Ordered distinct pairs whose endpoints lie in the coordinate ball. -/
def localPairCount (d n : ℕ) (T : ℝ) (x : Fin n → Rd d) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i ≠ j ∧ ‖x i‖ ≤ T ∧ ‖x j‖ ≤ T then 1 else 0

/-- Gaussian ordered-pair energy anchored at points in the ball. -/
def anchoredGaussianPairSum (d n : ℕ) (a T : ℝ) (x : Fin n → Rd d) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i ≠ j ∧ ‖x i‖ ≤ T then
      Real.exp (-a * ‖x i - x j‖ ^ (2 : ℕ)) else 0

private theorem gaussian_pair_bound (d : ℕ) (a T : ℝ)
    (ha : 0 ≤ a) (hT : 0 ≤ T) (x y : Rd d)
    (hx : ‖x‖ ≤ T) (hy : ‖y‖ ≤ T) :
    1 ≤ Real.exp (4 * a * T ^ (2 : ℕ)) *
      Real.exp (-a * ‖x - y‖ ^ (2 : ℕ)) := by
  have hdist : ‖x - y‖ ≤ 2 * T := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ 2 * T := by linarith
  have hsq : ‖x - y‖ ^ (2 : ℕ) ≤ 4 * T ^ (2 : ℕ) := by
    nlinarith [norm_nonneg (x - y)]
  have hexp : 0 ≤ a * (4 * T ^ (2 : ℕ) - ‖x - y‖ ^ (2 : ℕ)) :=
    mul_nonneg ha (sub_nonneg.mpr hsq)
  calc
    1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (a * (4 * T ^ (2 : ℕ) - ‖x - y‖ ^ (2 : ℕ))) :=
      Real.exp_le_exp.mpr hexp
    _ = Real.exp (4 * a * T ^ (2 : ℕ)) *
          Real.exp (-a * ‖x - y‖ ^ (2 : ℕ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The local factorial pair count is bounded by the anchored Gaussian energy.
This is the pathwise estimate used before taking expectations in `prop:lower`.
The exponential factor is exactly the paper's `e^{4aT²}`. -/
theorem localPairCount_le_gaussian (d n : ℕ) (a T : ℝ)
    (ha : 0 ≤ a) (hT : 0 ≤ T) (x : Fin n → Rd d) :
    localPairCount d n T x ≤
      Real.exp (4 * a * T ^ (2 : ℕ)) * anchoredGaussianPairSum d n a T x := by
  simp only [localPairCount, anchoredGaussianPairSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases h : i ≠ j ∧ ‖x i‖ ≤ T ∧ ‖x j‖ ≤ T
  · have h' : i ≠ j ∧ ‖x i‖ ≤ T := ⟨h.1, h.2.1⟩
    simpa only [if_pos h, if_pos h', mul_one] using
      gaussian_pair_bound d a T ha hT (x i) (x j) h.2.1 h.2.2
  · by_cases h' : i ≠ j ∧ ‖x i‖ ≤ T
    · simp only [if_neg h, if_pos h']
      positivity
    · simp [h, h']

end Riesz.Asymptotics
