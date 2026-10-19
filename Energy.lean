import Riesz.Definitions
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Ring

/-!
# Ordered energies and the sign-dependent optimal-energy conversion

All objects here use the concrete sphere configurations and energy definitions
from the showcase. The original admitted main theorem is never used.
-/

noncomputable section
open RieszShowcase
open scoped Classical Pointwise

namespace Riesz.Energy

/-- The ordered normalized-kernel energy inside the showcase's infimum. -/
def kernelEnergy (d : ℕ) (s : ℝ) (N : ℕ) (x : SphereConfiguration d N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    if i = j then 0 else K_s s (chord d (x.val i) (x.val j))

/-- Division by the exponent commutes with the finite ordered-pair sum. -/
theorem kernelEnergy_eq_rieszEnergy_div (d : ℕ) (s : ℝ) (N : ℕ)
    (x : SphereConfiguration d N) : kernelEnergy d s N x = rieszEnergy d s N x / s := by
  simp only [kernelEnergy, rieszEnergy, K_s, Finset.sum_div, ite_div, zero_div]

/-- Positive scalar multiplication commutes with real infima, including the
empty and unbounded cases where Mathlib's real infimum is totalized to zero. -/
theorem sInf_image_mul_pos (c : ℝ) (hc : 0 < c) (S : Set ℝ) :
    sInf ((fun x => c * x) '' S) = c * sInf S := by
  by_cases hb : BddBelow S
  swap
  · have hi : ¬ BddBelow ((fun x => c * x) '' S) := by
      intro hI
      apply hb
      simpa only [Set.image_image, Function.comp_def, OrderIso.mulLeft₀_symm,
        OrderIso.mulLeft₀_apply, inv_mul_cancel_left₀ hc.ne', Set.image_id'] using
        (OrderIso.mulLeft₀ c hc).symm.monotone.map_bddBelow hI
    simp only [Real.sInf_of_not_bddBelow hb, Real.sInf_of_not_bddBelow hi, mul_zero]
  · rcases S.eq_empty_or_nonempty with rfl | hn
    · simp only [Set.image_empty, Real.sInf_empty, mul_zero]
    · exact ((OrderIso.mulLeft₀ c hc).map_csInf' hn hb).symm

/-- Positive multiplication commutes with real suprema with the same
totalization convention as the infimum. -/
theorem sSup_image_mul_pos (c : ℝ) (hc : 0 < c) (S : Set ℝ) :
    sSup ((fun x => c * x) '' S) = c * sSup S := by
  have h := sInf_image_mul_pos c hc (-S)
  rw [Set.image_neg_of_apply_neg_eq_neg (fun x _ => mul_neg c x), Real.sInf_neg,
    Real.sInf_neg, mul_neg] at h
  exact neg_injective h

/-- A negative multiplier exchanges the real infimum and supremum. -/
theorem sInf_image_mul_neg (c : ℝ) (hc : c < 0) (S : Set ℝ) :
    sInf ((fun x => c * x) '' S) = c * sSup S := by
  have h := sSup_image_mul_pos (-c) (neg_pos.mpr hc) S
  simpa only [← Set.image_neg_eq_neg, Set.image_image, Function.comp_def,
    neg_mul, neg_neg] using
    (Real.sInf_neg ((fun x => -c * x) '' S)).trans (congrArg Neg.neg h)

/-- The sign-dependent conversion of optimal energies in the paper.
It also holds for empty energy sets because both real extrema then equal zero. -/
theorem optimalKernelEnergy_eq_optimalRieszEnergy_div (d : ℕ) (s : ℝ) (N : ℕ)
    (hs : s ≠ 0) : E_K d s N = E_s d s N / s := by
  have hr : Set.range (kernelEnergy d s N) =
      (fun r : ℝ => s⁻¹ * r) '' Set.range (rieszEnergy d s N) := by
    rw [← Set.range_comp']
    congr 1
    funext x
    simp only [kernelEnergy_eq_rieszEnergy_div, div_eq_mul_inv, mul_comm]
  change sInf (Set.range (kernelEnergy d s N)) = E_s d s N / s
  rw [hr]
  rcases lt_or_gt_of_ne hs with hn | hp
  · rw [sInf_image_mul_neg s⁻¹ (inv_lt_zero.mpr hn)]
    simp only [E_s, if_neg (not_lt_of_ge hn.le), div_eq_mul_inv, mul_comm]
  · rw [sInf_image_mul_pos s⁻¹ (inv_pos.mpr hp)]
    simp only [E_s, if_pos hp, div_eq_mul_inv, mul_comm]

/-- Multiplicative form used to transfer the normalized limit to Riesz energy. -/
theorem optimalRieszEnergy_eq_mul_optimalKernelEnergy (d : ℕ) (s : ℝ) (N : ℕ)
    (hs : s ≠ 0) : E_s d s N = s * E_K d s N := by
  simpa only [mul_comm] using
    ((eq_div_iff hs).mp (optimalKernelEnergy_eq_optimalRieszEnergy_div d s N hs)).symm

end Riesz.Energy
