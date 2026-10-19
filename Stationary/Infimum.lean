import Riesz.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Euclidean infimum: extended lower bound, finiteness, and signs

All energies and admissible laws are exactly those in the showcase. In
particular, the nonnegative integral is kept in ENNReal before adding the
finite real constant. No admitted theorem from the showcase is used.
-/

noncomputable section
open MeasureTheory RieszShowcase

namespace Riesz.Stationary

/-- Every stationary energy is bounded below by its finite shift, even when
the nonnegative integral is infinite. Admissibility is not needed here. -/
theorem c0_le_W (d : ℕ) (s : ℝ) (P : ConfigurationLaw d) :
    (c0 d s : EReal) ≤ W d s P := by
  unfold W
  exact le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _)

/-- The Euclidean variational infimum retains the same finite lower bound. -/
theorem c0_le_eExtended (d : ℕ) (s : ℝ) :
    (c0 d s : EReal) ≤ eExtended d s := by
  exact le_sInf (fun _ ⟨P, _, hP⟩ => hP ▸ c0_le_W d s P)

/-- In particular, the extended infimum can never be negative infinity. -/
theorem eExtended_ne_bot (d : ℕ) (s : ℝ) : eExtended d s ≠ ⊥ := by
  exact ne_of_gt ((EReal.bot_lt_coe (c0 d s)).trans_le (c0_le_eExtended d s))

/-- The upper finiteness obligation is exactly the existence of an admissible
law with finite energy; the lower finiteness bound is already proved. -/
theorem eExtended_ne_top_of_competitor (d : ℕ) (s : ℝ)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    eExtended d s ≠ ⊤ := by
  exact ne_of_lt (lt_of_le_of_lt (sInf_le ⟨P, hP, rfl⟩) hW.lt_top)

/-- A finite admissible competitor makes the extended infimum equal to the
ordinary real constant appearing in the public theorem. -/
theorem infimumFinite_of_competitor (d : ℕ) (s : ℝ)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    eExtended d s = (e d s : EReal) := by
  exact (EReal.coe_toReal (eExtended_ne_top_of_competitor d s P hP hW)
    (eExtended_ne_bot d s)).symm

/-- The finite real Euclidean infimum inherits its lower bound. -/
theorem c0_le_e_of_finite (d : ℕ) (s : ℝ)
    (hfinite : eExtended d s = (e d s : EReal)) : c0 d s ≤ e d s := by
  exact EReal.coe_le_coe_iff.mp (hfinite ▸ c0_le_eExtended d s)

/-- The reference lower bound is strictly positive at negative exponents. -/
theorem c0_pos_of_neg (d : ℕ) (s : ℝ) (hd : 2 ≤ d)
    (hs_lower : -2 < s) (hs_upper : s < (d : ℝ)) (hs_neg : s < 0) :
    0 < c0 d s := by
  unfold c0
  apply div_pos_of_neg_of_neg
  · have hd_pos : 0 < d := Nat.lt_of_lt_of_le (by decide) hd
    exact neg_neg_of_pos (mul_pos (Nat.cast_pos.mpr hd_pos)
      (Real.rpow_pos_of_pos Real.pi_pos _))
  · have hgamma_arg : 0 < 1 + s / 2 := by linarith
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hs_neg (sub_pos.mpr hs_upper))
      (Real.Gamma_pos_of_pos hgamma_arg)

/-- The negative-exponent sign is a consequence of finiteness and the proved
positive reference bound; it is not an independent analytic assumption. -/
theorem e_pos_of_neg_of_finite (d : ℕ) (s : ℝ) (hd : 2 ≤ d)
    (hs_lower : -2 < s) (hs_upper : s < (d : ℝ)) (hs_neg : s < 0)
    (hfinite : eExtended d s = (e d s : EReal)) : 0 < e d s := by
  exact lt_of_lt_of_le (c0_pos_of_neg d s hd hs_lower hs_upper hs_neg)
    (c0_le_e_of_finite d s hfinite)

/-- A strictly negative finite competitor supplies both finiteness and the
strictly negative sign. The construction of such a law is the remaining task. -/
theorem infimumFinite_and_e_neg_of_competitor (d : ℕ) (s : ℝ)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P < 0) :
    eExtended d s = (e d s : EReal) ∧ e d s < 0 := by
  have he_neg : eExtended d s < 0 :=
    (show eExtended d s ≤ W d s P from sInf_le ⟨P, hP, rfl⟩).trans_lt hW
  exact ⟨(EReal.coe_toReal (he_neg.trans EReal.zero_lt_top).ne
      (eExtended_ne_bot d s)).symm,
    EReal.toReal_neg he_neg (eExtended_ne_bot d s)⟩

end Riesz.Stationary
