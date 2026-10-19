import Riesz.Energy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact-count correction in the positive-exponent upper bound

The positive upper bound in `paper.tex`, Proposition `prop:positive-upper`,
builds a random spherical configuration with an almost-correct number of
points. These are the algebraic identities and the lower-energy estimate
needed when adding uniform points or selecting a uniform subset. The
probabilistic construction, sphere patch estimate, and resulting limit remain
separate obligations.
-/

noncomputable section

namespace Riesz.Asymptotics

open RieszShowcase

/-- The continuous normalized energy is positive in the positive-exponent
range, as needed to discard the background term in count adjustment. -/
theorem positiveExponent_background_pos (d : ℕ) (s : ℝ)
    (hd : 0 < d) (hs : 0 < s) (hsd : s < (d : ℝ)) : 0 < V_K d s := by
  have hdreal : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have harg₁ : 0 < ((d : ℝ) + 1) / 2 := by positivity
  have harg₂ : 0 < ((d : ℝ) - s) / 2 := by linarith
  have harg₃ : 0 < (d : ℝ) - s / 2 := by linarith
  have hg₁ := Real.Gamma_pos_of_pos harg₁
  have hg₂ := Real.Gamma_pos_of_pos harg₂
  have hg₃ := Real.Gamma_pos_of_pos harg₃
  unfold V_K V_s
  positivity

/-- The probability that a fixed ordered pair survives a uniformly chosen
`N`-subset of an `m`-point configuration. -/
def pairSurvivalFactor (N m : ℕ) : ℝ :=
  (N : ℝ) * ((N : ℝ) - 1) / ((m : ℝ) * ((m : ℝ) - 1))

/-- The centered energy identity for adding `N-m` independent uniform points.
Here `V` is the uniform-background ordered-pair potential. -/
theorem underCount_centered_identity (N m : ℕ) (V E : ℝ) :
    E + V * (2 * (m : ℝ) * ((N : ℝ) - (m : ℝ)) +
      ((N : ℝ) - (m : ℝ)) * ((N : ℝ) - (m : ℝ) - 1)) -
        V * (N : ℝ) ^ 2 =
      (E - V * (m : ℝ) ^ 2) - V * ((N : ℝ) - (m : ℝ)) := by
  ring

/-- The exact centered-energy formula when each old ordered pair survives
with probability `pairSurvivalFactor N m`. This is the algebraic part of the
uniform-subset argument; no probability law is silently assumed here. -/
theorem overCount_centered_identity (N m : ℕ) (V E : ℝ) (hm : 1 < m) :
    pairSurvivalFactor N m * E - V * (N : ℝ) ^ 2 =
      pairSurvivalFactor N m * (E - V * (m : ℝ) ^ 2) -
        V * (N : ℝ) * ((m : ℝ) - (N : ℝ)) / ((m : ℝ) - 1) := by
  have hmreal : (1 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < m)
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    linarith
  unfold pairSurvivalFactor
  field_simp [hm0, hm1]
  ring

/-- A fixed pair's survival probability lies in `[0,1]` when one chooses a
smaller nonempty subset. -/
theorem pairSurvivalFactor_nonneg (N m : ℕ) (hN : 1 ≤ N) (hNm : N < m) :
    0 ≤ pairSurvivalFactor N m := by
  have hmreal : (1 : ℝ) < m := by exact_mod_cast (lt_of_le_of_lt hN hNm)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold pairSurvivalFactor
  exact div_nonneg (mul_nonneg (by positivity) (by linarith))
    (mul_nonneg (by positivity) (by linarith))

/-- The quantitative pair-loss estimate used in the paper for the
overfull-count correction. -/
theorem pairSurvivalFactor_gap_bound (N m : ℕ) (hN : 1 ≤ N) (hNm : N < m) :
    1 - pairSurvivalFactor N m ≤
      2 * ((m : ℝ) - (N : ℝ)) / (m : ℝ) := by
  have hmreal : (1 : ℝ) < m := by exact_mod_cast (lt_of_le_of_lt hN hNm)
  have hNreal : (N : ℝ) + 1 ≤ m := by
    exact_mod_cast (show N + 1 ≤ m from hNm)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < m)
  have hm1 : (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < (m : ℝ) - 1)
  have hgap : 0 ≤ (m : ℝ) - (N : ℝ) := by linarith
  have hmid : (m : ℝ) + (N : ℝ) - 1 ≤ 2 * ((m : ℝ) - 1) := by linarith
  have hden : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by positivity
  have hfactor :
      1 - pairSurvivalFactor N m =
        ((m : ℝ) - (N : ℝ)) * ((m : ℝ) + (N : ℝ) - 1) /
          ((m : ℝ) * ((m : ℝ) - 1)) := by
    unfold pairSurvivalFactor
    field_simp [hm0, hm1]
    ring
  rw [hfactor]
  calc
    ((m : ℝ) - (N : ℝ)) * ((m : ℝ) + (N : ℝ) - 1) /
        ((m : ℝ) * ((m : ℝ) - 1)) ≤
      ((m : ℝ) - (N : ℝ)) * (2 * ((m : ℝ) - 1)) /
        ((m : ℝ) * ((m : ℝ) - 1)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmid hgap) hden
    _ = 2 * ((m : ℝ) - (N : ℝ)) / (m : ℝ) := by
      field_simp [hm0, hm1]

/-- The pair-survival probability is at most one. -/
theorem pairSurvivalFactor_le_one (N m : ℕ) (hN : 1 ≤ N) (hNm : N < m) :
    pairSurvivalFactor N m ≤ 1 := by
  have hmreal : (1 : ℝ) < m := by exact_mod_cast (lt_of_le_of_lt hN hNm)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNmreal : (N : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt hNm)
  have hden : 0 < (m : ℝ) * ((m : ℝ) - 1) := by positivity
  have hgap : 0 ≤ ((m : ℝ) - (N : ℝ)) *
      ((m : ℝ) + (N : ℝ) - 1) := by
    have hmid : 0 ≤ (m : ℝ) + (N : ℝ) - 1 := by linarith
    exact mul_nonneg (sub_nonneg.mpr hNmreal) hmid
  unfold pairSurvivalFactor
  apply (div_le_iff₀ hden).2
  nlinarith [hgap]

/-- If a centered `m`-point energy obeys the paper's universal lower bound,
the adverse overfull-count correction costs at most the displayed error. The
nonpositive background term is retained in the left side. -/
theorem overCount_adverse_bound
    (N m : ℕ) (p K V D : ℝ) (hN : 1 ≤ N) (hNm : N < m)
    (hK : 0 ≤ K) (hV : 0 ≤ V)
    (hD : -K * (m : ℝ) ^ p ≤ D) :
    pairSurvivalFactor N m * D -
      V * (N : ℝ) * ((m : ℝ) - (N : ℝ)) / ((m : ℝ) - 1) ≤
        D + 2 * K * ((m : ℝ) - (N : ℝ)) * (m : ℝ) ^ (p - 1) := by
  have hmreal : (1 : ℝ) < m := by exact_mod_cast (lt_of_le_of_lt hN hNm)
  have hNmreal : (N : ℝ) + 1 ≤ m := by
    exact_mod_cast (show N + 1 ≤ m from hNm)
  have hmpos : (0 : ℝ) < m := by linarith
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hble := pairSurvivalFactor_le_one N m hN hNm
  have hfactor := pairSurvivalFactor_gap_bound N m hN hNm
  have hpow : (m : ℝ) ^ p = (m : ℝ) * (m : ℝ) ^ (p - 1) := by
    have hp : p = (p - 1) + 1 := by ring
    conv_lhs => rw [hp, Real.rpow_add hmpos, Real.rpow_one]
    ring
  have hpow_nonneg : 0 ≤ K * (m : ℝ) ^ p :=
    mul_nonneg hK (Real.rpow_nonneg hmpos.le _)
  have hmult := mul_le_mul_of_nonpos_left hD (sub_nonpos.mpr hble)
  have hstep1 : pairSurvivalFactor N m * D ≤
      D + (1 - pairSurvivalFactor N m) * K * (m : ℝ) ^ p := by
    nlinarith [hmult]
  have hstep2 : (1 - pairSurvivalFactor N m) * K * (m : ℝ) ^ p ≤
      2 * K * ((m : ℝ) - (N : ℝ)) * (m : ℝ) ^ (p - 1) := by
    calc
      (1 - pairSurvivalFactor N m) * K * (m : ℝ) ^ p =
          (1 - pairSurvivalFactor N m) * (K * (m : ℝ) ^ p) := by ring
      _ ≤ (2 * ((m : ℝ) - (N : ℝ)) / (m : ℝ)) *
          (K * (m : ℝ) ^ p) :=
            mul_le_mul_of_nonneg_right hfactor hpow_nonneg
      _ = 2 * K * ((m : ℝ) - (N : ℝ)) * (m : ℝ) ^ (p - 1) := by
        rw [hpow]
        field_simp [hm0]
  have hbackground : 0 ≤
      V * (N : ℝ) * ((m : ℝ) - (N : ℝ)) / ((m : ℝ) - 1) := by
    have hNreal : (0 : ℝ) ≤ N := by positivity
    have hgap : (0 : ℝ) ≤ (m : ℝ) - (N : ℝ) := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg hV hNreal) hgap) (by linarith)
  calc
    pairSurvivalFactor N m * D -
        V * (N : ℝ) * ((m : ℝ) - (N : ℝ)) / ((m : ℝ) - 1) ≤
      pairSurvivalFactor N m * D := sub_le_self _ hbackground
    _ ≤ D + (1 - pairSurvivalFactor N m) * K * (m : ℝ) ^ p := hstep1
    _ ≤ D + 2 * K * ((m : ℝ) - (N : ℝ)) * (m : ℝ) ^ (p - 1) :=
      add_le_add_right hstep2 D

end Riesz.Asymptotics
