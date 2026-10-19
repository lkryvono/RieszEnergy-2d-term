import Riesz.Definitions
import Riesz.Energy
import Riesz.Stationary.Infimum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Assembly of the exact showcase theorem

This module proves the normalization and little-o bookkeeping. It does not
assume the admitted `RieszShowcase.main_theorem` as a premise. The substantial
analytic inputs are recorded explicitly, and remain proof obligations until
they have been constructed from the paper's lower and upper bounds.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase
open scoped Topology Asymptotics

namespace Riesz.Asymptotics

/-- The analytic conclusions required to assemble the public theorem.
This is a proposition describing obligations, not an axiom asserting them. -/
structure AnalyticClaims (d : ℕ) (s : ℝ) : Prop where
  normalizedLimit : Tendsto
    (fun N : ℕ => (E_K d s N - V_K d s * (N : ℝ) ^ (2 : ℕ)) /
      (N : ℝ) ^ (1 + s / (d : ℝ)))
    atTop (nhds ((omega d) ^ (-s / (d : ℝ)) * e d s))
  infimumFinite : eExtended d s = (e d s : EReal)
  positiveSign : 0 < s → e d s < 0
  attained : ∃ P : ConfigurationLaw d, Admissible d P ∧ W d s P = (e d s : EReal)
  balancedLimit : ∀ q : ℝ, 0 < q → q < 2 → s = -q →
    Tendsto (fun m : ℕ => b d q m / (m : ℝ) ^ d)
      atTop (nhds (e d (-q))) ∧
    e d (-q) = sInf {r : ℝ | ∃ m : ℕ, 1 ≤ m ∧ r = b d q m / (m : ℝ) ^ d}

/-- The sphere area used in the showcase is strictly positive. -/
theorem omega_pos (d : ℕ) : 0 < omega d := by
  unfold omega
  exact div_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity))

/-- The normalized limiting coefficient converts to the Riesz coefficient. -/
theorem coefficient_identity (d : ℕ) (s : ℝ) :
    s * ((omega d) ^ (-s / (d : ℝ)) * e d s) =
      C d s / (omega d) ^ (s / (d : ℝ)) := by
  simp [C, Real.rpow_neg (omega_pos d).le, div_eq_mul_inv, mul_comm, mul_assoc]

/-- Exact remainder bookkeeping, before passing to a limit. -/
theorem remainder_ratio (d N : ℕ) (s : ℝ) (hs : s ≠ 0)
    (hN : 0 < N) (henergy : E_s d s N = s * E_K d s N) :
    (E_s d s N - (V_s d s * (N : ℝ) ^ (2 : ℕ) +
      C d s / (omega d) ^ (s / (d : ℝ)) * (N : ℝ) ^ (1 + s / (d : ℝ)))) /
      (N : ℝ) ^ (1 + s / (d : ℝ)) =
    s * ((E_K d s N - V_K d s * (N : ℝ) ^ (2 : ℕ)) /
      (N : ℝ) ^ (1 + s / (d : ℝ))) - C d s / (omega d) ^ (s / (d : ℝ)) := by
  rw [henergy, V_K]
  have hpow : (N : ℝ) ^ (1 + s / (d : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _).ne'
  field_simp [hs, hpow, (Real.rpow_pos_of_pos (omega_pos d) (s / (d : ℝ))).ne']
  ring

/-- The normalized sphere limit implies exactly the little-o clause in the showcase. -/
theorem rieszExpansion_of_analyticClaims (d : ℕ) (s : ℝ) (hs : s ≠ 0)
    (h : AnalyticClaims d s) :
    (fun N : ℕ => E_s d s N - (V_s d s * (N : ℝ) ^ (2 : ℕ) +
      C d s / (omega d) ^ (s / (d : ℝ)) * (N : ℝ) ^ (1 + s / (d : ℝ))))
      =o[atTop] (fun N : ℕ => (N : ℝ) ^ (1 + s / (d : ℝ))) := by
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).2 ?_
  swap
  · have hlim : Tendsto
        (fun N : ℕ => s * ((E_K d s N - V_K d s * (N : ℝ) ^ (2 : ℕ)) /
          (N : ℝ) ^ (1 + s / (d : ℝ))) - C d s / (omega d) ^ (s / (d : ℝ)))
        atTop (nhds 0) := by
      simpa only [coefficient_identity, sub_self] using
        (h.normalizedLimit.const_mul s).sub_const (C d s / (omega d) ^ (s / (d : ℝ)))
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (remainder_ratio d N s hs hN
      (Riesz.Energy.optimalRieszEnergy_eq_mul_optimalKernelEnergy d s N hs)).symm
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact fun hz => ((Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _).ne' hz).elim

/-- The two sign branches imply the strict negativity of the second coefficient. -/
theorem C_neg_of_analyticClaims (d : ℕ) (s : ℝ) (hd : 2 ≤ d)
    (hs_lower : -2 < s) (hs_upper : s < (d : ℝ)) (hs : s ≠ 0)
    (h : AnalyticClaims d s) : C d s < 0 := by
  exact (lt_or_gt_of_ne hs).elim
    (fun hn => mul_neg_of_neg_of_pos hn
      (Riesz.Stationary.e_pos_of_neg_of_finite d s hd hs_lower hs_upper hn h.infimumFinite))
    (fun hp => mul_neg_of_pos_of_neg hp (h.positiveSign hp))

/-- Assemble every clause of the exact showcase statement from the analytic obligations. -/
theorem main_theorem_of_analyticClaims
    (d : ℕ) (s : ℝ)
    (hd : 2 ≤ d) (hs_lower : -2 < s) (hs_upper : s < (d : ℝ)) (hs_ne : s ≠ 0)
    (h : AnalyticClaims d s) :
    (fun N : ℕ =>
      E_s d s N -
        (V_s d s * (N : ℝ) ^ (2 : ℕ) +
          C d s / (omega d) ^ (s / (d : ℝ)) * (N : ℝ) ^ (1 + s / (d : ℝ))))
      =o[atTop] (fun N : ℕ => (N : ℝ) ^ (1 + s / (d : ℝ))) ∧
    C d s = s * e d s ∧
    C d s < 0 ∧
    Tendsto
      (fun N : ℕ =>
        (E_K d s N - V_K d s * (N : ℝ) ^ (2 : ℕ)) /
          (N : ℝ) ^ (1 + s / (d : ℝ)))
      atTop (nhds ((omega d) ^ (-s / (d : ℝ)) * e d s)) ∧
    eExtended d s = (e d s : EReal) ∧
    (0 < s → e d s < 0) ∧
    (s < 0 → 0 < e d s) ∧
    (∃ P : ConfigurationLaw d, Admissible d P ∧ W d s P = (e d s : EReal)) ∧
    (∀ q : ℝ, 0 < q → q < 2 → s = -q →
      Tendsto (fun m : ℕ => b d q m / (m : ℝ) ^ d)
        atTop (nhds (e d (-q))) ∧
      e d (-q) = sInf {r : ℝ | ∃ m : ℕ, 1 ≤ m ∧ r = b d q m / (m : ℝ) ^ d}) := by
  exact ⟨rieszExpansion_of_analyticClaims d s hs_ne h, rfl,
    C_neg_of_analyticClaims d s hd hs_lower hs_upper hs_ne h, h.normalizedLimit, h.infimumFinite,
    h.positiveSign,
    (fun hn => Riesz.Stationary.e_pos_of_neg_of_finite d s hd hs_lower hs_upper hn h.infimumFinite),
    h.attained, h.balancedLimit⟩

end Riesz.Asymptotics
