import Riesz.Negative.RandomRounding
import Mathlib.Tactic.Linarith

/-! An integer total weight removes the last fractional site after rounding. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped Classical

namespace Riesz.Negative

/-- If all weights are in `[0,1]`, at most one is fractional, and their sum is
an integer, then every weight is zero or one. -/
theorem integral_weights_of_integer_sum {n : ℕ} (v : Fin n → ℝ)
    (hv : ∀ k, 0 ≤ v k ∧ v k ≤ 1)
    (hcard : (fractionalSites v).card ≤ 1) (m : ℕ)
    (hsum : (∑ k, v k) = (m : ℝ)) :
    ∀ k, v k = 0 ∨ v k = 1 := by
  intro i
  by_contra hi
  have hfrac_of_not01 (k : Fin n) (hk : ¬ (v k = 0 ∨ v k = 1)) :
      k ∈ fractionalSites v := by
    have hne0 : v k ≠ 0 := fun h => hk (Or.inl h)
    have hne1 : v k ≠ 1 := fun h => hk (Or.inr h)
    simp only [fractionalSites, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨lt_of_le_of_ne (hv k).1 (Ne.symm hne0),
      lt_of_le_of_ne (hv k).2 hne1⟩
  have hi_frac : i ∈ fractionalSites v := hfrac_of_not01 i hi
  have hi_bounds : 0 < v i ∧ v i < 1 := by
    simpa only [fractionalSites, Finset.mem_filter, Finset.mem_univ, true_and]
      using hi_frac
  have hi1 : v i ≠ 1 := ne_of_lt hi_bounds.2
  have hother (k : Fin n) (hki : k ≠ i) : v k = 0 ∨ v k = 1 := by
    by_contra hk
    exact hki ((Finset.card_le_one.mp hcard) k (hfrac_of_not01 k hk) i hi_frac)
  let c : ℕ := (Finset.univ.filter fun k : Fin n => v k = 1).card
  have hrep : (∑ k : Fin n, v k) = v i + (c : ℝ) := by
    calc
      _ = ∑ k : Fin n,
          ((if k = i then v i else 0) + (if v k = 1 then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases hki : k = i
            · subst k
              simp [hi1]
            · rcases hother k hki with h0 | h1
              · simp [hki, h0]
              · simp [hki, h1]
      _ = v i + (c : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [c]
  have hm : v i + (c : ℝ) = (m : ℝ) := hrep.symm.trans hsum
  have hclt : c < m := by
    exact_mod_cast (show (c : ℝ) < (m : ℝ) by linarith [hi_bounds.1])
  have hmlt : m < c + 1 := by
    exact_mod_cast (show (m : ℝ) < (c : ℝ) + 1 by linarith [hi_bounds.2])
  omega

/-- The finite random rounding law has zero-or-one weights almost surely
when its initial total weight is an integer. -/
theorem randomRoundingLaw_integral_final {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) (m : ℕ)
    (hsum : (∑ k, w k) = (m : ℝ)) :
    ∀ᵐ v ∂randomRoundingLaw n w, ∀ k, v k = 0 ∨ v k = 1 := by
  have hcard : (fractionalSites w).card ≤ n + 1 := by
    have hle := (fractionalSites w).card_le_univ
    simp only [Fintype.card_fin] at hle
    omega
  apply (randomRoundingLaw_final n w hw hcard).mono
  intro v hv
  exact integral_weights_of_integer_sum v hv.1 hv.2.2.1 m (hv.2.1.trans hsum)

/-- For zero-or-one weights, the sum equals the number of occupied sites. -/
theorem occupied_card_eq_of_integral_weights {n : ℕ} (v : Fin n → ℝ)
    (h01 : ∀ k, v k = 0 ∨ v k = 1) (m : ℕ)
    (hsum : (∑ k, v k) = (m : ℝ)) :
    (Finset.univ.filter fun k : Fin n => v k = 1).card = m := by
  have hsum_card : (∑ k, v k) =
      ((Finset.univ.filter fun k : Fin n => v k = 1).card : ℝ) := by
    calc
      _ = ∑ k : Fin n, if v k = 1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        rcases h01 k with h0 | h1
        · simp [h0]
        · simp [h1]
      _ = _ := by simp
  exact_mod_cast hsum_card.symm.trans hsum

/-- With integer initial mass, finite random rounding produces exactly that
many occupied sites almost surely. -/
theorem randomRoundingLaw_exact_count {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) (m : ℕ)
    (hsum : (∑ k, w k) = (m : ℝ)) :
    ∀ᵐ v ∂randomRoundingLaw n w,
      (Finset.univ.filter fun k : Fin n => v k = 1).card = m := by
  have hcard : (fractionalSites w).card ≤ n + 1 := by
    have hle := (fractionalSites w).card_le_univ
    simp only [Fintype.card_fin] at hle
    omega
  apply (randomRoundingLaw_final n w hw hcard).mono
  intro v hv
  have hvsum : (∑ k, v k) = (m : ℝ) := hv.2.1.trans hsum
  exact occupied_card_eq_of_integral_weights v
    (integral_weights_of_integer_sum v hv.1 hv.2.2.1 m hvsum) m hvsum

/-- The occupied-site configuration produced by integer-mass rounding has
exactly the initial weighted mean against every scalar test function. -/
theorem randomRoundingLaw_occupied_test_mean {n d : ℕ}
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (m : ℕ) (hsum : (∑ k, w k) = (m : ℝ))
    (x : Fin n → Rd d) (f : Rd d → ℝ) :
    (∫ v, (Finset.univ.filter (fun k : Fin n => v k = 1)).sum
      (fun k => f (x k)) ∂randomRoundingLaw n w) =
        ∑ k : Fin n, w k * f (x k) := by
  calc
    _ = ∫ v, (∑ k : Fin n, v k * f (x k)) ∂randomRoundingLaw n w := by
      apply integral_congr_ae
      filter_upwards [randomRoundingLaw_integral_final w hw m hsum] with v hv
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      rcases hv k with h0 | h1
      · simp [h0]
      · simp [h1]
    _ = _ := randomRoundingLaw_test_mean n w x f

/-- The finite point configuration selected by a zero-or-one terminal weight list. -/
def occupiedSites {n d : ℕ} (x : Fin n → Rd d) (v : Fin n → ℝ) :
    Finset (Rd d) :=
  (Finset.univ.filter fun k : Fin n => v k = 1).image x

/-- Terminal zero-or-one atomic weights are the counting measure of the
occupied sites when the original sites are distinct. -/
theorem weightedAtomicMeasure_eq_occupiedSites {n d : ℕ}
    (x : Fin n → Rd d) (hx : Function.Injective x)
    (v : Fin n → ℝ) (h01 : ∀ k, v k = 0 ∨ v k = 1) :
    weightedAtomicMeasure d n x v =
      ∑ y ∈ occupiedSites x v, Measure.dirac y := by
  unfold weightedAtomicMeasure occupiedSites
  rw [Finset.sum_image hx.injOn]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  rcases h01 k with h0 | h1
  · simp [h0]
  · simp [h1]

/-- Distinct input sites and integer initial mass give an exact-size random
point configuration. -/
theorem randomRoundingLaw_occupiedSites_card {n d : ℕ}
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (m : ℕ) (hsum : (∑ k, w k) = (m : ℝ))
    (x : Fin n → Rd d) (hx : Function.Injective x) :
    ∀ᵐ v ∂randomRoundingLaw n w, (occupiedSites x v).card = m := by
  filter_upwards [randomRoundingLaw_exact_count w hw m hsum] with v hv
  simpa [occupiedSites, Finset.card_image_of_injective _ hx] using hv

/-- Almost every rounded atomic measure is a simple point counting measure. -/
theorem randomRoundingLaw_occupiedSites_measure {n d : ℕ}
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (m : ℕ) (hsum : (∑ k, w k) = (m : ℝ))
    (x : Fin n → Rd d) (hx : Function.Injective x) :
    ∀ᵐ v ∂randomRoundingLaw n w,
      weightedAtomicMeasure d n x v =
        ∑ y ∈ occupiedSites x v, Measure.dirac y := by
  filter_upwards [randomRoundingLaw_integral_final w hw m hsum] with v hv
  exact weightedAtomicMeasure_eq_occupiedSites x hx v hv

/-- The expected sum of a scalar test function over the selected point set
equals its initial weighted sum. -/
theorem randomRoundingLaw_occupiedSites_test_mean {n d : ℕ}
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (m : ℕ) (hsum : (∑ k, w k) = (m : ℝ))
    (x : Fin n → Rd d) (hx : Function.Injective x) (f : Rd d → ℝ) :
    (∫ v, (occupiedSites x v).sum f ∂randomRoundingLaw n w) =
      ∑ k : Fin n, w k * f (x k) := by
  calc
    _ = ∫ v, (Finset.univ.filter (fun k : Fin n => v k = 1)).sum
        (fun k => f (x k)) ∂randomRoundingLaw n w := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact Finset.sum_image hx.injOn
    _ = _ := randomRoundingLaw_occupied_test_mean w hw m hsum x f

/-- The complete finite-atomic discretization step: a random simple point
set has the prescribed integer count and mean, with the signed discrepancy
energy bounded by the initial fractional budget. -/
theorem atomic_discretization {n d : ℕ}
    (q D : ℝ) (hq : 0 < q) (hD : 0 ≤ D)
    (x : Fin n → Rd d) (hx : Function.Injective x)
    (hdiam : ∀ i j, ‖x i - x j‖ ≤ D)
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (m : ℕ) (hsum : (∑ k, w k) = (m : ℝ)) :
    (∀ᵐ v ∂randomRoundingLaw n w,
      (occupiedSites x v).card = m ∧
      weightedAtomicMeasure d n x v =
        ∑ y ∈ occupiedSites x v, Measure.dirac y) ∧
    (∀ f : Rd d → ℝ,
      (∫ v, (occupiedSites x v).sum f ∂randomRoundingLaw n w) =
        ∑ k : Fin n, w k * f (x k)) ∧
    (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun k => v k - w k))
      ∂randomRoundingLaw n w) ≤
        D ^ q / q * totalFractionalBudget w := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [randomRoundingLaw_occupiedSites_card w hw m hsum x hx,
      randomRoundingLaw_occupiedSites_measure w hw m hsum x hx] with v hc hm
    exact ⟨hc, hm⟩
  · intro f
    exact randomRoundingLaw_occupiedSites_test_mean w hw m hsum x hx f
  · exact randomRoundingLaw_expected_energy_le q D hq hD x hx hdiam w hw

end Riesz.Negative
