import Riesz.Definitions
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict

/-! First mean measures of stationary configuration laws. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal NNReal

namespace Riesz.Stationary

/-- Stationarity of a law makes its first mean measure translation invariant. -/
theorem join_isAddLeftInvariant (d : ℕ) (P : ConfigurationLaw d)
    (hP : IsStationary d P) : P.join.IsAddLeftInvariant := by
  exact ⟨fun a => (Measure.join_map_map (f := fun x : Rd d => a + x)
    (measurable_const.add measurable_id) P).symm.trans (congrArg Measure.join (hP a))⟩

/-- Finite local second moments give a locally finite first mean measure. -/
theorem join_isFiniteMeasureOnCompacts (d : ℕ) (P : ConfigurationLaw d)
    [IsProbabilityMeasure P]
    (hsecond : ∀ D : Set (Rd d), MeasurableSet D → Bornology.IsBounded D →
      (∫⁻ μ, (μ D) ^ (2 : ℕ) ∂P) < ∞) : IsFiniteMeasureOnCompacts P.join := by
  refine ⟨fun K hK => ?_⟩
  rw [Measure.join_apply hK.measurableSet]
  refine (lintegral_mono (g := fun μ : Measure (Rd d) => 1 + (μ K) ^ (2 : ℕ))
    (fun μ => ?_)).trans_lt ?_
  · by_cases h : μ K ≤ 1
    · exact h.trans (le_add_of_nonneg_right (show 0 ≤ (μ K) ^ (2 : ℕ) from bot_le))
    · exact (le_self_pow₀ (le_of_not_ge h) (by decide : (2 : ℕ) ≠ 0)).trans
        (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ 1 from bot_le))
  · rw [lintegral_add_left measurable_const, lintegral_const]
    simpa only [measure_univ, mul_one] using
      ENNReal.add_lt_top.mpr
        ⟨by simp, hsecond K hK.measurableSet hK.isBounded⟩

/-- A stationary law with finite local second moments has constant mean density. -/
theorem join_eq_smul_volume (d : ℕ) (P : ConfigurationLaw d)
    [IsProbabilityMeasure P] (hstationary : IsStationary d P)
    (hsecond : ∀ D : Set (Rd d), MeasurableSet D → Bornology.IsBounded D →
      (∫⁻ μ, (μ D) ^ (2 : ℕ) ∂P) < ∞) :
    ∃ c : ℝ≥0, P.join = c • (volume : Measure (Rd d)) := by
  letI : P.join.IsAddLeftInvariant := join_isAddLeftInvariant d P hstationary
  letI : IsFiniteMeasureOnCompacts P.join := join_isFiniteMeasureOnCompacts d P hsecond
  exact ⟨P.join.addHaarScalarFactor volume, Measure.isAddLeftInvariant_eq_smul P.join volume⟩

/-- The bounded-set mean condition in the showcase determines the full mean measure. -/
theorem join_eq_volume_of_admissible (d : ℕ) (P : ConfigurationLaw d)
    (hP : Admissible d P) : P.join = (volume : Measure (Rd d)) := by
  apply Measure.ext_of_iUnion_eq_univ
    (s := fun n : ℕ => Metric.closedBall (0 : Rd d) (n : ℝ))
    (Metric.iUnion_closedBall_nat (0 : Rd d))
  intro n
  ext D hD
  rw [Measure.restrict_apply hD, Measure.restrict_apply hD,
    Measure.join_apply (hD.inter measurableSet_closedBall)]
  exact hP.2.2.2.1 _ (hD.inter measurableSet_closedBall)
    (Metric.isBounded_closedBall.subset Set.inter_subset_right)

end Riesz.Stationary
