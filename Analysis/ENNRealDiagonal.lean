import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Diagonal replacement in nonnegative pair sums, including infinite values.
This gives covariance identities before any subtraction or real conversion. -/

noncomputable section

open scoped ENNReal Classical

namespace Riesz.Analysis

theorem ennreal_tsum_split_diagonal (ι : Type*) (f : ι → ι → ℝ≥0∞) :
    (∑' i : ι, ∑' j : ι, f i j) =
      (∑' i : ι, f i i) + ∑' i : ι, ∑' j : ι, if i = j then 0 else f i j := by
  have hrow (i : ι) : (∑' j : ι, f i j) =
      f i i + ∑' j : ι, if i = j then 0 else f i j := by
    simpa only [eq_comm] using ENNReal.tsum_eq_add_tsum_ite (f := f i) i
  simp_rw [hrow, ENNReal.tsum_add]

theorem ennreal_tsum_replace_diagonal (ι : Type*) (a : ι → ℝ≥0∞) (b : ι → ι → ℝ≥0∞) :
    (∑' i : ι, ∑' j : ι, if i = j then a i else b i j) =
      (∑' i : ι, a i) + ∑' i : ι, ∑' j : ι, if i = j then 0 else b i j := by
  rw [ennreal_tsum_split_diagonal]
  simp +contextual

theorem ennreal_tsum_diagonal_balance (ι : Type*) (a : ι → ℝ≥0∞)
    (b : ι → ι → ℝ≥0∞) :
    (∑' i : ι, ∑' j : ι, if i = j then a i else b i j) + (∑' i : ι, b i i) =
      (∑' i : ι, ∑' j : ι, b i j) + (∑' i : ι, a i) := by
  rw [ennreal_tsum_replace_diagonal, ennreal_tsum_split_diagonal ι b]
  ac_rfl

end Riesz.Analysis
