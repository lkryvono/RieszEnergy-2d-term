import Riesz.Negative.CubeTiling
import Riesz.Negative.SampledRounding

/-! Half-unit partitions of diffuse cube measures. These supply the continuous
cell inputs required by the verified sampling-and-rounding construction. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

abbrev HalfUnitCellIndex (d m : ℕ) := Fin d → Fin (2 * m)

def halfUnitCell (d m : ℕ) (z : HalfUnitCellIndex d m) : Set (Rd d) :=
  gridCell d (2 * m) (1 / 2) z

theorem halfUnitCell_measurable (d m : ℕ) (z : HalfUnitCellIndex d m) :
    MeasurableSet (halfUnitCell d m z) := by
  exact translatedCube_measurable d (1 / 2) _

theorem volume_halfUnitCell (d m : ℕ) (z : HalfUnitCellIndex d m) :
    volume (halfUnitCell d m z) = (ENNReal.ofReal (1 / 2 : ℝ)) ^ d := by
  exact volume_translatedCube d (1 / 2) _

theorem halfUnitCell_subset_cube (d m : ℕ) (z : HalfUnitCellIndex d m) :
    halfUnitCell d m z ⊆ cube d (m : ℝ) := by
  simpa only [halfUnitCell, Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc,
    one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), one_mul] using
    gridCell_subset_cube d (2 * m) (1 / 2) (by norm_num) z

theorem halfUnitCells_cover_cube (d m : ℕ) :
    (⋃ z : HalfUnitCellIndex d m, halfUnitCell d m z) = cube d (m : ℝ) := by
  simpa only [halfUnitCell, Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc,
    one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), one_mul] using
    gridCells_cover_cube d (2 * m) (1 / 2) (by norm_num)

theorem halfUnitCells_pairwise_disjoint (d m : ℕ) :
    Pairwise (fun z w : HalfUnitCellIndex d m =>
      Disjoint (halfUnitCell d m z) (halfUnitCell d m w)) := by
  exact gridCells_pairwise_disjoint d (2 * m) (1 / 2) (by norm_num)

theorem halfUnitCell_diameter_le (d m : ℕ) (z : HalfUnitCellIndex d m)
    (x y : Rd d) (hx : x ∈ halfUnitCell d m z) (hy : y ∈ halfUnitCell d m z) :
    ‖x - y‖ ≤ Real.sqrt d * (1 / 2) := by
  rcases hx with ⟨x, hx, rfl⟩
  rcases hy with ⟨y, hy, rfl⟩
  simpa only [add_sub_add_left_eq_sub] using
    cubeCellLabel_dist_le d (1 / 2) (by norm_num) x y
      (fun i => (hx i).1) (fun i => (hy i).1)
      ((cubeCellLabel_eq_zero d (1 / 2) (by norm_num) x hx).trans
        (cubeCellLabel_eq_zero d (1 / 2) (by norm_num) y hy).symm)

theorem twice_volume_halfUnitCell_le_one (d m : ℕ) (hd : 2 ≤ d)
    (z : HalfUnitCellIndex d m) :
    (2 : ℝ≥0∞) * volume (halfUnitCell d m z) ≤ 1 := by
  rw [volume_halfUnitCell]
  refine (mul_le_mul_right (pow_le_pow_of_le_one
    (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 2 : ℝ) from zero_le)
    (by norm_num) hd) (2 : ℝ≥0∞)).trans ?_
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

end Riesz.Negative
