import Riesz.Stationary.GridLaw
import Mathlib.Probability.Independence.InfinitePi

/-! Pair means and phase averaging for the stationary grid energy comparison.
Cross-cell pairs include every pair of finite labels. Simplicity identifies
distinct labels with distinct sites when this is used in the showcase energy. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Stationary

def gridCellTuple (d n : ℕ) (L : ℝ) (u : Rd d) (z : GridIndex d)
    (x : GridMarks d n) : Fin n → Rd d :=
  Riesz.Negative.translateTuple d n (u + latticeOrigin d L z) (x z)

def gridCellPairMean (d n : ℕ) (L : ℝ) (u : Rd d)
    (Q : Measure (Fin n → Rd d)) (z w : GridIndex d) : Measure (Rd d × Rd d) :=
  ∑ ij : Fin n × Fin n, Measure.map
    (fun x : GridMarks d n => (gridCellTuple d n L u z x ij.1,
      gridCellTuple d n L u w x ij.2)) (gridMarksLaw d n Q)

theorem measurable_gridCellTuple (d n : ℕ) (L : ℝ) (u : Rd d) (z : GridIndex d) :
    Measurable (gridCellTuple d n L u z) := by
  exact (Riesz.Negative.translateTuple d n (u + latticeOrigin d L z)).measurable.comp
    (measurable_pi_apply z)

theorem gridMarksLaw_eval_pair (d n : ℕ) (Q : Measure (Fin n → Rd d))
    [IsProbabilityMeasure Q] (z w : GridIndex d) (hzw : z ≠ w) :
    Measure.map (fun x : GridMarks d n => (x z, x w)) (gridMarksLaw d n Q) =
      Q.prod Q := by
  exact Measure.infinitePi_map_eval_prod (P := fun _ : GridIndex d => Q) hzw

theorem gridMarksLaw_translated_pair (d n : ℕ) (L : ℝ) (u : Rd d)
    (Q : Measure (Fin n → Rd d)) [IsProbabilityMeasure Q]
    (z w : GridIndex d) (hzw : z ≠ w) :
    Measure.map (fun x : GridMarks d n =>
      (gridCellTuple d n L u z x, gridCellTuple d n L u w x)) (gridMarksLaw d n Q) =
      (Riesz.Negative.translateTupleLaw d n (u + latticeOrigin d L z) Q).prod
        (Riesz.Negative.translateTupleLaw d n (u + latticeOrigin d L w) Q) := by
  rw [Riesz.Negative.translateTupleLaw, Riesz.Negative.translateTupleLaw,
    Measure.map_prod_map Q Q (Riesz.Negative.translateTuple d n (u + latticeOrigin d L z)).measurable
      (Riesz.Negative.translateTuple d n (u + latticeOrigin d L w)).measurable,
    ← gridMarksLaw_eval_pair d n Q z w hzw]
  exact (Measure.map_map (f := fun x : GridMarks d n => (x z, x w))
    ((Riesz.Negative.translateTuple d n (u + latticeOrigin d L z)).measurable.prodMap
      (Riesz.Negative.translateTuple d n (u + latticeOrigin d L w)).measurable)
    ((measurable_pi_apply z).prodMk (measurable_pi_apply w))).symm

theorem gridCellPairMean_eq_prod (d n : ℕ) (L : ℝ) (u : Rd d)
    (Q : Measure (Fin n → Rd d)) [IsProbabilityMeasure Q]
    (z w : GridIndex d) (hzw : z ≠ w) :
    gridCellPairMean d n L u Q z w =
      (Riesz.Negative.tupleMeanMeasure d n
        (Riesz.Negative.translateTupleLaw d n (u + latticeOrigin d L z) Q)).prod
      (Riesz.Negative.tupleMeanMeasure d n
        (Riesz.Negative.translateTupleLaw d n (u + latticeOrigin d L w) Q)) := by
  letI := Riesz.Negative.translateTupleLaw_probability d n (u + latticeOrigin d L z) Q
  letI := Riesz.Negative.translateTupleLaw_probability d n (u + latticeOrigin d L w) Q
  rw [← Riesz.Negative.independentTuplePairMean_eq_prod]
  unfold gridCellPairMean Riesz.Negative.independentTuplePairMean
  refine Finset.sum_congr rfl (fun ij _ => ?_)
  rw [← gridMarksLaw_translated_pair d n L u Q z w hzw]
  exact (Measure.map_map (((measurable_pi_apply ij.1).comp measurable_fst).prodMk
    ((measurable_pi_apply ij.2).comp measurable_snd))
    ((measurable_gridCellTuple d n L u z).prodMk (measurable_gridCellTuple d n L u w))).symm

/-- Distinct cells have exactly the background product pair measure. -/
theorem gridMarks_cross_cell_pairMean (d m : ℕ) (u : Rd d)
    (Q : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q)
    (z w : GridIndex d) (hzw : z ≠ w) :
    gridCellPairMean d (m ^ d) (m : ℝ) u Q z w =
      (volume.restrict (latticeCell d (m : ℝ) u z)).prod
        (volume.restrict (latticeCell d (m : ℝ) u w)) := by
  letI : IsProbabilityMeasure Q := hQ.1
  simp only [latticeCell, gridCellPairMean_eq_prod d (m ^ d) (m : ℝ) u Q z w hzw,
    Riesz.Negative.tupleBalanced_translated_mean d m _ Q hQ]

theorem gridCellPairMean_lintegral (d n : ℕ) (L : ℝ) (u : Rd d)
    (Q : Measure (Fin n → Rd d)) (z w : GridIndex d)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ x : GridMarks d n, ∑ ij : Fin n × Fin n,
      k (gridCellTuple d n L u z x ij.1, gridCellTuple d n L u w x ij.2)
      ∂gridMarksLaw d n Q) = ∫⁻ p, k p ∂gridCellPairMean d n L u Q z w := by
  rw [gridCellPairMean, lintegral_finsetSum_measure,
    lintegral_finsetSum (f := fun (ij : Fin n × Fin n) (x : GridMarks d n) =>
      k (gridCellTuple d n L u z x ij.1, gridCellTuple d n L u w x ij.2))
      Finset.univ (fun ij _ => hk.comp
      (((measurable_pi_apply ij.1).comp (measurable_gridCellTuple d n L u z)).prodMk
        ((measurable_pi_apply ij.2).comp (measurable_gridCellTuple d n L u w))))]
  exact Finset.sum_congr rfl (fun ij _ =>
    (lintegral_map hk (((measurable_pi_apply ij.1).comp
      (measurable_gridCellTuple d n L u z)).prodMk
        ((measurable_pi_apply ij.2).comp (measurable_gridCellTuple d n L u w)))).symm)

/-- Nonnegative kernels can be integrated against the exact cross-cell mean. -/
theorem gridMarks_cross_cell_pair_lintegral (d m : ℕ) (u : Rd d)
    (Q : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q)
    (z w : GridIndex d) (hzw : z ≠ w)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ x : GridMarks d (m ^ d), ∑ ij : Fin (m ^ d) × Fin (m ^ d),
      k (gridCellTuple d (m ^ d) (m : ℝ) u z x ij.1,
        gridCellTuple d (m ^ d) (m : ℝ) u w x ij.2) ∂gridMarksLaw d (m ^ d) Q) =
      ∫⁻ p, k p ∂(volume.restrict (latticeCell d (m : ℝ) u z)).prod
        (volume.restrict (latticeCell d (m : ℝ) u w)) := by
  rw [gridCellPairMean_lintegral d (m ^ d) (m : ℝ) u Q z w k hk,
    gridMarks_cross_cell_pairMean d m u Q hQ z w hzw]

theorem lattice_cell_lintegral_translate (d : ℕ) (L : ℝ) (v : Rd d) (z : GridIndex d)
    (f : Rd d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂volume.restrict (latticeCell d L v z)) =
      ∫⁻ u in cube d L, f (u + latticeOrigin d L z + v) ∂volume := by
  rw [latticeCell, ← Riesz.Negative.map_cube_volume_translation,
    lintegral_map hf (measurable_const_add (v + latticeOrigin d L z))]
  simp only [add_comm, add_left_comm]

/-- Averaging a translated cell sum over one phase cube covers all of Euclidean space. -/
theorem lattice_phase_lintegral (d : ℕ) (L : ℝ) (hL : 0 < L) (v : Rd d)
    (f : Rd d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in cube d L, ∑' z : GridIndex d, f (u + latticeOrigin d L z + v) ∂volume) =
      ∫⁻ u, f u ∂volume := by
  rw [lintegral_tsum (f := fun (z : GridIndex d) (u : Rd d) =>
    f (u + latticeOrigin d L z + v))
      (fun z => (hf.comp ((measurable_id.add_const (latticeOrigin d L z)).add_const v)).aemeasurable)]
  simp_rw [← lattice_cell_lintegral_translate d L v _ f hf]
  rw [← lintegral_sum_measure, latticeCells_volume_sum d L hL v]

theorem randomPhase_lattice_lintegral (d m : ℕ) (hm : 0 < m) (v : Rd d)
    (f : Rd d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u, ∑' z : GridIndex d, f (u + latticeOrigin d (m : ℝ) z + v)
      ∂Riesz.Negative.cubeUniform d m) =
      ((m : ℝ≥0∞) ^ d)⁻¹ * ∫⁻ u, f u ∂volume := by
  rw [Riesz.Negative.cubeUniform, lintegral_smul_measure,
    lattice_phase_lintegral d (m : ℝ) (Nat.cast_pos.mpr hm) v f hf, smul_eq_mul]

/-- Gaussian pair test with the showcase's volume-one first-point anchor. -/
def anchoredGaussianKernel (d : ℕ) (t : ℝ) (p : Rd d × Rd d) : ℝ≥0∞ :=
  if p.1 ∈ cube d 1 then ENNReal.ofReal (Real.exp (-(t * ‖p.2 - p.1‖ ^ 2))) else 0

/-- Phase averaging removes the first-point anchor and retains the exact cell-volume factor. -/
theorem randomPhase_anchoredGaussian_lintegral (d m : ℕ) (hm : 0 < m)
    (t : ℝ) (a b : Rd d) :
    (∫⁻ u, ∑' z : GridIndex d, anchoredGaussianKernel d t
      (u + latticeOrigin d (m : ℝ) z + a, u + latticeOrigin d (m : ℝ) z + b)
      ∂Riesz.Negative.cubeUniform d m) =
      ((m : ℝ≥0∞) ^ d)⁻¹ * ENNReal.ofReal (Real.exp (-(t * ‖b - a‖ ^ 2))) := by
  have h := randomPhase_lattice_lintegral d m hm a
    ((cube d 1).indicator (fun _ => ENNReal.ofReal (Real.exp (-(t * ‖b - a‖ ^ 2)))))
    (measurable_const.indicator (Riesz.Negative.measurableSet_cube d 1))
  simp only [lintegral_indicator_const (Riesz.Negative.measurableSet_cube d 1),
    Riesz.Negative.volume_cube, ENNReal.ofReal_one, one_pow, mul_one] at h
  simpa only [anchoredGaussianKernel, add_sub_add_left_eq_sub, Set.indicator_apply] using h

theorem gridCellTuple_ne_of_distinct_cells (d n : ℕ) (L : ℝ) (hL : 0 < L)
    (u : Rd d) (x : GridMarks d n)
    (hx : ∀ z, Function.Injective (x z) ∧ ∀ i, x z i ∈ cube d L)
    (z w : GridIndex d) (hzw : z ≠ w) (i j : Fin n) :
    gridCellTuple d n L u z x i ≠ gridCellTuple d n L u w x j := by
  have hi := gridSites_injective d n L hL u x hx
  exact fun heq => hzw (congrArg Prod.fst (@hi (z, i) (w, j) heq))

/-- The actual off-site kernel has the same cross-cell expectation. -/
theorem gridMarks_cross_cell_offSite_lintegral (d m : ℕ) (hm : 0 < m) (u : Rd d)
    (Q : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q)
    (z w : GridIndex d) (hzw : z ≠ w)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ x : GridMarks d (m ^ d), ∑ ij : Fin (m ^ d) × Fin (m ^ d),
      if gridCellTuple d (m ^ d) (m : ℝ) u z x ij.1 =
          gridCellTuple d (m ^ d) (m : ℝ) u w x ij.2 then 0
      else k (gridCellTuple d (m ^ d) (m : ℝ) u z x ij.1,
        gridCellTuple d (m ^ d) (m : ℝ) u w x ij.2) ∂gridMarksLaw d (m ^ d) Q) =
      ∫⁻ p, k p ∂(volume.restrict (latticeCell d (m : ℝ) u z)).prod
        (volume.restrict (latticeCell d (m : ℝ) u w)) := by
  letI : IsProbabilityMeasure Q := hQ.1
  refine (lintegral_congr_ae ?_).trans
    (gridMarks_cross_cell_pair_lintegral d m u Q hQ z w hzw k hk)
  exact (gridMarksLaw_good d (m ^ d) (m : ℝ) Q hQ.2.1).mono (fun x hx =>
    Finset.sum_congr rfl (fun ij _ => if_neg (gridCellTuple_ne_of_distinct_cells d (m ^ d)
      (m : ℝ) (Nat.cast_pos.mpr hm) u x hx z w hzw ij.1 ij.2)))

theorem measurable_anchoredGaussianKernel (d : ℕ) (t : ℝ) :
    Measurable (anchoredGaussianKernel d t) := by
  exact Measurable.ite ((Riesz.Negative.measurableSet_cube d 1).preimage measurable_fst)
    (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp
        (continuous_const.mul ((continuous_snd.sub continuous_fst).norm.pow 2)).neg).measurable)
    measurable_const

/-- Cross-cell Gaussian pairs, with diagonal exclusion and the exact showcase anchor. -/
theorem gridMarks_cross_cell_offSite_gaussian (d m : ℕ) (hm : 0 < m) (u : Rd d)
    (Q : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q)
    (z w : GridIndex d) (hzw : z ≠ w) (t : ℝ) :
    (∫⁻ x : GridMarks d (m ^ d), ∑ ij : Fin (m ^ d) × Fin (m ^ d),
      if gridCellTuple d (m ^ d) (m : ℝ) u z x ij.1 =
          gridCellTuple d (m ^ d) (m : ℝ) u w x ij.2 then 0
      else anchoredGaussianKernel d t
        (gridCellTuple d (m ^ d) (m : ℝ) u z x ij.1,
          gridCellTuple d (m ^ d) (m : ℝ) u w x ij.2) ∂gridMarksLaw d (m ^ d) Q) =
      ∫⁻ p, anchoredGaussianKernel d t p
        ∂(volume.restrict (latticeCell d (m : ℝ) u z)).prod
          (volume.restrict (latticeCell d (m : ℝ) u w)) := by
  exact gridMarks_cross_cell_offSite_lintegral d m hm u Q hQ z w hzw
    (anchoredGaussianKernel d t) (measurable_anchoredGaussianKernel d t)

end Riesz.Stationary
