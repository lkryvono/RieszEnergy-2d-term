import Riesz.Stationary.GridWithinGaussian

/-! Background Gaussian pair integrals for the covariance of the independent grid.
All infinite sums and pair integrals stay in ENNReal until their finiteness is established. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Stationary

theorem integrable_gaussian_norm (d : ℕ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun y : Rd d => Real.exp (-t * ‖y‖ ^ 2)) volume := by
  apply Integrable.of_integral_ne_zero
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm ht]
  exact (Real.rpow_pos_of_pos (div_pos Real.pi_pos ht) _).ne'

theorem lintegral_gaussian_norm (d : ℕ) (t : ℝ) (ht : 0 < t) :
    (∫⁻ y : Rd d, ENNReal.ofReal (Real.exp (-t * ‖y‖ ^ 2)) ∂volume) =
      ENNReal.ofReal (B d t) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussian_norm d t ht)
    (ae_of_all volume (fun _ => (Real.exp_pos _).le)),
    GaussianFourier.integral_rexp_neg_mul_sq_norm ht]
  simp only [B, Rd, finrank_euclideanSpace_fin]

theorem lintegral_gaussian_translate (d : ℕ) (t : ℝ) (ht : 0 < t) (x : Rd d) :
    (∫⁻ y : Rd d, ENNReal.ofReal (Real.exp (-(t * ‖y - x‖ ^ 2))) ∂volume) =
      ENNReal.ofReal (B d t) := by
  simpa only [neg_mul] using (lintegral_sub_right_eq_self
    (fun y : Rd d => ENNReal.ofReal (Real.exp (-t * ‖y‖ ^ 2))) x).trans
      (lintegral_gaussian_norm d t ht)

theorem anchoredGaussian_background_lintegral (d : ℕ) (t : ℝ) (ht : 0 < t) :
    (∫⁻ p, anchoredGaussianKernel d t p ∂volume.prod volume) =
      ENNReal.ofReal (B d t) := by
  rw [lintegral_prod _ (measurable_anchoredGaussianKernel d t).aemeasurable]
  have hinner : (fun x : Rd d => ∫⁻ y, anchoredGaussianKernel d t (x, y) ∂volume) =
      (cube d 1).indicator (fun _ => ENNReal.ofReal (B d t)) := by
    funext x
    by_cases hx : x ∈ cube d 1 <;>
      simp [anchoredGaussianKernel, hx, lintegral_gaussian_translate d t ht x]
  simp only [hinner, lintegral_indicator_const (Riesz.Negative.measurableSet_cube d 1),
    Riesz.Negative.volume_cube, ENNReal.ofReal_one, one_pow, mul_one]

theorem lattice_pair_lintegral_sum (d : ℕ) (L : ℝ) (hL : 0 < L) (u : Rd d)
    (k : Rd d × Rd d → ℝ≥0∞) :
    (∑' z : GridIndex d, ∑' w : GridIndex d, ∫⁻ p, k p
      ∂(volume.restrict (latticeCell d L u z)).prod
        (volume.restrict (latticeCell d L u w))) =
      ∫⁻ p, k p ∂volume.prod volume := by
  rw [← ENNReal.tsum_prod, ← lintegral_sum_measure,
    ← Measure.prod_sum (fun z : GridIndex d => volume.restrict (latticeCell d L u z))
      (fun w : GridIndex d => volume.restrict (latticeCell d L u w))]
  simp only [latticeCells_volume_sum d L hL u]

/-- The complete background cell-pair sum is exactly the showcase Gaussian background. -/
theorem lattice_anchoredGaussian_sum (d : ℕ) (L : ℝ) (hL : 0 < L)
    (u : Rd d) (t : ℝ) (ht : 0 < t) :
    (∑' z : GridIndex d, ∑' w : GridIndex d, ∫⁻ p, anchoredGaussianKernel d t p
      ∂(volume.restrict (latticeCell d L u z)).prod
        (volume.restrict (latticeCell d L u w))) =
      ENNReal.ofReal (B d t) := by
  rw [lattice_pair_lintegral_sum d L hL u, anchoredGaussian_background_lintegral d t ht]

def gaussianPairKernel (d : ℕ) (t : ℝ) (p : Rd d × Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(t * ‖p.2 - p.1‖ ^ 2)))

theorem measurable_gaussianPairKernel (d : ℕ) (t : ℝ) :
    Measurable (gaussianPairKernel d t) := by
  exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul ((continuous_snd.sub continuous_fst).norm.pow 2)).neg).measurable

theorem lattice_cell_pair_lintegral_translate (d : ℕ) (L : ℝ) (u : Rd d)
    (z w : GridIndex d) (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ p, k p ∂(volume.restrict (latticeCell d L u z)).prod
      (volume.restrict (latticeCell d L u w))) =
      ∫⁻ p, k (u + latticeOrigin d L z + p.1, u + latticeOrigin d L w + p.2)
        ∂(volume.restrict (cube d L)).prod (volume.restrict (cube d L)) := by
  rw [latticeCell, latticeCell, ← Riesz.Negative.map_cube_volume_translation,
    ← Riesz.Negative.map_cube_volume_translation]
  rw [Measure.map_prod_map _ _ (measurable_const_add (u + latticeOrigin d L z))
    (measurable_const_add (u + latticeOrigin d L w)), lintegral_map hk
      ((measurable_const_add (u + latticeOrigin d L z)).prodMap
        (measurable_const_add (u + latticeOrigin d L w)))]
  rfl

theorem measurable_latticeShiftedPairKernel (d : ℕ) (L : ℝ)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    Measurable (fun p : Rd d × (Rd d × Rd d) => ∑' z : GridIndex d,
      k (p.1 + latticeOrigin d L z + p.2.1, p.1 + latticeOrigin d L z + p.2.2)) := by
  exact Measurable.tsum (fun z => hk.comp
    (((measurable_fst.add_const (latticeOrigin d L z)).add
      (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_fst.add_const (latticeOrigin d L z)).add
        (measurable_snd.comp measurable_snd))))

theorem lattice_pair_base_lintegral_tsum (d : ℕ) (L : ℝ) (u : Rd d)
    (μ : Measure (Rd d × Rd d)) (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∑' z : GridIndex d, ∫⁻ p,
      k (u + latticeOrigin d L z + p.1, u + latticeOrigin d L z + p.2) ∂μ) =
      ∫⁻ p, ∑' z : GridIndex d,
        k (u + latticeOrigin d L z + p.1, u + latticeOrigin d L z + p.2) ∂μ := by
  exact (lintegral_tsum (fun z => (hk.comp
    ((measurable_const.add measurable_fst).prodMk
      (measurable_const.add measurable_snd))).aemeasurable)).symm

/-- The same-cell background has the same phase factor as the tuple pairs. -/
theorem randomPhase_sameCellBackgroundGaussian (d m : ℕ) (hm : 0 < m) (t : ℝ) :
    (∫⁻ u, ∑' z : GridIndex d, ∫⁻ p, anchoredGaussianKernel d t p
      ∂(volume.restrict (latticeCell d (m : ℝ) u z)).prod
        (volume.restrict (latticeCell d (m : ℝ) u z)) ∂Riesz.Negative.cubeUniform d m) =
      ((m : ℝ≥0∞) ^ d)⁻¹ * ∫⁻ p, gaussianPairKernel d t p
        ∂(volume.restrict (cube d (m : ℝ))).prod (volume.restrict (cube d (m : ℝ))) := by
  simp_rw [lattice_cell_pair_lintegral_translate d (m : ℝ) _ _ _ _
    (measurable_anchoredGaussianKernel d t)]
  simp_rw [lattice_pair_base_lintegral_tsum d (m : ℝ) _ _ _
    (measurable_anchoredGaussianKernel d t)]
  letI := Riesz.Negative.cubeUniform_probability d m hm
  rw [lintegral_lintegral_swap ((measurable_latticeShiftedPairKernel d (m : ℝ) _
    (measurable_anchoredGaussianKernel d t)).aemeasurable)]
  simp_rw [randomPhase_anchoredGaussian_lintegral d m hm t]
  exact lintegral_const_mul _ (measurable_gaussianPairKernel d t)

theorem measurable_cellBackgroundPairIntegral (d : ℕ) (L : ℝ)
    (z w : GridIndex d) (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    Measurable (fun u : Rd d => ∫⁻ p, k p
      ∂(volume.restrict (latticeCell d L u z)).prod
        (volume.restrict (latticeCell d L u w))) := by
  simp_rw [lattice_cell_pair_lintegral_translate d L _ z w k hk]
  exact (hk.comp (((measurable_fst.add_const (latticeOrigin d L z)).add
    (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_fst.add_const (latticeOrigin d L w)).add
        (measurable_snd.comp measurable_snd)))).lintegral_prod_right'

theorem measurable_gridSameCellPairMean (d n : ℕ) (L : ℝ)
    (Qcell : Measure (Fin n → Rd d)) [IsProbabilityMeasure Qcell]
    (z : GridIndex d) (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    Measurable (fun u : Rd d => ∫⁻ x : GridMarks d n,
      tuplePairSum d n k (gridCellTuple d n L u z x) ∂gridMarksLaw d n Qcell) := by
  simp_rw [gridMarks_same_cell_pair_lintegral d n L _ Qcell z k hk]
  exact ((measurable_tuplePairSum d n k hk).comp
    (measurable_phaseTranslateTuple d n L z)).lintegral_prod_right'

end Riesz.Stationary
