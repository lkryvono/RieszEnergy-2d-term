import Riesz.Stationary.GridGaussian

/-! The same-cell Gaussian contribution after averaging the random grid phase.
The finite tuple retains the actual off-site condition until simplicity is used. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Stationary

def tuplePairSum (d n : ℕ) (k : Rd d × Rd d → ℝ≥0∞) (x : Fin n → Rd d) : ℝ≥0∞ :=
  ∑ ij : Fin n × Fin n, k (x ij.1, x ij.2)

def offSiteGaussianKernel (d : ℕ) (t : ℝ) (p : Rd d × Rd d) : ℝ≥0∞ :=
  if p.1 = p.2 then 0 else ENNReal.ofReal (Real.exp (-(t * ‖p.2 - p.1‖ ^ 2)))

def tupleOffSiteGaussian (d n : ℕ) (t : ℝ) (x : Fin n → Rd d) : ℝ≥0∞ :=
  tuplePairSum d n (offSiteGaussianKernel d t) x

theorem measurable_offSiteGaussianKernel (d : ℕ) (t : ℝ) :
    Measurable (offSiteGaussianKernel d t) := by
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_snd.sub continuous_fst).norm.pow 2)).neg).measurable)

theorem measurable_tuplePairSum (d n : ℕ) (k : Rd d × Rd d → ℝ≥0∞)
    (hk : Measurable k) : Measurable (tuplePairSum d n k) := by
  unfold tuplePairSum
  have hsum : Measurable (fun x : Fin n → Rd d => ∑' ij : Fin n × Fin n,
      k (x ij.1, x ij.2)) := Measurable.tsum (fun ij => hk.comp
        ((measurable_pi_apply ij.1).prodMk (measurable_pi_apply ij.2)))
  simpa only [tuplePairSum, tsum_fintype] using hsum

theorem measurable_shiftedPair_lattice_tsum (d : ℕ) (L : ℝ) (a b : Rd d)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    Measurable (fun u : Rd d => ∑' z : GridIndex d,
      k (u + latticeOrigin d L z + a, u + latticeOrigin d L z + b)) := by
  exact Measurable.tsum (fun z => hk.comp
    (((measurable_id.add_const (latticeOrigin d L z)).add_const a).prodMk
      ((measurable_id.add_const (latticeOrigin d L z)).add_const b)))

theorem tuplePairSum_shift_tsum (d n : ℕ) (L : ℝ) (u : Rd d) (x : Fin n → Rd d)
    (k : Rd d × Rd d → ℝ≥0∞) :
    (∑' z : GridIndex d, tuplePairSum d n k
      (Riesz.Negative.translateTuple d n (u + latticeOrigin d L z) x)) =
      ∑ ij : Fin n × Fin n, ∑' z : GridIndex d,
        k (u + latticeOrigin d L z + x ij.1, u + latticeOrigin d L z + x ij.2) := by
  have h : (∑' z : GridIndex d, ∑' ij : Fin n × Fin n,
      k (u + latticeOrigin d L z + x ij.1, u + latticeOrigin d L z + x ij.2)) =
      ∑' ij : Fin n × Fin n, ∑' z : GridIndex d,
        k (u + latticeOrigin d L z + x ij.1, u + latticeOrigin d L z + x ij.2) :=
    ENNReal.tsum_comm
  simpa only [tuplePairSum, tsum_fintype, Riesz.Negative.translateTuple_apply] using h

theorem randomPhase_offSiteGaussian_lintegral (d m : ℕ) (hm : 0 < m)
    (t : ℝ) (a b : Rd d) :
    (∫⁻ u, ∑' z : GridIndex d, offSiteAnchoredGaussianKernel d t
      (u + latticeOrigin d (m : ℝ) z + a, u + latticeOrigin d (m : ℝ) z + b)
      ∂Riesz.Negative.cubeUniform d m) =
      ((m : ℝ≥0∞) ^ d)⁻¹ * offSiteGaussianKernel d t (a, b) := by
  by_cases hab : a = b
  case neg =>
    simpa only [offSiteAnchoredGaussianKernel, offSiteGaussianKernel, add_right_inj,
      if_neg hab] using randomPhase_anchoredGaussian_lintegral d m hm t a b
  case pos => simp [offSiteAnchoredGaussianKernel, offSiteGaussianKernel, hab]

/-- Exact phase average of all off-site pairs from one repeated finite tuple. -/
theorem randomPhase_tupleOffSiteGaussian (d n m : ℕ) (hm : 0 < m)
    (t : ℝ) (x : Fin n → Rd d) :
    (∫⁻ u, ∑' z : GridIndex d, tuplePairSum d n (offSiteAnchoredGaussianKernel d t)
      (Riesz.Negative.translateTuple d n (u + latticeOrigin d (m : ℝ) z) x)
      ∂Riesz.Negative.cubeUniform d m) =
      ((m : ℝ≥0∞) ^ d)⁻¹ * tupleOffSiteGaussian d n t x := by
  simp_rw [tuplePairSum_shift_tsum]
  rw [lintegral_finsetSum (f := fun (ij : Fin n × Fin n) (u : Rd d) =>
    ∑' z : GridIndex d, offSiteAnchoredGaussianKernel d t
      (u + latticeOrigin d (m : ℝ) z + x ij.1, u + latticeOrigin d (m : ℝ) z + x ij.2))
    Finset.univ (fun ij _ => measurable_shiftedPair_lattice_tsum d (m : ℝ)
      (x ij.1) (x ij.2) _ (measurable_offSiteAnchoredGaussianKernel d t))]
  simp_rw [randomPhase_offSiteGaussian_lintegral d m hm t]
  simp only [tupleOffSiteGaussian, tuplePairSum, Finset.mul_sum]

theorem measurable_phaseTranslateTuple (d n : ℕ) (L : ℝ) (z : GridIndex d) :
    Measurable (fun p : Rd d × (Fin n → Rd d) =>
      Riesz.Negative.translateTuple d n (p.1 + latticeOrigin d L z) p.2) := by
  exact measurable_pi_lambda _ (fun i => (measurable_fst.add_const (latticeOrigin d L z)).add
    ((measurable_pi_apply i).comp measurable_snd))

theorem measurable_latticeTuplePairSum (d n : ℕ) (L : ℝ)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    Measurable (fun p : Rd d × (Fin n → Rd d) =>
      ∑' z : GridIndex d, tuplePairSum d n k
        (Riesz.Negative.translateTuple d n (p.1 + latticeOrigin d L z) p.2)) := by
  exact Measurable.tsum (fun z => (measurable_tuplePairSum d n k hk).comp
    (measurable_phaseTranslateTuple d n L z))

theorem latticeTuplePairSum_lintegral (d n : ℕ) (L : ℝ) (u : Rd d)
    (Qcell : Measure (Fin n → Rd d)) (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∑' z : GridIndex d, ∫⁻ x, tuplePairSum d n k
      (Riesz.Negative.translateTuple d n (u + latticeOrigin d L z) x) ∂Qcell) =
      ∫⁻ x, ∑' z : GridIndex d, tuplePairSum d n k
        (Riesz.Negative.translateTuple d n (u + latticeOrigin d L z) x) ∂Qcell := by
  exact (lintegral_tsum (fun z => ((measurable_tuplePairSum d n k hk).comp
    (Riesz.Negative.translateTuple d n (u + latticeOrigin d L z)).measurable).aemeasurable)).symm

theorem gridMarks_same_cell_pair_lintegral (d n : ℕ) (L : ℝ) (u : Rd d)
    (Qcell : Measure (Fin n → Rd d)) [IsProbabilityMeasure Qcell]
    (z : GridIndex d) (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ x : GridMarks d n, tuplePairSum d n k (gridCellTuple d n L u z x)
      ∂gridMarksLaw d n Qcell) =
      ∫⁻ x, tuplePairSum d n k
        (Riesz.Negative.translateTuple d n (u + latticeOrigin d L z) x) ∂Qcell := by
  exact (measurePreserving_eval_infinitePi (fun _ : GridIndex d => Qcell) z).lintegral_comp
    ((measurable_tuplePairSum d n k hk).comp
      (Riesz.Negative.translateTuple d n (u + latticeOrigin d L z)).measurable)

theorem measurable_tupleOffSiteGaussian (d n : ℕ) (t : ℝ) :
    Measurable (tupleOffSiteGaussian d n t) := by
  exact measurable_tuplePairSum d n _ (measurable_offSiteGaussianKernel d t)

theorem tupleOffSiteGaussian_eq_index_sum (d n : ℕ) (t : ℝ) (x : Fin n → Rd d)
    (hx : Function.Injective x) :
    tupleOffSiteGaussian d n t x = ∑ ij : Fin n × Fin n,
      if ij.1 = ij.2 then 0 else ENNReal.ofReal (Real.exp (-(t * ‖x ij.2 - x ij.1‖ ^ 2))) := by
  simp only [tupleOffSiteGaussian, tuplePairSum, offSiteGaussianKernel, hx.eq_iff]

/-- Restoring the diagonal adds exactly the number of tuple points. -/
theorem tupleGaussian_diagonal_identity (d n : ℕ) (t : ℝ) (x : Fin n → Rd d)
    (hx : Function.Injective x) :
    (∑ ij : Fin n × Fin n, ENNReal.ofReal (Real.exp (-(t * ‖x ij.2 - x ij.1‖ ^ 2)))) =
      (n : ℝ≥0∞) + tupleOffSiteGaussian d n t x := by
  have hpoint (ij : Fin n × Fin n) :
      ENNReal.ofReal (Real.exp (-(t * ‖x ij.2 - x ij.1‖ ^ 2))) =
        (if ij.1 = ij.2 then 1 else 0) + offSiteGaussianKernel d t (x ij.1, x ij.2) := by
    by_cases hij : ij.1 = ij.2 <;> simp [offSiteGaussianKernel, hx.eq_iff, hij]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, tupleOffSiteGaussian, tuplePairSum]
  simp only [Fintype.sum_prod_type]
  simp

/-- The same-cell contribution of the independent grid has exactly the
cell-volume factor times the original finite-tuple expectation. -/
theorem randomPhase_grid_sameCellGaussian (d n m : ℕ) (hm : 0 < m)
    (Qcell : Measure (Fin n → Rd d)) [IsProbabilityMeasure Qcell] (t : ℝ) :
    (∫⁻ u, ∑' z : GridIndex d, ∫⁻ x : GridMarks d n,
      tuplePairSum d n (offSiteAnchoredGaussianKernel d t)
        (gridCellTuple d n (m : ℝ) u z x)
      ∂gridMarksLaw d n Qcell ∂Riesz.Negative.cubeUniform d m) =
      ((m : ℝ≥0∞) ^ d)⁻¹ * ∫⁻ x, tupleOffSiteGaussian d n t x ∂Qcell := by
  simp_rw [gridMarks_same_cell_pair_lintegral d n (m : ℝ) _ Qcell _ _
    (measurable_offSiteAnchoredGaussianKernel d t),
    latticeTuplePairSum_lintegral d n (m : ℝ) _ Qcell _
      (measurable_offSiteAnchoredGaussianKernel d t)]
  letI := Riesz.Negative.cubeUniform_probability d m hm
  rw [lintegral_lintegral_swap ((measurable_latticeTuplePairSum d n (m : ℝ) _
    (measurable_offSiteAnchoredGaussianKernel d t)).aemeasurable)]
  simp_rw [randomPhase_tupleOffSiteGaussian d n m hm t]
  exact lintegral_const_mul _ (measurable_tupleOffSiteGaussian d n t)

end Riesz.Stationary
