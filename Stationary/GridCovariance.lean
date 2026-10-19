import Riesz.Stationary.GridBackgroundGaussian
import Riesz.Analysis.ENNRealDiagonal

/-! Exact Gaussian covariance balance for the independently filled grid.
The identity first exchanges nonnegative same-cell contributions, so no
subtraction of infinite pair sums is used. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Stationary

def gaussianCellBackground (d : ℕ) (L t : ℝ) (u : Rd d) (z w : GridIndex d) : ℝ≥0∞ :=
  ∫⁻ p, anchoredGaussianKernel d t p ∂(volume.restrict (latticeCell d L u z)).prod
    (volume.restrict (latticeCell d L u w))

def gaussianSameCellPairs (d n : ℕ) (L : ℝ) (Qcell : Measure (Fin n → Rd d))
    (t : ℝ) (u : Rd d) (z : GridIndex d) : ℝ≥0∞ :=
  ∫⁻ x : GridMarks d n, tuplePairSum d n (offSiteAnchoredGaussianKernel d t)
    (gridCellTuple d n L u z x) ∂gridMarksLaw d n Qcell

theorem measurable_gaussianCellBackground (d : ℕ) (L t : ℝ) (z w : GridIndex d) :
    Measurable (fun u : Rd d => gaussianCellBackground d L t u z w) := by
  exact measurable_cellBackgroundPairIntegral d L z w _ (measurable_anchoredGaussianKernel d t)

theorem measurable_gaussianSameCellPairs (d n : ℕ) (L : ℝ)
    (Qcell : Measure (Fin n → Rd d)) [IsProbabilityMeasure Qcell]
    (t : ℝ) (z : GridIndex d) :
    Measurable (fun u : Rd d => gaussianSameCellPairs d n L Qcell t u z) := by
  exact measurable_gridSameCellPairMean d n L Qcell z _
    (measurable_offSiteAnchoredGaussianKernel d t)

theorem Q_randomShiftGridLaw_cell_replaced (d m : ℕ) (hm : 0 < m)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) (t : ℝ) :
    Q d (randomShiftGridLaw d m Qcell) t =
      ∫⁻ u, ∑' z : GridIndex d, ∑' w : GridIndex d,
        if z = w then gaussianSameCellPairs d (m ^ d) (m : ℝ) Qcell t u z
        else gaussianCellBackground d (m : ℝ) t u z w ∂Riesz.Negative.cubeUniform d m := by
  rw [Q_randomShiftGridLaw_cell_split d m hm Qcell hQ t]
  refine lintegral_congr (fun u => tsum_congr (fun z => tsum_congr (fun w => ?_)))
  by_cases hzw : z = w <;>
    simp only [hzw, if_true, if_false, gaussianSameCellPairs, gaussianCellBackground, tuplePairSum]

theorem Q_randomShiftGridLaw_background_balance (d m : ℕ) (hm : 0 < m)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) (t : ℝ) :
    Q d (randomShiftGridLaw d m Qcell) t +
        (∫⁻ u, ∑' z : GridIndex d, gaussianCellBackground d (m : ℝ) t u z z
          ∂Riesz.Negative.cubeUniform d m) =
      (∫⁻ u, ∑' z : GridIndex d, ∑' w : GridIndex d,
        gaussianCellBackground d (m : ℝ) t u z w ∂Riesz.Negative.cubeUniform d m) +
      ∫⁻ u, ∑' z : GridIndex d, gaussianSameCellPairs d (m ^ d) (m : ℝ) Qcell t u z
        ∂Riesz.Negative.cubeUniform d m := by
  letI : IsProbabilityMeasure Qcell := hQ.1
  rw [Q_randomShiftGridLaw_cell_replaced d m hm Qcell hQ t]
  have hdiag : Measurable (fun u : Rd d =>
      ∑' z : GridIndex d, gaussianCellBackground d (m : ℝ) t u z z) :=
    Measurable.tsum (fun z => measurable_gaussianCellBackground d (m : ℝ) t z z)
  have hsame : Measurable (fun u : Rd d =>
      ∑' z : GridIndex d, gaussianSameCellPairs d (m ^ d) (m : ℝ) Qcell t u z) :=
    Measurable.tsum (fun z => measurable_gaussianSameCellPairs d (m ^ d) (m : ℝ) Qcell t z)
  rw [← lintegral_add_right _ hdiag, ← lintegral_add_right _ hsame]
  refine lintegral_congr (fun u => ?_)
  convert Riesz.Analysis.ennreal_tsum_diagonal_balance
    (GridIndex d) (fun z => gaussianSameCellPairs d (m ^ d) (m : ℝ) Qcell t u z)
      (fun z w => gaussianCellBackground d (m : ℝ) t u z w) using 1
  congr 4
  exact funext (fun z => tsum_congr (fun w => (ite_eq_ite (z = w) _ _).2 trivial))

/-- The exact showcase pair functional differs from the Gaussian background
only by the original finite cell's pair contribution. -/
theorem Q_randomShiftGridLaw_gaussian_balance (d m : ℕ) (hm : 0 < m)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) (t : ℝ) (ht : 0 < t) :
    Q d (randomShiftGridLaw d m Qcell) t +
        ((m : ℝ≥0∞) ^ d)⁻¹ * (∫⁻ p, gaussianPairKernel d t p
          ∂(volume.restrict (cube d (m : ℝ))).prod (volume.restrict (cube d (m : ℝ)))) =
      ENNReal.ofReal (B d t) +
        ((m : ℝ≥0∞) ^ d)⁻¹ * ∫⁻ x, tupleOffSiteGaussian d (m ^ d) t x ∂Qcell := by
  have h := Q_randomShiftGridLaw_background_balance d m hm Qcell hQ t
  letI : IsProbabilityMeasure Qcell := hQ.1
  letI := Riesz.Negative.cubeUniform_probability d m hm
  simp only [gaussianCellBackground, gaussianSameCellPairs] at h
  rw [randomPhase_sameCellBackgroundGaussian d m hm t,
    randomPhase_grid_sameCellGaussian d (m ^ d) m hm Qcell t] at h
  simp_rw [lattice_anchoredGaussian_sum d (m : ℝ) (Nat.cast_pos.mpr hm) _ t ht] at h
  simpa only [lintegral_const, measure_univ, mul_one] using h

theorem gaussianPairKernel_le_one (d : ℕ) (t : ℝ) (ht : 0 ≤ t) (p : Rd d × Rd d) :
    gaussianPairKernel d t p ≤ 1 := by
  exact (ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg ht (sq_nonneg _))))).trans_eq ENNReal.ofReal_one

theorem tuplePairSum_gaussian_le (d n : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Fin n → Rd d) :
    tuplePairSum d n (gaussianPairKernel d t) x ≤ (n : ℝ≥0∞) ^ 2 := by
  have h : tuplePairSum d n (gaussianPairKernel d t) x ≤
      ∑ _ij : Fin n × Fin n, (1 : ℝ≥0∞) :=
    Finset.sum_le_sum (fun ij _ => gaussianPairKernel_le_one d t ht (x ij.1, x ij.2))
  simpa [pow_two] using h

theorem tupleOffSiteGaussian_le (d n : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Fin n → Rd d) :
    tupleOffSiteGaussian d n t x ≤ (n : ℝ≥0∞) ^ 2 := by
  apply le_trans ?_ (tuplePairSum_gaussian_le d n t ht x)
  unfold tupleOffSiteGaussian tuplePairSum
  refine Finset.sum_le_sum (fun ij _ => ?_)
  by_cases hij : x ij.1 = x ij.2 <;>
    simp [offSiteGaussianKernel, gaussianPairKernel, hij]

theorem cubeGaussian_lintegral_ne_top (d m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ p, gaussianPairKernel d t p
      ∂(volume.restrict (cube d (m : ℝ))).prod (volume.restrict (cube d (m : ℝ)))) ≠ ∞ := by
  letI := Riesz.Negative.cube_background_isFiniteMeasure d m
  exact ((lintegral_mono (fun p => gaussianPairKernel_le_one d t ht p)).trans_lt
    (lintegral_const_lt_top ENNReal.one_ne_top)).ne

theorem tupleOffSiteGaussian_lintegral_ne_top (d n : ℕ)
    (Qcell : Measure (Fin n → Rd d)) [IsProbabilityMeasure Qcell] (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x, tupleOffSiteGaussian d n t x ∂Qcell) ≠ ∞ := by
  exact ne_top_of_le_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n))
    (lintegral_le_const (ae_of_all Qcell (fun x => tupleOffSiteGaussian_le d n t ht x)))

theorem tupleGaussian_expected_diagonal (d n : ℕ)
    (Qcell : Measure (Fin n → Rd d)) [IsProbabilityMeasure Qcell] (t : ℝ)
    (hQ : ∀ᵐ x ∂Qcell, Function.Injective x) :
    (∫⁻ x, tuplePairSum d n (gaussianPairKernel d t) x ∂Qcell) =
      (n : ℝ≥0∞) + ∫⁻ x, tupleOffSiteGaussian d n t x ∂Qcell := by
  have hdiag : ∀ᵐ x ∂Qcell, tuplePairSum d n (gaussianPairKernel d t) x =
      (n : ℝ≥0∞) + tupleOffSiteGaussian d n t x :=
    hQ.mono (fun x hx => tupleGaussian_diagonal_identity d n t x hx)
  rw [lintegral_congr_ae hdiag,
    lintegral_add_right _ (measurable_tupleOffSiteGaussian d n t),
    lintegral_const, measure_univ, mul_one]

theorem Q_randomShiftGridLaw_ne_top (d m : ℕ) (hm : 0 < m)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) (t : ℝ) (ht : 0 < t) :
    Q d (randomShiftGridLaw d m Qcell) t ≠ ∞ := by
  letI : IsProbabilityMeasure Qcell := hQ.1
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (B d t) +
      ((m : ℝ≥0∞) ^ d)⁻¹ * ∫⁻ x, tupleOffSiteGaussian d (m ^ d) t x ∂Qcell)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (Nat.cast_ne_zero.mpr hm.ne')))
      (tupleOffSiteGaussian_lintegral_ne_top d (m ^ d) Qcell t ht.le)⟩) ?_
  exact (le_add_right le_rfl).trans
    (Q_randomShiftGridLaw_gaussian_balance d m hm Qcell hQ t ht).le

/-- The paper's real covariance profile `1 + Q - B`, for the actual showcase law.
The finite-cell diagonal gives the term `1` after dividing by the cell volume. -/
theorem Q_randomShiftGridLaw_real_covariance (d m : ℕ) (hm : 0 < m)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) (t : ℝ) (ht : 0 < t) :
    (Q d (randomShiftGridLaw d m Qcell) t).toReal + 1 - B d t =
      ((m : ℝ) ^ d)⁻¹ *
        ((∫⁻ x, tuplePairSum d (m ^ d) (gaussianPairKernel d t) x ∂Qcell).toReal -
          (∫⁻ p, gaussianPairKernel d t p
            ∂(volume.restrict (cube d (m : ℝ))).prod
              (volume.restrict (cube d (m : ℝ)))).toReal) := by
  have h := congrArg ENNReal.toReal (Q_randomShiftGridLaw_gaussian_balance d m hm Qcell hQ t ht)
  letI : IsProbabilityMeasure Qcell := hQ.1
  have hf : ((m : ℝ≥0∞) ^ d)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (pow_ne_zero _ (Nat.cast_ne_zero.mpr hm.ne'))
  rw [ENNReal.toReal_add (Q_randomShiftGridLaw_ne_top d m hm Qcell hQ t ht)
      (ENNReal.mul_ne_top hf (cubeGaussian_lintegral_ne_top d m t ht.le)),
    ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top hf (tupleOffSiteGaussian_lintegral_ne_top d (m ^ d) Qcell t ht.le))] at h
  have hB : 0 ≤ B d t := (Real.rpow_pos_of_pos (div_pos Real.pi_pos ht) _).le
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hB] at h
  rw [tupleGaussian_expected_diagonal d (m ^ d) Qcell t
      (hQ.2.1.mono (fun _ hx => hx.1)),
    ENNReal.toReal_add (ENNReal.natCast_ne_top _)
      (tupleOffSiteGaussian_lintegral_ne_top d (m ^ d) Qcell t ht.le),
    ENNReal.toReal_natCast, Nat.cast_pow, mul_sub, mul_add,
    inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hm.ne'))]
  linarith

end Riesz.Stationary
