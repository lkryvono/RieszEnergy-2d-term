import Riesz.Stationary.GridPairs
import Riesz.Configuration.PairIntegrals

/-! Gaussian pair integrals of the random shifted grid, with the showcase's
anchor and diagonal exclusion kept throughout the calculation. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Stationary

def offSiteAnchoredGaussianKernel (d : ℕ) (t : ℝ) (p : Rd d × Rd d) : ℝ≥0∞ :=
  if p.1 = p.2 then 0 else anchoredGaussianKernel d t p

theorem measurable_offSiteAnchoredGaussianKernel (d : ℕ) (t : ℝ) :
    Measurable (offSiteAnchoredGaussianKernel d t) := by
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd)
    measurable_const (measurable_anchoredGaussianKernel d t)

theorem anchored_offSite_pair_lintegral (d : ℕ) (t : ℝ) (μ : Measure (Rd d)) :
    (∫⁻ x in cube d 1, ∫⁻ y,
      if x = y then 0 else ENNReal.ofReal (Real.exp (-t * ‖y - x‖ ^ 2)) ∂μ ∂μ) =
      ∫⁻ x, ∫⁻ y, offSiteAnchoredGaussianKernel d t (x, y) ∂μ ∂μ := by
  rw [← lintegral_indicator (Riesz.Negative.measurableSet_cube d 1)]
  refine lintegral_congr (fun x => ?_)
  by_cases hx : x ∈ cube d 1 <;>
    simp [offSiteAnchoredGaussianKernel, anchoredGaussianKernel, hx, neg_mul]

theorem gridConfiguration_pair_lintegral (d n : ℕ) (L : ℝ) (u : Rd d)
    (x : GridMarks d n) (k : Rd d × Rd d → ℝ≥0∞) :
    (∫⁻ a, ∫⁻ b, k (a, b) ∂gridConfiguration d n L u x
      ∂gridConfiguration d n L u x) =
      ∑' a : GridIndex d × Fin n, ∑' b : GridIndex d × Fin n,
        k (gridSites d n L u x a, gridSites d n L u x b) := by
  simp only [gridConfiguration, lintegral_sum_measure, lintegral_dirac]

theorem measurable_grid_pair_tsum (d n : ℕ) (L : ℝ)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    Measurable (fun p : Rd d × GridMarks d n =>
      ∑' a : GridIndex d × Fin n, ∑' b : GridIndex d × Fin n,
        k (gridSites d n L p.1 p.2 a, gridSites d n L p.1 p.2 b)) := by
  exact Measurable.tsum (fun a => Measurable.tsum (fun b => hk.comp
    ((measurable_gridSites d n L a).prodMk (measurable_gridSites d n L b))))

theorem grid_pair_tsum_eq_cell_pairs (d n : ℕ) (L : ℝ) (u : Rd d)
    (x : GridMarks d n) (k : Rd d × Rd d → ℝ≥0∞) :
    (∑' a : GridIndex d × Fin n, ∑' b : GridIndex d × Fin n,
      k (gridSites d n L u x a, gridSites d n L u x b)) =
      ∑' z : GridIndex d, ∑' w : GridIndex d, ∑ ij : Fin n × Fin n,
        k (gridCellTuple d n L u z x ij.1, gridCellTuple d n L u w x ij.2) := by
  simp only [ENNReal.tsum_prod']
  refine tsum_congr (fun z => ?_)
  rw [ENNReal.tsum_comm]
  simp only [tsum_fintype, Fintype.sum_prod_type]
  rfl

theorem measurable_gridCellPairSum (d n : ℕ) (L : ℝ) (u : Rd d)
    (z w : GridIndex d) (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    Measurable (fun x : GridMarks d n => ∑ ij : Fin n × Fin n,
      k (gridCellTuple d n L u z x ij.1, gridCellTuple d n L u w x ij.2)) := by
  have hsum : Measurable (fun x : GridMarks d n => ∑' ij : Fin n × Fin n,
      k (gridCellTuple d n L u z x ij.1, gridCellTuple d n L u w x ij.2)) :=
    Measurable.tsum (fun ij => hk.comp
      (((measurable_pi_apply ij.1).comp (measurable_gridCellTuple d n L u z)).prodMk
        ((measurable_pi_apply ij.2).comp (measurable_gridCellTuple d n L u w))))
  simpa only [tsum_fintype] using hsum

theorem grid_pair_marks_lintegral (d n : ℕ) (L : ℝ) (u : Rd d)
    (Qcell : Measure (Fin n → Rd d))
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ x : GridMarks d n,
      ∑' a : GridIndex d × Fin n, ∑' b : GridIndex d × Fin n,
        k (gridSites d n L u x a, gridSites d n L u x b) ∂gridMarksLaw d n Qcell) =
      ∑' z : GridIndex d, ∑' w : GridIndex d, ∫⁻ x : GridMarks d n,
        ∑ ij : Fin n × Fin n,
          k (gridCellTuple d n L u z x ij.1, gridCellTuple d n L u w x ij.2)
        ∂gridMarksLaw d n Qcell := by
  simp_rw [grid_pair_tsum_eq_cell_pairs]
  rw [lintegral_tsum (fun z => (Measurable.tsum (fun w =>
    measurable_gridCellPairSum d n L u z w k hk)).aemeasurable)]
  exact tsum_congr (fun z => lintegral_tsum (fun w =>
    (measurable_gridCellPairSum d n L u z w k hk).aemeasurable))

/-- Pull the actual showcase pair functional back to the phase and independent marks. -/
theorem Q_randomShiftGridLaw_lintegral (d m : ℕ) (hm : 0 < m)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) (t : ℝ) :
    Q d (randomShiftGridLaw d m Qcell) t =
      ∫⁻ p : Rd d × GridMarks d (m ^ d),
        ∑' a : GridIndex d × Fin (m ^ d), ∑' b : GridIndex d × Fin (m ^ d),
          offSiteAnchoredGaussianKernel d t
            (gridSites d (m ^ d) (m : ℝ) p.1 p.2 a,
              gridSites d (m ^ d) (m : ℝ) p.1 p.2 b)
        ∂(Riesz.Negative.cubeUniform d m).prod (gridMarksLaw d (m ^ d) Qcell) := by
  simp_rw [Q, anchored_offSite_pair_lintegral]
  rw [randomShiftGridLaw, lintegral_map'
    (Riesz.Configuration.aemeasurable_pair_lintegral_of_simple d _
      (randomShiftGridLaw_ae_simple d m hm Qcell hQ) _
      (measurable_offSiteAnchoredGaussianKernel d t))
    (measurable_gridConfiguration d (m ^ d) (m : ℝ)).aemeasurable]
  simp_rw [gridConfiguration_pair_lintegral]

/-- The showcase pair functional as an iterated phase and marks expectation. -/
theorem Q_randomShiftGridLaw_phase_marks (d m : ℕ) (hm : 0 < m)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) (t : ℝ) :
    Q d (randomShiftGridLaw d m Qcell) t =
      ∫⁻ u, ∫⁻ x : GridMarks d (m ^ d),
        ∑' a : GridIndex d × Fin (m ^ d), ∑' b : GridIndex d × Fin (m ^ d),
          offSiteAnchoredGaussianKernel d t
            (gridSites d (m ^ d) (m : ℝ) u x a, gridSites d (m ^ d) (m : ℝ) u x b)
        ∂gridMarksLaw d (m ^ d) Qcell ∂Riesz.Negative.cubeUniform d m := by
  letI : IsProbabilityMeasure Qcell := hQ.1
  letI := gridMarksLaw_probability d (m ^ d) Qcell
  letI := Riesz.Negative.cubeUniform_probability d m hm
  rw [Q_randomShiftGridLaw_lintegral d m hm Qcell hQ t,
    lintegral_prod _ ((measurable_grid_pair_tsum d (m ^ d) (m : ℝ) _
      (measurable_offSiteAnchoredGaussianKernel d t)).aemeasurable)]

theorem Q_randomShiftGridLaw_cell_pairs (d m : ℕ) (hm : 0 < m)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) (t : ℝ) :
    Q d (randomShiftGridLaw d m Qcell) t =
      ∫⁻ u, ∑' z : GridIndex d, ∑' w : GridIndex d, ∫⁻ x : GridMarks d (m ^ d),
        ∑ ij : Fin (m ^ d) × Fin (m ^ d),
          offSiteAnchoredGaussianKernel d t
            (gridCellTuple d (m ^ d) (m : ℝ) u z x ij.1,
              gridCellTuple d (m ^ d) (m : ℝ) u w x ij.2)
        ∂gridMarksLaw d (m ^ d) Qcell ∂Riesz.Negative.cubeUniform d m := by
  rw [Q_randomShiftGridLaw_phase_marks d m hm Qcell hQ t]
  simp_rw [grid_pair_marks_lintegral d (m ^ d) (m : ℝ) _ Qcell _
    (measurable_offSiteAnchoredGaussianKernel d t)]

/-- Distinct-cell expectations in the actual showcase functional equal the
background product integrals; only the same-cell term retains correlations. -/
theorem Q_randomShiftGridLaw_cell_split (d m : ℕ) (hm : 0 < m)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) (t : ℝ) :
    Q d (randomShiftGridLaw d m Qcell) t =
      ∫⁻ u, ∑' z : GridIndex d, ∑' w : GridIndex d,
        if z = w then
          ∫⁻ x : GridMarks d (m ^ d), ∑ ij : Fin (m ^ d) × Fin (m ^ d),
            offSiteAnchoredGaussianKernel d t
              (gridCellTuple d (m ^ d) (m : ℝ) u z x ij.1,
                gridCellTuple d (m ^ d) (m : ℝ) u w x ij.2)
            ∂gridMarksLaw d (m ^ d) Qcell
        else ∫⁻ p, anchoredGaussianKernel d t p
          ∂(volume.restrict (latticeCell d (m : ℝ) u z)).prod
            (volume.restrict (latticeCell d (m : ℝ) u w))
        ∂Riesz.Negative.cubeUniform d m := by
  rw [Q_randomShiftGridLaw_cell_pairs d m hm Qcell hQ t]
  refine lintegral_congr (fun u => tsum_congr (fun z => tsum_congr (fun w => ?_)))
  by_cases hzw : z = w
  case neg =>
    simpa only [if_neg hzw, offSiteAnchoredGaussianKernel] using
      gridMarks_cross_cell_offSite_gaussian d m hm u Qcell hQ z w hzw t
  case pos => simp only [if_pos hzw]

end Riesz.Stationary
