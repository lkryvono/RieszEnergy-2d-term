import Riesz.Configuration.CompactContainment
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Sequences

/-! Tightness from first moments of the existing compact mass cutoffs. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal NNReal Topology Classical CompactlySupported

namespace Riesz.Configuration

/-- Uniform finite first moments of compact mass cutoffs give tightness. -/
theorem isTightMeasureSet_of_countingMassCutoff_lintegral_le (d : ℕ)
    (S : Set (Measure (CountingConfiguration d))) (C : ℕ → ℝ≥0∞)
    (hC : ∀ j, C j ≠ ∞)
    (hmom : ∀ P ∈ S, ∀ j,
      ∫⁻ μ, ENNReal.ofReal (∫ x, countingMassCutoff d j x ∂μ.val) ∂P ≤ C j) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_tsum_mul_lt_of_countable hε.ne' C hC
  refine ⟨{μ : CountingConfiguration d |
    ∀ j, ∫ x, countingMassCutoff d j x ∂μ.val ≤ ((δ j)⁻¹ : ℝ≥0)},
    isCompact_countingMassCutoff_le d _, ?_⟩
  intro P hP
  have hfail : ∀ j, P {μ : CountingConfiguration d |
      ((δ j)⁻¹ : ℝ≥0) < ∫ x, countingMassCutoff d j x ∂μ.val} ≤ C j * δ j := by
    intro j
    have hmark := meas_ge_le_lintegral_div (μ := P)
      (measurable_countingIntegral d (countingMassCutoff d j)).ennreal_ofReal.aemeasurable
      (ε := ((δ j)⁻¹ : ℝ≥0)) (by exact_mod_cast inv_ne_zero (hδ j).ne')
      ENNReal.coe_ne_top
    have hratio : (∫⁻ μ, ENNReal.ofReal (∫ x, countingMassCutoff d j x ∂μ.val) ∂P) /
        (((δ j)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ C j * δ j := by
      simpa only [ENNReal.coe_inv (hδ j).ne', div_eq_mul_inv, inv_inv] using
        ENNReal.div_le_div (hmom P hP j) (le_refl (((δ j)⁻¹ : ℝ≥0) : ℝ≥0∞))
    apply (measure_mono ?_).trans (hmark.trans hratio)
    intro μ hμ
    simpa only [Set.mem_setOf_eq, ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hμ.le
  apply (measure_mono (t := ⋃ j, {μ : CountingConfiguration d |
    ((δ j)⁻¹ : ℝ≥0) < ∫ x, countingMassCutoff d j x ∂μ.val}) ?_).trans
    ((measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum hfail).trans hsum.le))
  simp only [Set.compl_setOf, not_forall, not_le, Set.setOf_exists, Set.Subset.rfl]

/-- Uniform cutoff first moments give a weakly convergent subsequence of probability laws. -/
theorem exists_tendsto_subseq_of_countingMassCutoff_lintegral_le (d : ℕ)
    (P : ℕ → ProbabilityMeasure (CountingConfiguration d)) (C : ℕ → ℝ≥0∞)
    (hC : ∀ j, C j ≠ ∞)
    (hmom : ∀ n j,
      ∫⁻ μ, ENNReal.ofReal (∫ x, countingMassCutoff d j x ∂μ.val) ∂(P n).toMeasure ≤ C j) :
    ∃ (Q : ProbabilityMeasure (CountingConfiguration d)) (φ : ℕ → ℕ),
      StrictMono φ ∧ Filter.Tendsto (P ∘ φ) Filter.atTop (𝓝 Q) := by
  have htight : IsTightMeasureSet
      {((Q : ProbabilityMeasure (CountingConfiguration d)) : Measure (CountingConfiguration d)) |
        Q ∈ Set.range P} := by
    apply isTightMeasureSet_of_countingMassCutoff_lintegral_le d _ C hC
    rintro _ ⟨Q, ⟨n, rfl⟩, rfl⟩ j
    exact hmom n j
  obtain ⟨Q, _, φ, hφ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
      (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨Q, φ, hφ, hlim⟩

end Riesz.Configuration
