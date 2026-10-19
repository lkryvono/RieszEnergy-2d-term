import Riesz.Negative.ExactCount
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Sampling a single finite continuous piece by a weighted random atom. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

/-- An atom carrying the total mass of a finite cell measure. -/
def cellSampleAtom (d : ℕ) (ν : FiniteMeasure (Rd d)) (y : Rd d) : Measure (Rd d) :=
  (ν.mass : ℝ≥0∞) • Measure.dirac y

instance cellSampleAtom_isFiniteMeasure (d : ℕ) (ν : FiniteMeasure (Rd d)) (y : Rd d) :
    IsFiniteMeasure (cellSampleAtom d ν y) := by
  dsimp [cellSampleAtom]
  infer_instance

/-- Sampling from the normalized cell measure preserves its full measure mean. -/
theorem cellSampleAtom_mean (d : ℕ) (ν : FiniteMeasure (Rd d))
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ y, (cellSampleAtom d ν y) D ∂(ν.normalize : Measure (Rd d))) = ν D := by
  calc
    _ = (ν.mass : ℝ≥0∞) * (ν.normalize : Measure (Rd d)) D := by
      simp only [cellSampleAtom, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply' _ hD]
      rw [lintegral_const_mul' _ _ (by simp),
        lintegral_indicator_one hD]
    _ = ν D := by
      have h := congrArg (fun a : NNReal => (a : ENNReal))
        (ν.self_eq_mass_mul_normalize D)
      simpa only [ENNReal.coe_mul,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using h.symm

/-- Scalar test-function form of the cell sampling mean identity. -/
theorem cellSampleLaw_integral (d : ℕ) (ν : FiniteMeasure (Rd d))
    (f : Rd d → ℝ) :
    (∫ y, (ν.mass : ℝ) * f y ∂(ν.normalize : Measure (Rd d))) =
      ∫ y, f y ∂(ν : Measure (Rd d)) := by
  calc
    _ = (ν.mass : ℝ) * ∫ y, f y ∂(ν.normalize : Measure (Rd d)) :=
      integral_const_mul _ _
    _ = ∫ y, f y ∂((ν.mass : NNReal) • (ν.normalize : Measure (Rd d))) := by
      rw [integral_smul_nnreal_measure]
      rfl
    _ = _ := by
      congr 1
      exact (congrArg (fun μ : FiniteMeasure (Rd d) => (μ : Measure (Rd d)))
        ν.self_eq_mass_smul_normalize).symm

/-- A nonzero diffuse cell measure gives a diffuse sampling law. -/
theorem cellSampleLaw_nullSingleton (d : ℕ) (ν : FiniteMeasure (Rd d))
    (hν : ν ≠ 0) (hatom : ∀ y : Rd d, ν {y} = 0) :
    NullSingletonClass (ν.normalize : Measure (Rd d)) := by
  refine ⟨fun y => ?_⟩
  rw [← ν.normalize.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [ν.normalize_eq_of_nonzero hν]
  simp [hatom y]

/-- Sampling a diffuse cell avoids every pre-existing finite set of sites. -/
theorem cellSampleLaw_avoids_finite (d : ℕ) (ν : FiniteMeasure (Rd d))
    (hν : ν ≠ 0) (hatom : ∀ y : Rd d, ν {y} = 0)
    (S : Finset (Rd d)) :
    ∀ᵐ y ∂(ν.normalize : Measure (Rd d)), y ∉ S := by
  letI := cellSampleLaw_nullSingleton d ν hν hatom
  exact S.finite_toSet.countable.ae_notMem _

/-- A sampled site stays in any measurable carrier of the cell measure. -/
theorem cellSampleLaw_supported (d : ℕ) (ν : FiniteMeasure (Rd d))
    (hν : ν ≠ 0) (B : Set (Rd d))
    (hsupport : ν Bᶜ = 0) :
    ∀ᵐ y ∂(ν.normalize : Measure (Rd d)), y ∈ B := by
  rw [ae_iff]
  change (ν.normalize : Measure (Rd d)) Bᶜ = 0
  rw [← ν.normalize.ennreal_coeFn_eq_coeFn_toMeasure,
    ν.normalize_eq_of_nonzero hν]
  simp [hsupport]

/-- The signed discrepancy created by replacing a cell measure with one atom. -/
def cellSampleIncrement (d : ℕ) (ν : FiniteMeasure (Rd d)) (y : Rd d) :
    SignedMeasure (Rd d) :=
  (cellSampleAtom d ν y).toSignedMeasure - (ν : Measure (Rd d)).toSignedMeasure

/-- Every sampled-cell discrepancy has zero total mass, pathwise. -/
theorem cellSampleIncrement_mass_zero (d : ℕ) (ν : FiniteMeasure (Rd d))
    (y : Rd d) : cellSampleIncrement d ν y Set.univ = 0 := by
  have h₁ : cellSampleAtom d ν y Set.univ = (ν.mass : ℝ≥0∞) := by
    simp [cellSampleAtom, Measure.smul_apply]
  have h₂ : (ν : Measure (Rd d)) Set.univ = (ν.mass : ℝ≥0∞) := by
    rw [← ν.ennreal_coeFn_eq_coeFn_toMeasure]
    rfl
  simp only [cellSampleIncrement, Measure.toSignedMeasure_sub_apply MeasurableSet.univ,
    measureReal_def, h₁, h₂, sub_self]

/-- Diffuseness makes the sampled atom and its original cell measure the
Jordan parts of the one-cell discrepancy. -/
theorem cellSampleIncrement_jordan_parts (d : ℕ) (ν : FiniteMeasure (Rd d))
    (hatom : ∀ y : Rd d, ν {y} = 0) (y : Rd d) :
    (cellSampleIncrement d ν y).toJordanDecomposition.posPart = cellSampleAtom d ν y ∧
    (cellSampleIncrement d ν y).toJordanDecomposition.negPart =
      (ν : Measure (Rd d)) := by
  letI : NullSingletonClass (ν : Measure (Rd d)) := ⟨fun z => by
    rw [← ν.ennreal_coeFn_eq_coeFn_toMeasure]
    simp [hatom z]⟩
  let J : JordanDecomposition (Rd d) :=
    ⟨cellSampleAtom d ν y, (ν : Measure (Rd d)),
      (mutuallySingular_dirac y (ν : Measure (Rd d))).smul (ν.mass : ℝ≥0∞)⟩
  exact ⟨congrArg JordanDecomposition.posPart
      (JordanDecomposition.toJordanDecomposition_toSignedMeasure J),
    congrArg JordanDecomposition.negPart
      (JordanDecomposition.toJordanDecomposition_toSignedMeasure J)⟩

theorem cellSampleIncrement_totalVariation (d : ℕ) (ν : FiniteMeasure (Rd d))
    (hatom : ∀ y : Rd d, ν {y} = 0) (y : Rd d) :
    (cellSampleIncrement d ν y).totalVariation =
      cellSampleAtom d ν y + (ν : Measure (Rd d)) := by
  obtain ⟨hpos, hneg⟩ := cellSampleIncrement_jordan_parts d ν hatom y
  simp only [SignedMeasure.totalVariation, hpos, hneg]

theorem cellSampleIncrement_totalVariation_mass (d : ℕ) (ν : FiniteMeasure (Rd d))
    (hatom : ∀ y : Rd d, ν {y} = 0) (y : Rd d) :
    (cellSampleIncrement d ν y).totalVariation Set.univ =
      2 * (ν.mass : ℝ≥0∞) := by
  rw [cellSampleIncrement_totalVariation d ν hatom y]
  rw [Measure.add_apply]
  have h₁ : cellSampleAtom d ν y Set.univ = (ν.mass : ℝ≥0∞) := by
    simp [cellSampleAtom, Measure.smul_apply]
  have h₂ : (ν : Measure (Rd d)) Set.univ = (ν.mass : ℝ≥0∞) := by
    rw [← ν.ennreal_coeFn_eq_coeFn_toMeasure]
    rfl
  rw [h₁, h₂, two_mul]

/-- If the cell measure and sampled site lie in one region, so does the
variation of the signed sampling discrepancy. -/
theorem cellSampleIncrement_concentrated (d : ℕ) (ν : FiniteMeasure (Rd d))
    (hatom : ∀ y : Rd d, ν {y} = 0)
    (B : Set (Rd d)) (hsupport : ν Bᶜ = 0)
    (y : Rd d) (hy : y ∈ B) :
    (cellSampleIncrement d ν y).totalVariation Bᶜ = 0 := by
  rw [cellSampleIncrement_totalVariation d ν hatom y, Measure.add_apply]
  have h₁ : cellSampleAtom d ν y Bᶜ = 0 := by
    simp [cellSampleAtom, Measure.smul_apply, hy]
  have h₂ : (ν : Measure (Rd d)) Bᶜ = 0 := by
    rw [← ν.ennreal_coeFn_eq_coeFn_toMeasure]
    simp [hsupport]
  rw [h₁, h₂, add_zero]

/-- A single sampled cell has signed discrepancy cost of quadratic order in
its mass. This is the bound needed for the first stage of dyadic sampling. -/
theorem cellSampleIncrement_energy_le (d : ℕ) (ν : FiniteMeasure (Rd d))
    (hatom : ∀ y : Rd d, ν {y} = 0)
    (q L : ℝ) (hq : 0 < q) (hL : 0 ≤ L)
    (B : Set (Rd d)) (hsupport : ν Bᶜ = 0)
    (hdiam : ∀ x ∈ B, ∀ z ∈ B, ‖x - z‖ ≤ L)
    (y : Rd d) (hy : y ∈ B) :
    Riesz.Analysis.signedDiscrepancyEnergy q (cellSampleIncrement d ν y) ≤
      L ^ q * (2 * (ν.mass : ℝ)) ^ 2 / q := by
  have hvariation :
      (cellSampleIncrement d ν y).totalVariation.real Set.univ =
        2 * (ν.mass : ℝ) := by
    have hmass : (ν.mass : ℝ≥0∞).toReal = (ν.mass : ℝ) := by rfl
    rw [measureReal_def, cellSampleIncrement_totalVariation_mass d ν hatom y,
      ENNReal.toReal_mul, hmass]
    norm_num
  rw [← hvariation]
  exact Riesz.Analysis.signedDiscrepancyEnergy_le q L hq hL
    (cellSampleIncrement d ν y) B
    (cellSampleIncrement_concentrated d ν hatom B hsupport y hy) hdiam

/-- The complete one-cell replacement statement used before finite rounding:
the weighted sample preserves the cell measure, avoids old sites, remains in
the cell, has zero-mass discrepancy, and costs quadratic order in cell mass. -/
theorem cell_sampling_step (d : ℕ) (ν : FiniteMeasure (Rd d))
    (hν : ν ≠ 0) (hatom : ∀ y : Rd d, ν {y} = 0)
    (q L : ℝ) (hq : 0 < q) (hL : 0 ≤ L)
    (B : Set (Rd d)) (hsupport : ν Bᶜ = 0)
    (hdiam : ∀ x ∈ B, ∀ z ∈ B, ‖x - z‖ ≤ L)
    (S : Finset (Rd d)) :
    (∀ D : Set (Rd d), MeasurableSet D →
      (∫⁻ y, (cellSampleAtom d ν y) D
        ∂(ν.normalize : Measure (Rd d))) = ν D) ∧
    (∀ᵐ y ∂(ν.normalize : Measure (Rd d)),
      y ∈ B ∧ y ∉ S ∧
      cellSampleIncrement d ν y Set.univ = 0 ∧
      Riesz.Analysis.signedDiscrepancyEnergy q (cellSampleIncrement d ν y) ≤
        L ^ q * (2 * (ν.mass : ℝ)) ^ 2 / q) := by
  refine ⟨fun D hD => cellSampleAtom_mean d ν D hD, ?_⟩
  filter_upwards [cellSampleLaw_supported d ν hν B hsupport,
    cellSampleLaw_avoids_finite d ν hν hatom S] with y hy hS
  exact ⟨hy, hS, cellSampleIncrement_mass_zero d ν y,
    cellSampleIncrement_energy_le d ν hatom q L hq hL B hsupport hdiam y hy⟩

end Riesz.Negative
