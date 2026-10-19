import Mathlib.MeasureTheory.Measure.Sub

/-!
The measure-valued correction in the proof of the reverse cube comparison.
These lemmas make the fallback intensity a genuine positive measure, with
exactly the mass and mean required by the balanced finite-volume problem.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz.Negative

/-- The good-event intensity estimate used in the reverse cube argument.
`χ` is the cutoff part of the background, `u` is the expected cutoff point
measure on the good event, `p` is the good-event probability, and `z` bounds
the (possibly signed before taking its positive part) mass-correction term.
The result is a bound of positive measures, so no Radon–Nikodym density is
introduced for the fallback law. -/
theorem good_event_intensity_domination (α : Type*) [MeasurableSpace α]
    (ν χ u z : Measure α) [IsFiniteMeasure ν]
    (p c : ℝ≥0∞) (hp : p ≤ 1)
    (hχ : χ ≤ ν) (hu : u ≤ χ) (hz : z ≤ c • ν) :
    u + p • (ν - χ) + z ≤ (1 + c) • ν := by
  haveI : IsFiniteMeasure χ := isFiniteMeasure_of_le ν hχ
  have hp' : p • (ν - χ) ≤ ν - χ := by
    intro A
    simpa only [Measure.smul_apply, smul_eq_mul, one_mul] using
      (mul_le_mul_left hp ((ν - χ) A))
  calc
    u + p • (ν - χ) + z ≤ χ + (ν - χ) + c • ν :=
      add_le_add (add_le_add hu hp') hz
    _ = (1 + c) • ν := by
      rw [add_comm χ (ν - χ), Measure.sub_add_cancel_of_le hχ]
      simp only [add_smul, one_smul]

/-- The normalized good-event intensity is dominated by the desired cube
background whenever the unnormalized intensity has the paper's multiplicative
domination bound. -/
theorem scaled_good_intensity_le (α : Type*) [MeasurableSpace α]
    (ν ρ : Measure α) (t : ℝ≥0∞) (ht₀ : t ≠ 0) (ht_top : t ≠ ⊤)
    (hρ : ρ ≤ t • ν) : t⁻¹ • ρ ≤ ν := by
  intro A
  have h := hρ A
  simp only [Measure.smul_apply, smul_eq_mul] at h ⊢
  calc
    t⁻¹ * ρ A ≤ t⁻¹ * (t * ν A) := mul_le_mul_right h _
    _ = ν A := ENNReal.inv_mul_cancel_left ht₀ ht_top

/-- The correction branch is a positive measure and restores the exact
unconditional intensity. -/
theorem corrected_intensity_eq (α : Type*) [MeasurableSpace α]
    (ν ρ : Measure α) [IsFiniteMeasure ν]
    (t : ℝ≥0∞) (ht₀ : t ≠ 0) (ht_top : t ≠ ⊤)
    (hρ : ρ ≤ t • ν) :
    (ν - t⁻¹ • ρ) + t⁻¹ • ρ = ν := by
  have hle := scaled_good_intensity_le α ν ρ t ht₀ ht_top hρ
  letI : IsFiniteMeasure (t⁻¹ • ρ) := isFiniteMeasure_of_le ν hle
  exact Measure.sub_add_cancel_of_le hle

/-- The fallback law is dominated by the cube background; in particular it
cannot introduce atoms when the background is nonatomic. -/
theorem corrected_intensity_le (α : Type*) [MeasurableSpace α]
    (ν ρ : Measure α) (t : ℝ≥0∞) : ν - t⁻¹ • ρ ≤ ν :=
  Measure.sub_le

/-- The fallback mass is exactly the gap between the requested total mass and
the scaled good-event mass. -/
theorem corrected_intensity_mass (α : Type*) [MeasurableSpace α]
    (ν ρ : Measure α) [IsFiniteMeasure ν]
    (t : ℝ≥0∞) (ht₀ : t ≠ 0) (ht_top : t ≠ ⊤)
    (hρ : ρ ≤ t • ν) :
    (ν - t⁻¹ • ρ) Set.univ = ν Set.univ - t⁻¹ * ρ Set.univ := by
  have hle := scaled_good_intensity_le α ν ρ t ht₀ ht_top hρ
  letI : IsFiniteMeasure (t⁻¹ • ρ) := isFiniteMeasure_of_le ν hle
  simpa only [Measure.smul_apply, smul_eq_mul] using
    Measure.sub_apply MeasurableSet.univ hle

end Riesz.Negative
