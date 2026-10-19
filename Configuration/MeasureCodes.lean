import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Countable evaluation codes for finite measures in the Giry measurable structure.
These results supply the separation hypothesis for measurable images of finite
configuration spaces. No topology on infinite configurations is asserted here. -/

noncomputable section

open MeasureTheory MeasurableSpace
open scoped ENNReal Classical

namespace Riesz.Configuration

/-- Finite intersections of a countable measurable generating sequence. -/
def generatingIntersection (α : Type*) [MeasurableSpace α] [CountablyGenerated α]
    (s : Finset ℕ) : Set α :=
  ⋂ i ∈ s, natGeneratingSequence α i

theorem measurableSet_generatingIntersection (α : Type*) [MeasurableSpace α]
    [CountablyGenerated α] (s : Finset ℕ) :
    MeasurableSet (generatingIntersection α s) := by
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter
    (fun _ : i ∈ s => measurableSet_natGeneratingSequence i))

theorem isPiSystem_generatingIntersection (α : Type*) [MeasurableSpace α]
    [CountablyGenerated α] : IsPiSystem (Set.range (generatingIntersection α)) := by
  rintro a ⟨s, rfl⟩ b ⟨t, rfl⟩ hne
  refine ⟨s ∪ t, ?_⟩
  ext x
  simp [generatingIntersection, or_imp, forall_and]

theorem generateFrom_generatingIntersection (α : Type*) [MeasurableSpace α]
    [CountablyGenerated α] :
    generateFrom (Set.range (generatingIntersection α)) = (inferInstance : MeasurableSpace α) := by
  apply le_antisymm
  · exact generateFrom_le (fun s ⟨t, ht⟩ => ht ▸ measurableSet_generatingIntersection α t)
  · refine (generateFrom_natGeneratingSequence α).symm.le.trans (generateFrom_mono ?_)
    rintro s ⟨i, rfl⟩
    exact ⟨{i}, by simp [generatingIntersection]⟩

/-- A countable evaluation code, including the total mass at the empty intersection. -/
def finiteMeasureCode (α : Type*) [MeasurableSpace α] [CountablyGenerated α]
    (μ : FiniteMeasure α) : Finset ℕ → ℝ≥0∞ :=
  fun s => μ.toMeasure (generatingIntersection α s)

theorem measurable_finiteMeasureCode (α : Type*) [MeasurableSpace α]
    [CountablyGenerated α] : Measurable (finiteMeasureCode α) := by
  exact measurable_pi_lambda _ (fun s =>
    (Measure.measurable_coe (measurableSet_generatingIntersection α s)).comp measurable_subtype_coe)

theorem finiteMeasureCode_injective (α : Type*) [MeasurableSpace α]
    [CountablyGenerated α] : Function.Injective (finiteMeasureCode α) := by
  intro μ ν h
  apply FiniteMeasure.toMeasure_injective
  refine ext_of_generate_finite (Set.range (generatingIntersection α))
    (generateFrom_generatingIntersection α).symm (isPiSystem_generatingIntersection α) ?_ ?_
  · rintro s ⟨t, rfl⟩
    exact congr_fun h t
  · simpa [finiteMeasureCode, generatingIntersection] using congr_fun h ∅

theorem countablySeparated_of_measurable_injective {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [CountablySeparated β]
    {f : α → β} (hf : Measurable f) (hinj : Function.Injective f) :
    CountablySeparated α := by
  obtain ⟨C, hC, hmeas, hsep⟩ :=
    exists_countable_separating β MeasurableSet Set.univ
  refine ⟨⟨⟨Set.preimage f '' C, hC.image _, ?_, ?_⟩⟩⟩
  · rintro s ⟨t, ht, rfl⟩
    exact hf (hmeas t ht)
  · intro x hx y hy hxy
    exact hinj (hsep (f x) (Set.mem_univ _) (f y) (Set.mem_univ _)
      (fun s hs => hxy (f ⁻¹' s) ⟨s, hs, rfl⟩))

/-- Finite measures are countably separated for the actual Giry measurable structure. -/
theorem countablySeparated_finiteMeasure (α : Type*) [MeasurableSpace α]
    [CountablyGenerated α] : CountablySeparated (FiniteMeasure α) := by
  exact countablySeparated_of_measurable_injective
    (measurable_finiteMeasureCode α) (finiteMeasureCode_injective α)

end Riesz.Configuration
