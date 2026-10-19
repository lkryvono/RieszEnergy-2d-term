import Mathlib.Probability.Kernel.Representation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Jointly measurable sampling of finite measures on a fixed uniform space.
The zero-mass branch uses Mathlib's normalization convention. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace Riesz.Configuration

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem measurable_finiteMeasure_mass :
    Measurable (fun μ : FiniteMeasure Y => μ.mass) := by
  exact ENNReal.measurable_toNNReal.comp
    ((Measure.measurable_coe MeasurableSet.univ).comp measurable_subtype_coe)

variable [Nonempty Y]

theorem finiteMeasure_normalize_apply (μ : FiniteMeasure Y) (D : Set Y) :
    (μ.normalize : Measure Y) D =
      if μ.mass = 0 then Measure.dirac (Nonempty.some ‹Nonempty Y›) D
      else (μ.mass⁻¹ : NNReal) • (μ : Measure Y) D := by
  by_cases hmass : μ.mass = 0
  all_goals simp [FiniteMeasure.normalize, hmass, Measure.nnreal_smul_coe_apply]

theorem measurable_finiteMeasure_normalize :
    Measurable (fun μ : FiniteMeasure Y => (μ.normalize : Measure Y)) := by
  refine Measure.measurable_of_measurable_coe _ (fun D hD => ?_)
  simp only [finiteMeasure_normalize_apply]
  exact measurable_const.ite
    (measurable_finiteMeasure_mass (measurableSet_singleton 0))
    (measurable_finiteMeasure_mass.inv.smul
      ((Measure.measurable_coe hD).comp measurable_subtype_coe))

/-- The normalization of a measurable finite-measure family is a Markov kernel. -/
def normalizedFiniteKernel (ν : X → FiniteMeasure Y) (hν : Measurable ν) : Kernel X Y where
  toFun a := ((ν a).normalize : Measure Y)
  measurable' := measurable_finiteMeasure_normalize.comp hν

instance normalizedFiniteKernel_isMarkov (ν : X → FiniteMeasure Y) (hν : Measurable ν) :
    IsMarkovKernel (normalizedFiniteKernel ν hν) where
  isProbabilityMeasure a := inferInstanceAs (IsProbabilityMeasure ((ν a).normalize : Measure Y))

variable [StandardBorelSpace Y]

/-- One uniform coordinate samples a finite measure after normalization, jointly
measurably in every measurable parameter, including the zero-mass branch. -/
theorem exists_jointly_measurable_finiteMeasure_sampler
    (ν : X → FiniteMeasure Y) (hν : Measurable ν) :
    ∃ f : X → unitInterval → Y, Measurable (Function.uncurry f) ∧
      ∀ a, Measure.map (f a) volume = ((ν a).normalize : Measure Y) := by
  exact (normalizedFiniteKernel ν hν).exists_measurable_map_eq_unitInterval

/-- A universal sampler; its argument is the finite measure itself. -/
def sampleFiniteMeasure (ν : FiniteMeasure Y) (u : unitInterval) : Y :=
  (exists_jointly_measurable_finiteMeasure_sampler (id : FiniteMeasure Y → FiniteMeasure Y)
    measurable_id).choose ν u

theorem measurable_sampleFiniteMeasure :
    Measurable (Function.uncurry (sampleFiniteMeasure (Y := Y))) := by
  exact (exists_jointly_measurable_finiteMeasure_sampler
    (id : FiniteMeasure Y → FiniteMeasure Y) measurable_id).choose_spec.1

theorem sampleFiniteMeasure_map (ν : FiniteMeasure Y) :
    Measure.map (sampleFiniteMeasure ν) volume = (ν.normalize : Measure Y) := by
  exact (exists_jointly_measurable_finiteMeasure_sampler
    (id : FiniteMeasure Y → FiniteMeasure Y) measurable_id).choose_spec.2 ν

theorem measurable_sampleFiniteMeasure_fixed (ν : FiniteMeasure Y) :
    Measurable (sampleFiniteMeasure ν) := by
  exact measurable_sampleFiniteMeasure.comp (measurable_const.prodMk measurable_id)

theorem measurePreserving_sampleFiniteMeasure (ν : FiniteMeasure Y) :
    MeasurePreserving (sampleFiniteMeasure ν) volume (ν.normalize : Measure Y) := by
  exact ⟨measurable_sampleFiniteMeasure_fixed ν, sampleFiniteMeasure_map ν⟩

end Riesz.Configuration
