import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Weak convergence of finite products, for compactly supported pair tests. -/

noncomputable section

open MeasureTheory Filter TopologicalSpace
open scoped Topology NNReal

namespace Riesz.Configuration

theorem finiteMeasure_prod_smul
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (a b : ℝ≥0) (μ : FiniteMeasure X) (ν : FiniteMeasure Y) :
    (a • μ).prod (b • ν) = (a * b) • (μ.prod ν) := by
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.toMeasure_prod, FiniteMeasure.toMeasure_smul,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, mul_comm]

theorem finiteMeasure_prod_eq_mass_smul_normalize
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Nonempty X] [Nonempty Y] (μ : FiniteMeasure X) (ν : FiniteMeasure Y) :
    μ.prod ν = (μ.mass * ν.mass) • (μ.normalize.prod ν.normalize).toFiniteMeasure := by
  exact (congrArg₂ FiniteMeasure.prod μ.self_eq_mass_smul_normalize
    ν.self_eq_mass_smul_normalize).trans
      (finiteMeasure_prod_smul μ.mass ν.mass μ.normalize.toFiniteMeasure ν.normalize.toFiniteMeasure)

/-- Finite product measures converge weakly, including zero limit factors. -/
theorem tendsto_finiteMeasure_prod
    {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Nonempty X] [Nonempty Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {l : Filter ι} {u : ι → FiniteMeasure X} {v : ι → FiniteMeasure Y}
    {μ : FiniteMeasure X} {ν : FiniteMeasure Y}
    (hu : Tendsto u l (𝓝 μ)) (hv : Tendsto v l (𝓝 ν)) :
    Tendsto (fun i => (u i).prod (v i)) l (𝓝 (μ.prod ν)) := by
  by_cases hμ : μ ≠ 0
  · by_cases hν : ν ≠ 0
    · have hp : Tendsto
          (fun i => ((u i).normalize.prod (v i).normalize).toFiniteMeasure) l
          (𝓝 (μ.normalize.prod ν.normalize).toFiniteMeasure) := by
        simpa only [Function.comp_def] using
          (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto _).comp
          ((ProbabilityMeasure.continuous_prod.tendsto (μ.normalize, ν.normalize)).comp
            ((FiniteMeasure.tendsto_normalize_of_tendsto hu hμ).prodMk_nhds
              (FiniteMeasure.tendsto_normalize_of_tendsto hv hν)))
      simpa only [← finiteMeasure_prod_eq_mass_smul_normalize] using (hu.mass.mul hv.mass).smul hp
    · have hmass : Tendsto (fun i => ((u i).prod (v i)).mass) l (𝓝 0) := by
        simpa only [FiniteMeasure.mass_prod, not_ne_iff.mp hν,
          FiniteMeasure.zero_mass, mul_zero] using hu.mass.mul hv.mass
      simpa only [not_ne_iff.mp hν, FiniteMeasure.prod_zero] using
        FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass
  · have hmass : Tendsto (fun i => ((u i).prod (v i)).mass) l (𝓝 0) := by
      simpa only [FiniteMeasure.mass_prod, not_ne_iff.mp hμ,
        FiniteMeasure.zero_mass, zero_mul] using hu.mass.mul hv.mass
    simpa only [not_ne_iff.mp hμ, FiniteMeasure.zero_prod] using
      FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass

/-- The product of finite measures depends continuously on both factors. -/
theorem continuous_finiteMeasure_prod
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Nonempty X] [Nonempty Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y] :
    Continuous (fun p : FiniteMeasure X × FiniteMeasure Y => p.1.prod p.2) := by
  exact continuous_iff_continuousAt.mpr fun p =>
    tendsto_finiteMeasure_prod (continuous_fst.tendsto p) (continuous_snd.tendsto p)

end Riesz.Configuration
