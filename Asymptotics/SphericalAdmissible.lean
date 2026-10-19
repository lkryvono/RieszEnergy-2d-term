import Riesz.Asymptotics.SphericalFactorial
import Riesz.Asymptotics.SphericalLocalLimits

/-!
# Admissible limits of actual positive-energy spherical configurations

The ambient limit satisfies the exact class in the Showcase. Its local moments,
stationarity, intensity and simplicity follow from the original energy bound.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal Topology Classical

namespace Riesz.Asymptotics

/-- Every actual positive-energy weak limit belongs to the Showcase class. -/
theorem sphereLocalCountingProbability_limit_admissible_of_positive_energy_bound
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (henergy : ∃ L : ℝ, ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N n) s (x n) ≤ L)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto
      (fun n => sphereLocalCountingProbability d (N n)
        (sphericalRadius d (N n)) (x n).val) atTop (𝓝 Q)) :
    Admissible d (Q.toMeasure.map Subtype.val) := by
  let P : ℕ → ProbabilityMeasure (CountingConfiguration d) := fun n =>
    sphereLocalCountingProbability d (N n) (sphericalRadius d (N n)) (x n).val
  have hsfull : -2 < s := (neg_lt_zero.mpr (zero_lt_two : (0 : ℝ) < 2)).trans hs
  have hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ n : ℕ, (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(P n).toMeasure) ≤ C :=
    fun T hT => exists_sphereLocalCountingProbability_ball_second_moment_bound_of_energy_bound
      d hd s hsfull hsd hs.ne' N hN x henergy T hT
  have hsimple := sphereLocalCountingProbability_limit_ae_simple_of_positive_energy_bound
    d hd s hs hsd N hN x henergy Q hQ
  have hstationary := sphereLocalCountingProbability_limit_stationary
    d hd N hN (fun n => (x n).val) Q hQ
  have hmean := sphereLocalCountingProbability_limit_mean_eq_volume_unconditional
    d hd N hN (fun n => (x n).val) Q hQ hball
  have hsecond := countingLaw_limit_ambient_local_second_moments d P Q hQ hball
  exact ⟨Measure.isProbabilityMeasure_map
      (μ := Q.toMeasure) measurable_subtype_coe.aemeasurable,
    hsimple.2, hstationary,
    fun D hD _ => (Measure.join_apply hD).symm.trans
      (congrArg (fun ν : Measure (Rd d) => ν D) hmean), hsecond⟩

/-- Bounded positive energies yield an actual subsequence with admissible limit. -/
theorem exists_sphereLocalCountingProbability_admissible_limit_of_positive_energy_bound
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (henergy : ∃ L : ℝ, ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N n) s (x n) ≤ L) :
    ∃ (Q : ProbabilityMeasure (CountingConfiguration d)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto ((fun n => sphereLocalCountingProbability d (N n)
        (sphericalRadius d (N n)) (x n).val) ∘ φ) atTop (𝓝 Q) ∧
      Admissible d (Q.toMeasure.map Subtype.val) := by
  obtain ⟨Q, φ, hφ, hQ⟩ := exists_sphereLocalCountingProbability_tendsto_subseq
    d hd N (fun n => (x n).val)
  refine ⟨Q, φ, hφ, hQ, ?_⟩
  obtain ⟨L, hL⟩ := henergy
  apply sphereLocalCountingProbability_limit_admissible_of_positive_energy_bound
    d hd s hs hsd (N ∘ φ) (hN.comp hφ.tendsto_atTop)
    (fun n => x (φ n)) ⟨L, hφ.tendsto_atTop.eventually hL⟩ Q
  exact hQ

end Riesz.Asymptotics
