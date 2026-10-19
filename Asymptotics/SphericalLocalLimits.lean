import Riesz.Asymptotics.SphericalPairMoments
import Riesz.Asymptotics.SphericalLimitMoments
import Riesz.Asymptotics.SphericalTightness

/-!
# Actual spherical weak limits with finite local second moments

The moment condition is on the original ambient space of measure laws used in
the showcase. Stationarity, intensity and simplicity are separate obligations.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal Topology Classical

namespace Riesz.Asymptotics

/-- Bounded scaled energies yield an actual local-law subsequence whose limit
has the full bounded-set second-moment condition required by `Admissible`. -/
theorem exists_sphereLocalCountingProbability_limit_with_second_moments
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : -2 < s) (hsd : s < (d : ℝ)) (hsne : s ≠ 0)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (henergy : ∃ L : ℝ, ∀ᶠ n in atTop,
      scaledSphericalKernelEnergy d (N n) s (x n) ≤ L) :
    ∃ (Q : ProbabilityMeasure (CountingConfiguration d)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto ((fun n => sphereLocalCountingProbability d (N n)
        (sphericalRadius d (N n)) (x n).val) ∘ φ) atTop (𝓝 Q) ∧
      ∀ D : Set (Rd d), MeasurableSet D → Bornology.IsBounded D →
        (∫⁻ μ, (μ D) ^ 2 ∂(Q.toMeasure.map (fun μ => μ.val))) < ∞ := by
  exact (exists_sphereLocalCountingProbability_tendsto_subseq d hd N
    (fun n => (x n).val)).elim (fun Q hQ => hQ.elim (fun φ hφ =>
      ⟨Q, φ, hφ.1, hφ.2,
        countingLaw_limit_ambient_local_second_moments d _ Q hφ.2 (fun T hT =>
          (exists_sphereLocalCountingProbability_ball_second_moment_bound_of_energy_bound
            d hd s hs hsd hsne N hN x henergy T hT).elim
              (fun C hC => ⟨C, hC.1, fun n => hC.2 (φ n)⟩))⟩))

end Riesz.Asymptotics
