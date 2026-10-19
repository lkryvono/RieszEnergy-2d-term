import Riesz.Geometry.SphereFromProblem1
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Uniform rotations and their exact spherical marginals

The orthogonal Haar probability is reused from Problem 1. These adapters give
its right invariance and the law of every rotated point on the Showcase sphere.
Identification with chart area and normal-coordinate estimates are separate.
-/

noncomputable section

open MeasureTheory RieszShowcase

namespace Riesz.Geometry

theorem orthogonalHaar_map_mul_right (m : ℕ) (U : Problem1.OrthogonalN m) :
    (Problem1.orthogonalHaar m).map (fun R => R * U) = Problem1.orthogonalHaar m := by
  letI : IsProbabilityMeasure ((Problem1.orthogonalHaar m).map (fun R => R * U)) :=
    (Problem1.orthogonalHaar m).isProbabilityMeasure_map
      (measurable_mul_const U).aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Every sphere point has the north-pole orbit law under a uniform rotation. -/
theorem orthogonalHaar_map_sphereActionN (m : ℕ) (hm : 1 ≤ m)
    (x : Problem1.UnitSphereN m) :
    (Problem1.orthogonalHaar m).map (fun U => Problem1.sphereActionN U x) =
      Problem1.sigmaGeneric m hm := by
  obtain ⟨U, hU⟩ := Problem1.orthogonal_north_transitive m hm x
  have hcompose : (fun R => Problem1.sphereActionN R x) =
      Problem1.orbitMap m hm ∘ (fun R => R * U) := by
    funext R
    simp only [Function.comp_apply, Problem1.orbitMap_apply,
      Problem1.sphereActionN_mul, hU]
  rw [hcompose, ← Measure.map_map (Problem1.orbitMap_measurable m hm)
    (measurable_mul_const U), orthogonalHaar_map_mul_right]
  rfl

/-- The uniform orthogonal rotation law, normalized to total mass one. -/
def uniformRotationLaw (d : ℕ) : Measure (Problem1.Orthogonal d) :=
  Problem1.orthogonalHaar (d + 1)

instance uniformRotationLaw_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (uniformRotationLaw d) :=
  Problem1.orthogonalHaarIsProbabilityMeasure (d + 1)

theorem uniformRotationLaw_map_mul_left (d : ℕ) (U : Problem1.Orthogonal d) :
    (uniformRotationLaw d).map (fun R => U * R) = uniformRotationLaw d := by
  exact Problem1.orthogonalHaar_map_mul_left U

theorem uniformRotationLaw_map_mul_right (d : ℕ) (U : Problem1.Orthogonal d) :
    (uniformRotationLaw d).map (fun R => R * U) = uniformRotationLaw d := by
  exact orthogonalHaar_map_mul_right (d + 1) U

/-- Orthogonal action on the exact sphere subtype used in the Showcase. -/
def rotateSphere (d : ℕ) (U : Problem1.Orthogonal d) (x : Sphere d) : Sphere d :=
  (problem1SphereIsometryEquiv d).symm
    (Problem1.sphereAction U (problem1SphereIsometryEquiv d x))

theorem rotateSphere_joint_continuous (d : ℕ) :
    Continuous (fun p : Problem1.Orthogonal d × Sphere d =>
      rotateSphere d p.1 p.2) := by
  unfold rotateSphere
  apply (problem1SphereIsometryEquiv d).symm.continuous.comp
  change Continuous ((fun p : Problem1.OrthogonalN (d + 1) ×
      Problem1.UnitSphereN (d + 1) => Problem1.sphereActionN p.1 p.2) ∘
    fun p : Problem1.Orthogonal d × Sphere d =>
      (p.1, problem1SphereIsometryEquiv d p.2))
  apply (Problem1.sphereActionN_joint_continuous (d + 1)).comp
  exact continuous_fst.prodMk
    ((problem1SphereIsometryEquiv d).continuous.comp continuous_snd)

theorem rotateSphere_isometry (d : ℕ) (U : Problem1.Orthogonal d) :
    Isometry (rotateSphere d U) := by
  exact (problem1SphereIsometryEquiv d).symm.isometry.comp
    ((Problem1.sphereActionN_isometry U).comp (problem1SphereIsometryEquiv d).isometry)

theorem rotateSphere_one (d : ℕ) (x : Sphere d) : rotateSphere d 1 x = x := by
  simp only [rotateSphere, Problem1.sphereAction, Problem1.sphereActionN_one,
    IsometryEquiv.symm_apply_apply]

theorem rotateSphere_mul (d : ℕ) (U V : Problem1.Orthogonal d) (x : Sphere d) :
    rotateSphere d (U * V) x = rotateSphere d U (rotateSphere d V x) := by
  simp only [rotateSphere, Problem1.sphereAction, Problem1.sphereActionN_mul,
    IsometryEquiv.apply_symm_apply]

theorem rotateSphere_chord (d : ℕ) (U : Problem1.Orthogonal d) (x y : Sphere d) :
    chord d (rotateSphere d U x) (rotateSphere d U y) = chord d x y := by
  simpa only [chord, Subtype.dist_eq, dist_eq_norm] using
    (rotateSphere_isometry d U).dist_eq x y

/-- A uniform rotation sends each fixed point to the exact invariant sphere law. -/
theorem uniformRotationLaw_map_rotateSphere (d : ℕ) (x : Sphere d) :
    (uniformRotationLaw d).map (fun U => rotateSphere d U x) = sphericalMeasure d := by
  change (Problem1.orthogonalHaar (d + 1)).map
    ((problem1SphereIsometryEquiv d).symm ∘
      fun U => Problem1.sphereActionN U (problem1SphereIsometryEquiv d x)) =
    (Problem1.sigma d).map (problem1SphereIsometryEquiv d).symm
  have hmeas : Measurable (fun U : Problem1.Orthogonal d =>
      Problem1.sphereActionN U (problem1SphereIsometryEquiv d x)) :=
    ((Problem1.sphereActionN_joint_continuous (d + 1)).comp
      (continuous_id.prodMk continuous_const)).measurable
  rw [← Measure.map_map (problem1SphereIsometryEquiv d).symm.continuous.measurable hmeas,
    orthogonalHaar_map_sphereActionN (d + 1) (Nat.succ_pos d)]
  rfl

/-- The evaluator at any fixed point preserves the exact probability measures. -/
theorem uniformRotationLaw_measurePreserving (d : ℕ) (x : Sphere d) :
    MeasurePreserving (fun U => rotateSphere d U x)
      (uniformRotationLaw d) (sphericalMeasure d) := by
  refine ⟨?_, uniformRotationLaw_map_rotateSphere d x⟩
  exact ((rotateSphere_joint_continuous d).comp
    (continuous_id.prodMk continuous_const)).measurable

end Riesz.Geometry
