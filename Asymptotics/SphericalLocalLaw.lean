import Riesz.Geometry.NormalCoordinates
import Riesz.Configuration.Compactness
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The actual rotated spherical local law

Every point in the open north hemisphere is pulled back by the normal chart.
The finite sum retains the original labels, so no measurable relabeling or
selection of configurations is used.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical Topology

namespace Riesz.Asymptotics

/-- Counting measure of all northern rotated sites in normal coordinates. -/
def sphereLocalCounting (d N : ℕ) (R : ℝ) (x : Fin N → Sphere d)
    (U : Problem1.Orthogonal d) : Measure (Rd d) :=
  ∑ i, if Riesz.Geometry.rotateSphere d U (x i) ∈ Riesz.Geometry.northHemisphere d
    then Measure.dirac (Riesz.Geometry.normalInverse d R
      (Riesz.Geometry.rotateSphere d U (x i)).val)
    else 0

/-- The producer is jointly measurable in the input tuple and rotation. -/
theorem measurable_sphereLocalCounting (d N : ℕ) (R : ℝ) :
    Measurable (fun p : (Fin N → Sphere d) × Problem1.Orthogonal d =>
      sphereLocalCounting d N R p.1 p.2) := by
  refine Finset.measurable_fun_sum _ (fun i _ => ?_)
  have hmap : Measurable (fun p : (Fin N → Sphere d) × Problem1.Orthogonal d =>
      (p.2, p.1 i)) :=
    measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst)
  have hbase : Measurable (fun p : Problem1.Orthogonal d × Sphere d =>
      Riesz.Geometry.rotateSphere d p.1 p.2) :=
    (Riesz.Geometry.rotateSphere_joint_continuous d).measurable
  have hrot := hbase.comp hmap
  exact Measurable.ite
    ((Riesz.Geometry.northHemisphere_isOpen d).measurableSet.preimage hrot)
    (Measure.measurable_dirac.comp
      ((Riesz.Geometry.normalInverse_continuous d R).measurable.comp
        (measurable_subtype_coe.comp hrot))) measurable_const

/-- Exact Haar-averaged first mean, with every northern original label retained. -/
theorem sphereLocalCounting_mean (d N : ℕ) (R : ℝ) (x : Fin N → Sphere d)
    (A : Set (Rd d)) (hA : MeasurableSet A) :
    (∫⁻ U, sphereLocalCounting d N R x U A ∂Riesz.Geometry.uniformRotationLaw d) =
      (N : ℝ≥0∞) * Riesz.Geometry.sphericalMeasure d
        {y : Sphere d | y ∈ Riesz.Geometry.northHemisphere d ∧
          Riesz.Geometry.normalInverse d R y.val ∈ A} := by
  simp only [sphereLocalCounting, Measure.finsetSum_apply, apply_ite,
    Measure.coe_zero, ite_apply, Pi.zero_apply]
  have hsite : Measurable (fun y : Sphere d =>
      if y ∈ Riesz.Geometry.northHemisphere d then
        Measure.dirac (Riesz.Geometry.normalInverse d R y.val) A else 0) :=
    Measurable.ite (Riesz.Geometry.northHemisphere_isOpen d).measurableSet
      ((Measure.measurable_coe hA).comp (Measure.measurable_dirac.comp
        ((Riesz.Geometry.normalInverse_continuous d R).measurable.comp
          measurable_subtype_coe))) measurable_const
  rw [lintegral_finsetSum (f := fun (i : Fin N) U =>
      if Riesz.Geometry.rotateSphere d U (x i) ∈ Riesz.Geometry.northHemisphere d then
        Measure.dirac (Riesz.Geometry.normalInverse d R
          (Riesz.Geometry.rotateSphere d U (x i)).val) A else 0)
    Finset.univ (fun i _ => hsite.comp
    (Riesz.Geometry.uniformRotationLaw_measurePreserving d (x i)).measurable)]
  have heval (i : Fin N) :
      (∫⁻ U, if Riesz.Geometry.rotateSphere d U (x i) ∈ Riesz.Geometry.northHemisphere d
        then Measure.dirac (Riesz.Geometry.normalInverse d R
          (Riesz.Geometry.rotateSphere d U (x i)).val) A else 0
        ∂Riesz.Geometry.uniformRotationLaw d) =
      ∫⁻ y : Sphere d, if y ∈ Riesz.Geometry.northHemisphere d then
        Measure.dirac (Riesz.Geometry.normalInverse d R y.val) A else 0
        ∂Riesz.Geometry.sphericalMeasure d :=
    (Riesz.Geometry.uniformRotationLaw_measurePreserving d (x i)).lintegral_comp hsite
  simp only [heval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hD : MeasurableSet {y : Sphere d | y ∈ Riesz.Geometry.northHemisphere d ∧
      Riesz.Geometry.normalInverse d R y.val ∈ A} :=
    (Riesz.Geometry.northHemisphere_isOpen d).measurableSet.inter
      (hA.preimage ((Riesz.Geometry.normalInverse_continuous d R).measurable.comp
        measurable_subtype_coe))
  simpa only [Measure.dirac_apply' _ hA, Set.indicator, Pi.one_apply,
    Set.mem_setOf_eq, ← ite_and] using
    congrArg (fun t : ℝ≥0∞ => (N : ℝ≥0∞) * t)
      (lintegral_indicator_one (μ := Riesz.Geometry.sphericalMeasure d) hD)

/-- Fixing the input tuple gives a measurable counting-measure producer. -/
theorem measurable_sphereLocalCounting_fixed (d N : ℕ) (R : ℝ)
    (x : Fin N → Sphere d) : Measurable (sphereLocalCounting d N R x) := by
  have hmap : Measurable (fun U : Problem1.Orthogonal d => (x, U)) :=
    measurable_const.prodMk measurable_id
  have h := (measurable_sphereLocalCounting d N R).comp hmap
  exact h

/-- The actual Haar pushforward law on ambient counting measures. -/
def sphereLocalLaw (d N : ℕ) (R : ℝ) (x : Fin N → Sphere d) : ConfigurationLaw d :=
  (Riesz.Geometry.uniformRotationLaw d).map (sphereLocalCounting d N R x)

instance sphereLocalLaw_isProbabilityMeasure (d N : ℕ) (R : ℝ)
    (x : Fin N → Sphere d) : IsProbabilityMeasure (sphereLocalLaw d N R x) := by
  exact (Riesz.Geometry.uniformRotationLaw d).isProbabilityMeasure_map
    (measurable_sphereLocalCounting_fixed d N R x).aemeasurable

/-- The exact first mean of the actual ambient pushforward law. -/
theorem sphereLocalLaw_mean (d N : ℕ) (R : ℝ) (x : Fin N → Sphere d)
    (A : Set (Rd d)) (hA : MeasurableSet A) :
    (∫⁻ μ, μ A ∂sphereLocalLaw d N R x) =
      (N : ℝ≥0∞) * Riesz.Geometry.sphericalMeasure d
        {y : Sphere d | y ∈ Riesz.Geometry.northHemisphere d ∧
          Riesz.Geometry.normalInverse d R y.val ∈ A} := by
  simpa only [sphereLocalLaw, lintegral_map (Measure.measurable_coe hA)
    (measurable_sphereLocalCounting_fixed d N R x)] using
    sphereLocalCounting_mean d N R x A hA

/-- Original labels whose rotated points lie in the chart hemisphere. -/
abbrev SphereLocalLabels (d N : ℕ) (x : Fin N → Sphere d) (U : Problem1.Orthogonal d) :=
  {i : Fin N // Riesz.Geometry.rotateSphere d U (x i) ∈ Riesz.Geometry.northHemisphere d}

/-- The normal coordinate of a retained original label. -/
def sphereLocalSite (d N : ℕ) (R : ℝ) (x : Fin N → Sphere d)
    (U : Problem1.Orthogonal d) (i : SphereLocalLabels d N x U) : Rd d :=
  Riesz.Geometry.normalInverse d R (Riesz.Geometry.rotateSphere d U (x i.val)).val

/-- The conditional sum is exactly the sum over northern original labels. -/
theorem sphereLocalCounting_eq_sum (d N : ℕ) (R : ℝ) (x : Fin N → Sphere d)
    (U : Problem1.Orthogonal d) :
    sphereLocalCounting d N R x U =
      ∑ i : SphereLocalLabels d N x U, Measure.dirac (sphereLocalSite d N R x U i) := by
  rw [sphereLocalCounting, ← Finset.sum_filter,
    Finset.sum_subtype (p := fun i => Riesz.Geometry.rotateSphere d U (x i) ∈
      Riesz.Geometry.northHemisphere d) (F := inferInstance) _ (by simp)]
  rfl

/-- A finite tuple representation, retaining every original northern label. -/
theorem sphereLocalCounting_eq_tupleCounting (d N : ℕ) (R : ℝ)
    (x : Fin N → Sphere d) (U : Problem1.Orthogonal d) :
    sphereLocalCounting d N R x U =
      Riesz.Negative.tupleCounting d (Fintype.card (SphereLocalLabels d N x U))
        (fun j => sphereLocalSite d N R x U
          ((Fintype.equivFin (SphereLocalLabels d N x U)).symm j)) := by
  simpa only [sphereLocalCounting_eq_sum, Riesz.Negative.tupleCounting] using
    ((Fintype.equivFin (SphereLocalLabels d N x U)).symm.sum_comp
      (fun i => Measure.dirac (sphereLocalSite d N R x U i))).symm

/-- The producer is a genuine counting configuration for every input tuple. -/
theorem sphereLocalCounting_isCountingConfiguration (d N : ℕ) (R : ℝ)
    (x : Fin N → Sphere d) (U : Problem1.Orthogonal d) :
    Riesz.Configuration.IsCountingConfiguration d (sphereLocalCounting d N R x U) := by
  exact fun k => (sphereLocalCounting_eq_tupleCounting d N R x U).symm ▸
    Riesz.Configuration.finiteCountingOn_tupleCounting d _ _
      (Metric.closedBall (0 : Rd d) (k : ℝ))

/-- The actual producer in the multiplicity-aware counting-configuration space. -/
def sphereLocalConfiguration (d N : ℕ) (R : ℝ) (x : Fin N → Sphere d)
    (U : Problem1.Orthogonal d) : Riesz.Configuration.CountingConfiguration d :=
  ⟨sphereLocalCounting d N R x U,
    sphereLocalCounting_isCountingConfiguration d N R x U⟩

/-- Joint measurability of the actual lifted producer. -/
theorem measurable_sphereLocalConfiguration (d N : ℕ) (R : ℝ) :
    Measurable (fun p : (Fin N → Sphere d) × Problem1.Orthogonal d =>
      sphereLocalConfiguration d N R p.1 p.2) := by
  exact (measurable_sphereLocalCounting d N R).subtype_mk

/-- Measurability of the lifted producer for a fixed spherical tuple. -/
theorem measurable_sphereLocalConfiguration_fixed (d N : ℕ) (R : ℝ)
    (x : Fin N → Sphere d) : Measurable (sphereLocalConfiguration d N R x) := by
  exact (measurable_sphereLocalCounting_fixed d N R x).subtype_mk

/-- The actual Haar law on multiplicity-aware counting configurations. -/
def sphereLocalCountingProbability (d N : ℕ) (R : ℝ) (x : Fin N → Sphere d) :
    ProbabilityMeasure (Riesz.Configuration.CountingConfiguration d) :=
  ⟨(Riesz.Geometry.uniformRotationLaw d).map (sphereLocalConfiguration d N R x),
    (Riesz.Geometry.uniformRotationLaw d).isProbabilityMeasure_map
      (measurable_sphereLocalConfiguration_fixed d N R x).aemeasurable⟩

/-- Exact first mean on the actual counting-configuration probability space. -/
theorem sphereLocalCountingProbability_mean (d N : ℕ) (R : ℝ)
    (x : Fin N → Sphere d) (A : Set (Rd d)) (hA : MeasurableSet A) :
    (∫⁻ μ, μ.val A ∂(sphereLocalCountingProbability d N R x).toMeasure) =
      (N : ℝ≥0∞) * Riesz.Geometry.sphericalMeasure d
        {y : Sphere d | y ∈ Riesz.Geometry.northHemisphere d ∧
          Riesz.Geometry.normalInverse d R y.val ∈ A} := by
  simpa only [sphereLocalCountingProbability, ProbabilityMeasure.coe_mk,
    lintegral_map (f := fun μ : Riesz.Configuration.CountingConfiguration d => μ.val A)
      ((Measure.measurable_coe hA).comp measurable_subtype_coe)
      (measurable_sphereLocalConfiguration_fixed d N R x), sphereLocalConfiguration] using
    sphereLocalCounting_mean d N R x A hA

/-- Forgetting the counting subtype gives exactly the original ambient law. -/
theorem sphereLocalCountingProbability_map_val (d N : ℕ) (R : ℝ)
    (x : Fin N → Sphere d) :
    (sphereLocalCountingProbability d N R x).toMeasure.map Subtype.val =
      sphereLocalLaw d N R x := by
  simpa only [sphereLocalCountingProbability, ProbabilityMeasure.coe_mk,
    sphereLocalLaw, Function.comp_def, sphereLocalConfiguration] using
    (Measure.map_map (μ := Riesz.Geometry.uniformRotationLaw d)
      measurable_subtype_coe (measurable_sphereLocalConfiguration_fixed d N R x))

/-- Distinct spherical inputs remain distinct in the open normal chart. -/
theorem sphereLocalSite_injective (d N : ℕ) {R : ℝ} (hR : 0 < R)
    (x : Fin N → Sphere d) (hx : Function.Injective x) (U : Problem1.Orthogonal d) :
    Function.Injective (sphereLocalSite d N R x U) := by
  intro i j hij
  exact Subtype.ext (hx ((Riesz.Geometry.rotateSphere_isometry d U).injective
    ((Riesz.Geometry.normalPoint_normalInverse d hR i.property).symm.trans
      ((congrArg (Riesz.Geometry.normalPoint d R) hij).trans
        (Riesz.Geometry.normalPoint_normalInverse d hR j.property)))))

/-- Every rotated pullback of a distinct tuple is a simple configuration. -/
theorem sphereLocalCounting_simple (d N : ℕ) {R : ℝ} (hR : 0 < R)
    (x : Fin N → Sphere d) (hx : Function.Injective x) (U : Problem1.Orthogonal d) :
    IsSimpleConfiguration d (sphereLocalCounting d N R x U) := by
  simpa only [sphereLocalCounting_eq_tupleCounting] using
    Riesz.Negative.tupleCounting_simple d _
      (fun j => sphereLocalSite d N R x U
        ((Fintype.equivFin (SphereLocalLabels d N x U)).symm j))
      ((sphereLocalSite_injective d N hR x hx U).comp
        (Fintype.equivFin (SphereLocalLabels d N x U)).symm.injective)

/-- A distinct spherical tuple produces a law concentrated on simple configurations. -/
theorem sphereLocalCountingProbability_simple (d N : ℕ) {R : ℝ} (hR : 0 < R)
    (x : Fin N → Sphere d) (hx : Function.Injective x) :
    ∀ᵐ μ ∂(sphereLocalCountingProbability d N R x).toMeasure,
      IsSimpleConfiguration d μ.val := by
  exact (ae_map_iff (measurable_sphereLocalConfiguration_fixed d N R x).aemeasurable
    ((Riesz.Configuration.measurableSet_isSimpleConfiguration d).preimage
      measurable_subtype_coe)).mpr
    (Filter.Eventually.of_forall fun U => sphereLocalCounting_simple d N hR x hx U)

/-- A bound for the finite prefix before the asymptotic cap estimate applies. -/
theorem sphereLocalCountingProbability_mean_le_count (d N : ℕ) (R : ℝ)
    (x : Fin N → Sphere d) (A : Set (Rd d)) (hA : MeasurableSet A) :
    (∫⁻ μ, μ.val A ∂(sphereLocalCountingProbability d N R x).toMeasure) ≤ (N : ℝ≥0∞) := by
  simpa only [mul_one] using
    (sphereLocalCountingProbability_mean d N R x A hA).trans_le
      (mul_le_mul_right (prob_le_one (μ := Riesz.Geometry.sphericalMeasure d)) (N : ℝ≥0∞))

end Riesz.Asymptotics
