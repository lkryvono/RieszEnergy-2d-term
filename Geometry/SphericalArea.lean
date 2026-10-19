import Riesz.Geometry.RotationsFromProblem1
import Riesz.Asymptotics.Assembly
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Riesz.Geometry.NormalCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Cone area and the exact invariant sphere measure

The area measure from ambient Lebesgue measure is identified with the existing
Haar sphere law, so explicit upper-bound charts use the original normalization.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal NNReal Topology Pointwise

namespace Riesz.Geometry

/-- Haar averaging fixes every finite rotation-invariant sphere measure. -/
theorem eq_smul_sphericalMeasure_of_map_rotateSphere_eq
    (d : ℕ) (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (hinv : ∀ U : Problem1.Orthogonal d, ν.map (rotateSphere d U) = ν) :
    ν = ν Set.univ • sphericalMeasure d := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hrot (U : Problem1.Orthogonal d) : Measurable (rotateSphere d U) :=
    ((rotateSphere_joint_continuous d).comp (continuous_const.prodMk continuous_id)).measurable
  have hfixed (U : Problem1.Orthogonal d) :
      (∫⁻ x, f (rotateSphere d U x) ∂ν) = ∫⁻ x, f x ∂ν :=
    (lintegral_map hf (hrot U)).symm.trans (congrArg (fun μ => ∫⁻ x, f x ∂μ) (hinv U))
  have horbit (x : Sphere d) :
      (∫⁻ U, f (rotateSphere d U x) ∂uniformRotationLaw d) = ∫⁻ y, f y ∂sphericalMeasure d :=
    (uniformRotationLaw_measurePreserving d x).lintegral_comp hf
  have hjoint : Measurable (fun p : Problem1.Orthogonal d × Sphere d =>
      f (rotateSphere d p.1 p.2)) := hf.comp (rotateSphere_joint_continuous d).measurable
  have hswap : (∫⁻ U, ∫⁻ x, f (rotateSphere d U x) ∂ν ∂uniformRotationLaw d) =
      ∫⁻ x, ∫⁻ U, f (rotateSphere d U x) ∂uniformRotationLaw d ∂ν :=
    lintegral_lintegral_swap hjoint.aemeasurable
  simp only [hfixed, horbit, lintegral_const, measure_univ, mul_one] at hswap
  simpa only [lintegral_smul_measure, smul_eq_mul, mul_comm] using hswap

/-- The existing orthogonal map, bundled with its Euclidean isometry property. -/
def orthogonalAmbientIsometry (d : ℕ) (U : Problem1.Orthogonal d) :
    Rd (d + 1) ≃ₗᵢ[ℝ] Rd (d + 1) :=
  (show Rd (d + 1) →ₗᵢ[ℝ] Rd (d + 1) from
    { toLinearMap := Problem1.orthogonalLin U
      norm_map' := Problem1.orthogonalLin_norm U }).toLinearIsometryEquiv rfl

theorem orthogonal_cone_preimage (d : ℕ) (U : Problem1.Orthogonal d)
    (s : Set (Problem1.Sphere d)) :
    (orthogonalAmbientIsometry d U) ⁻¹'
        (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (Problem1.sphereAction U ⁻¹' s)) := by
  let L := orthogonalAmbientIsometry d U
  ext y
  constructor
  · intro hy
    rcases Set.mem_smul.mp hy with ⟨r, hr, z, hz, heq⟩
    rcases hz with ⟨x, hx, rfl⟩
    refine Set.mem_smul.mpr ⟨r, hr,
      (Problem1.sphereAction U⁻¹ x : Rd (d + 1)), ?_, ?_⟩
    · exact ⟨Problem1.sphereAction U⁻¹ x,
        by simpa only [Set.mem_preimage, Problem1.sphereAction,
          Problem1.sphereActionN_inv_right] using hx, rfl⟩
    · apply L.injective
      rw [map_smul]
      change r • (Problem1.sphereAction U (Problem1.sphereAction U⁻¹ x) : Rd (d + 1)) = L y
      simpa only [Problem1.sphereAction, Problem1.sphereActionN_inv_right] using heq
  · intro hy
    rcases Set.mem_smul.mp hy with ⟨r, hr, z, ⟨x, hx, rfl⟩, heq⟩
    refine Set.mem_smul.mpr ⟨r, hr, (Problem1.sphereAction U x : Rd (d + 1)),
      ⟨Problem1.sphereAction U x, hx, rfl⟩, ?_⟩
    change r • L (x : Rd (d + 1)) = L y
    rw [← map_smul, heq]

theorem toSphere_map_sphereAction (d : ℕ) (U : Problem1.Orthogonal d) :
    ((volume : Measure (Rd (d + 1))).toSphere).map (Problem1.sphereAction U) =
      (volume : Measure (Rd (d + 1))).toSphere := by
  have hact : Measurable (Problem1.sphereAction U) :=
    (Problem1.sphereActionN_continuous U).measurable
  ext s hs
  rw [Measure.map_apply hact hs, Measure.toSphere_apply' _ (hact hs),
    Measure.toSphere_apply' _ hs, ← orthogonal_cone_preimage d U s]
  exact congrArg (fun t : ℝ≥0∞ => (Module.finrank ℝ (Rd (d + 1)) : ℝ≥0∞) * t)
    ((orthogonalAmbientIsometry d U).measurePreserving.measure_preimage_emb
      (orthogonalAmbientIsometry d U).toHomeomorph.measurableEmbedding _)

theorem unitSphere_toSphere_mass (d : ℕ) :
    (volume : Measure (Rd (d + 1))).toSphere Set.univ = ENNReal.ofReal (omega d) := by
  have hn : 0 < ((d : ℝ) + 1) / 2 := by positivity
  have hscalar : ((d + 1 : ℕ) : ℝ) *
      (Real.sqrt Real.pi ^ (d + 1) / Real.Gamma (((d + 1 : ℕ) : ℝ) / 2 + 1)) = omega d := by
    rw [← Real.rpow_natCast (Real.sqrt Real.pi) (d + 1),
      ← Real.rpow_div_two_eq_sqrt (((d + 1 : ℕ) : ℝ)) Real.pi_nonneg]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Real.Gamma_add_one hn.ne']
    unfold omega
    field_simp [(Real.Gamma_pos_of_pos hn).ne', hn.ne']
  rw [Measure.toSphere_apply_univ, EuclideanSpace.volume_ball]
  simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [← ENNReal.ofReal_natCast (d + 1), ← ENNReal.ofReal_mul (Nat.cast_nonneg (d + 1)), hscalar]

/-- Cone area agrees with the original Haar sphere law and its exact omega factor. -/
theorem unitSphere_toSphere_map_eq (d : ℕ) :
    ((volume : Measure (Rd (d + 1))).toSphere).map
        (problem1SphereIsometryEquiv d).symm =
      ENNReal.ofReal (omega d) • sphericalMeasure d := by
  let ν := ((volume : Measure (Rd (d + 1))).toSphere).map
    (problem1SphereIsometryEquiv d).symm
  have hinv : ∀ U : Problem1.Orthogonal d, ν.map (rotateSphere d U) = ν := by
    intro U
    have hconj : rotateSphere d U ∘ (problem1SphereIsometryEquiv d).symm =
        (problem1SphereIsometryEquiv d).symm ∘ Problem1.sphereAction U := by
      funext x
      simp only [Function.comp_apply, rotateSphere, IsometryEquiv.apply_symm_apply]
    dsimp only [ν]
    rw [Measure.map_map (rotateSphere_isometry d U).continuous.measurable
      (problem1SphereIsometryEquiv d).symm.continuous.measurable, hconj,
      ← Measure.map_map (problem1SphereIsometryEquiv d).symm.continuous.measurable
        (Problem1.sphereActionN_continuous U).measurable, toSphere_map_sphereAction]
  have hmass : ν Set.univ = ENNReal.ofReal (omega d) := by
    dsimp only [ν]
    rw [Measure.map_apply (problem1SphereIsometryEquiv d).symm.continuous.measurable
      MeasurableSet.univ, Set.preimage_univ, unitSphere_toSphere_mass]
  exact (eq_smul_sphericalMeasure_of_map_rotateSphere_eq d ν hinv).trans
    (congrArg (fun c : ℝ≥0∞ => c • sphericalMeasure d) hmass)

/-- The existing tail coordinate map as a continuous linear map. -/
def equalAreaTailCLM (k : ℕ) : Rd (k + 1) →L[ℝ] Rd k := by
  refine {
    toFun := euclideanTail k
    map_add' := ?_
    map_smul' := ?_
    cont := euclideanTail_continuous k }
  all_goals intros
  all_goals ext i
  all_goals simp [euclideanTail]

/-- The linear tangent inclusion at the north pole. -/
def equalAreaTangent (d : ℕ) : Rd d →ₗᵢ[ℝ] Rd (d + 1) := by
  refine {
    toFun := euclideanCons d 0
    map_add' := ?_
    map_smul' := ?_
    norm_map' := by
      intro x
      change ‖euclideanCons d 0 x‖ = ‖x‖
      nlinarith [euclideanCons_norm_sq d 0 x, norm_nonneg (euclideanCons d 0 x), norm_nonneg x] }
  all_goals intros
  all_goals ext i
  all_goals refine Fin.cases ?_ (fun j => ?_) i
  all_goals simp [euclideanCons]

@[simp]
theorem equalAreaTangent_proj_head (d : ℕ) :
    (PiLp.proj 2 (fun _ : Fin (d + 1) => ℝ) 0).comp
      (equalAreaTangent d).toContinuousLinearMap = 0 := by
  ext x
  simp [equalAreaTangent, euclideanCons]

@[simp]
theorem equalAreaTangent_proj_tail (d : ℕ) (i : Fin d) :
    (PiLp.proj 2 (fun _ : Fin (d + 1) => ℝ) i.succ).comp
      (equalAreaTangent d).toContinuousLinearMap = PiLp.proj 2 (fun _ : Fin d => ℝ) i := by
  ext x
  simp [equalAreaTangent, euclideanCons]

/-- The transverse radius in the explicit equal-area chart. -/
def equalAreaCapAmplitude (k : ℕ) (x : Rd (k + 1)) : ℝ :=
  Real.sqrt (1 - ‖euclideanTail k x‖ ^ 2)

/-- Equal-area cylindrical coordinates, with angle in coordinate zero. -/
def equalAreaCapVector (k : ℕ) (x : Rd (k + 1)) : Rd (k + 2) :=
  euclideanCons (k + 1) (equalAreaCapAmplitude k x * Real.cos (x 0))
    (euclideanCons k (equalAreaCapAmplitude k x * Real.sin (x 0)) (euclideanTail k x))

/-- The explicit chart has the Euclidean tangent inclusion as derivative at zero. -/
theorem equalAreaCapVector_hasFDerivAt_zero (k : ℕ) :
    HasFDerivAt (equalAreaCapVector k)
      (equalAreaTangent (k + 1)).toContinuousLinearMap 0 := by
  have hu : HasFDerivAt (euclideanTail k) (equalAreaTailCLM k) 0 :=
    (equalAreaTailCLM k).hasFDerivAt
  have hsq : HasFDerivAt (fun x : Rd (k + 1) => ‖euclideanTail k x‖ ^ 2)
      (0 : Rd (k + 1) →L[ℝ] ℝ) 0 := by
    simpa [show euclideanTail k (0 : Rd (k + 1)) = 0 from rfl] using hu.norm_sq
  have hr : HasFDerivAt (fun x : Rd (k + 1) => 1 - ‖euclideanTail k x‖ ^ 2)
      (0 : Rd (k + 1) →L[ℝ] ℝ) 0 := by simpa using hsq.const_sub (1 : ℝ)
  have ha : HasFDerivAt (equalAreaCapAmplitude k) (0 : Rd (k + 1) →L[ℝ] ℝ) 0 := by
    simpa [equalAreaCapAmplitude] using!
      hr.sqrt (by simp [show euclideanTail k (0 : Rd (k + 1)) = 0 from rfl])
  have hv : HasFDerivAt (fun x : Rd (k + 1) => x 0)
      (PiLp.proj 2 (fun _ : Fin (k + 1) => ℝ) 0) 0 :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (0 : Rd (k + 1)) 0
  have hc : HasFDerivAt
      (fun x : Rd (k + 1) => equalAreaCapAmplitude k x * Real.cos (x 0))
      (0 : Rd (k + 1) →L[ℝ] ℝ) 0 := by
    simpa [equalAreaCapAmplitude,
      show euclideanTail k (0 : Rd (k + 1)) = 0 from rfl] using! ha.mul hv.cos
  have hs : HasFDerivAt
      (fun x : Rd (k + 1) => equalAreaCapAmplitude k x * Real.sin (x 0))
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 1) => ℝ) 0) 0 := by
    simpa [equalAreaCapAmplitude,
      show euclideanTail k (0 : Rd (k + 1)) = 0 from rfl] using! ha.mul hv.sin
  rw [← hasFDerivWithinAt_univ]
  apply (hasFDerivWithinAt_piLp 2).2
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [equalAreaCapVector, euclideanCons] using! hc.hasFDerivWithinAt (s := Set.univ)
  · refine Fin.cases ?_ (fun l => ?_) j
    · simpa [equalAreaCapVector, euclideanCons] using! hs.hasFDerivWithinAt (s := Set.univ)
    · simpa [equalAreaCapVector, euclideanCons, euclideanTail] using!
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (0 : Rd (k + 1)) l.succ).hasFDerivWithinAt
          (s := Set.univ)

/-- The cylindrical chart lands on the unit sphere. -/
theorem equalAreaCapVector_norm_sq (k : ℕ) (x : Rd (k + 1))
    (hx : ‖euclideanTail k x‖ < 1) : ‖equalAreaCapVector k x‖ ^ 2 = 1 := by
  have hs : ‖euclideanTail k x‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg (euclideanTail k x)]
  have ha : equalAreaCapAmplitude k x ^ 2 = 1 - ‖euclideanTail k x‖ ^ 2 :=
    Real.sq_sqrt (by linarith)
  rw [equalAreaCapVector, euclideanCons_norm_sq, euclideanCons_norm_sq]
  nlinarith [Real.cos_sq_add_sin_sq (x 0)]

theorem equalAreaCapVector_norm (k : ℕ) (x : Rd (k + 1))
    (hx : ‖euclideanTail k x‖ < 1) : ‖equalAreaCapVector k x‖ = 1 := by
  nlinarith [equalAreaCapVector_norm_sq k x hx, norm_nonneg (equalAreaCapVector k x)]

/-- Smoothness holds throughout the transverse unit cylinder. -/
theorem equalAreaCapVector_contDiffAt (k : ℕ) (n : WithTop ℕ∞)
    {x : Rd (k + 1)} (hx : ‖euclideanTail k x‖ < 1) :
    ContDiffAt ℝ n (equalAreaCapVector k) x := by
  have hu : ContDiffAt ℝ n (euclideanTail k) x :=
    (equalAreaTailCLM k).contDiff.contDiffAt
  have hv : ContDiffAt ℝ n (fun y : Rd (k + 1) => y 0) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 1) => ℝ) 0).contDiff.contDiffAt
  have hsq : ‖euclideanTail k x‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg (euclideanTail k x)]
  have hr : ContDiffAt ℝ n (fun y : Rd (k + 1) => 1 - ‖euclideanTail k y‖ ^ 2) x :=
    contDiffAt_const.sub (hu.norm_sq ℝ)
  have ha : ContDiffAt ℝ n (equalAreaCapAmplitude k) x :=
    hr.sqrt (ne_of_gt (by linarith))
  apply (contDiffAt_piLp 2).2
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [equalAreaCapVector, euclideanCons] using ha.mul hv.cos
  · refine Fin.cases ?_ (fun l => ?_) j
    · simpa [equalAreaCapVector, euclideanCons] using ha.mul hv.sin
    · simpa [equalAreaCapVector, euclideanCons, euclideanTail] using
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 1) => ℝ) l.succ).contDiff.contDiffAt :
          ContDiffAt ℝ n (fun y : Rd (k + 1) => y l.succ) x)

/-- Arbitrarily small relative chord distortion near the north pole. -/
theorem exists_equalAreaCapVector_relative_distortion (k : ℕ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 / 2 ∧
      ∀ x ∈ Metric.ball (0 : Rd (k + 1)) rho,
        ∀ y ∈ Metric.ball (0 : Rd (k + 1)) rho,
          (1 - epsilon) * ‖x - y‖ ≤
              ‖equalAreaCapVector k x - equalAreaCapVector k y‖ ∧
          ‖equalAreaCapVector k x - equalAreaCapVector k y‖ ≤
              (1 + epsilon) * ‖x - y‖ := by
  let T : Rd (k + 1) →L[ℝ] Rd (k + 2) :=
    (equalAreaTangent (k + 1)).toContinuousLinearMap
  let E : Rd (k + 1) → Rd (k + 2) := fun x => equalAreaCapVector k x - T x
  have hphi : ContDiffAt ℝ 1 (equalAreaCapVector k) 0 :=
    equalAreaCapVector_contDiffAt k 1
      (by simp [show euclideanTail k (0 : Rd (k + 1)) = 0 from rfl])
  have hE : ContDiffAt ℝ 1 E 0 := hphi.sub T.contDiff.contDiffAt
  have hD : HasFDerivAt E (0 : Rd (k + 1) →L[ℝ] Rd (k + 2)) 0 := by
    simpa only [E, T, sub_self] using!
      (equalAreaCapVector_hasFDerivAt_zero k).sub T.hasFDerivAt
  have hDzero : fderiv ℝ E 0 = 0 := hD.fderiv
  have hc := (hE.continuousAt_fderiv (by norm_num)).norm
  have hb : ∀ᶠ x in 𝓝 (0 : Rd (k + 1)), ‖fderiv ℝ E x‖ < epsilon :=
    hc.eventually (gt_mem_nhds (by simpa [hDzero] using hepsilon))
  have hd : ∀ᶠ x in 𝓝 (0 : Rd (k + 1)), DifferentiableAt ℝ E x :=
    (hE.eventually (by norm_num)).mono fun x hx => hx.differentiableAt_one
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hd.and hb)
  let rho : ℝ := min r (1 / 2)
  have hrho : 0 < rho := lt_min hr (by norm_num)
  have hsub : Metric.ball (0 : Rd (k + 1)) rho ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  refine ⟨rho, hrho, min_le_right _ _, ?_⟩
  intro x hx y hy
  have hdiff : ∀ z ∈ Metric.ball (0 : Rd (k + 1)) rho, DifferentiableAt ℝ E z :=
    fun z hz => (hball z (hsub hz)).1
  have hbound : ∀ z ∈ Metric.ball (0 : Rd (k + 1)) rho, ‖fderiv ℝ E z‖ ≤ epsilon :=
    fun z hz => (hball z (hsub hz)).2.le
  have herror := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_ball (0 : Rd (k + 1)) rho) hy hx
  have hrewrite : E x - E y =
      (equalAreaCapVector k x - equalAreaCapVector k y) - T (x - y) := by
    simp only [E, map_sub]
    abel
  rw [hrewrite] at herror
  have habs := (abs_norm_sub_norm_le
    (equalAreaCapVector k x - equalAreaCapVector k y) (T (x - y))).trans herror
  have hTnorm : ‖T (x - y)‖ = ‖x - y‖ :=
    (equalAreaTangent (k + 1)).norm_map (x - y)
  rw [hTnorm] at habs
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  constructor
  all_goals nlinarith

theorem equalAreaTail_norm_le (k : ℕ) (x : Rd (k + 1)) :
    ‖euclideanTail k x‖ ≤ ‖x‖ := by
  have h := euclideanCons_norm_sq k (x 0) (euclideanTail k x)
  rw [euclideanCons_head_tail] at h
  nlinarith [sq_nonneg (x 0), norm_nonneg (euclideanTail k x), norm_nonneg x]

namespace EqualAreaCone

open Module

abbrev E (k : ℕ) := (ℝ × ℝ) × Rd k

def coneBasis (k : ℕ) : Basis (Fin 2 ⊕ Fin k) ℝ (E k) :=
  (Basis.finTwoProd ℝ).prod (EuclideanSpace.basisFun (Fin k) ℝ).toBasis

def radialCLM (k : ℕ) : E k →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Rd k))

def angleCLM (k : ℕ) : E k →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Rd k))

def transverseCLM (k : ℕ) : E k →L[ℝ] Rd k :=
  ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Rd k)

def amplitude (k : ℕ) (p : E k) : ℝ := Real.sqrt (1 - ‖p.2‖ ^ 2)

def amplitudeDerivative (k : ℕ) (a : ℝ) (u : Rd k) : E k →L[ℝ] ℝ :=
  (-a⁻¹) • ((innerSL ℝ u).comp (transverseCLM k))

def prepolar (k : ℕ) (p : E k) : E k :=
  ((p.1.1 * amplitude k p, p.1.2), p.1.1 • p.2)

def prepolarDerivative (k : ℕ) (r a : ℝ) (u : Rd k) : E k →L[ℝ] E k :=
  ((r • amplitudeDerivative k a u + a • radialCLM k).prod (angleCLM k)).prod
    (r • transverseCLM k + (radialCLM k).smulRight u)

def polarProduct (k : ℕ) : E k → E k := Prod.map polarCoord.symm id

def polarProductDerivative (k : ℕ) (p : E k) : E k →L[ℝ] E k :=
  (fderivPolarCoordSymm p.1).prodMap (ContinuousLinearMap.id ℝ (Rd k))

def cone (k : ℕ) : E k → E k := polarProduct k ∘ prepolar k

def coneDerivative (k : ℕ) (p : E k) : E k →L[ℝ] E k :=
  (polarProductDerivative k (prepolar k p)).comp
    (prepolarDerivative k p.1.1 (amplitude k p) p.2)

def prepolarA (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, 1]

def prepolarB (k : ℕ) (a : ℝ) (u : Fin k → ℝ) : Matrix (Fin 2) (Fin k) ℝ :=
  fun i j => if i = 0 then (-a⁻¹) * u j else 0

def prepolarC (k : ℕ) (u : Fin k → ℝ) : Matrix (Fin k) (Fin 2) ℝ :=
  fun i j => if j = 0 then u i else 0

def prepolarMatrix (k : ℕ) (r a : ℝ) (u : Fin k → ℝ) :
    Matrix (Fin 2 ⊕ Fin k) (Fin 2 ⊕ Fin k) ℝ :=
  Matrix.fromBlocks (prepolarA a) (r • prepolarB k a u)
    (prepolarC k u) (r • (1 : Matrix (Fin k) (Fin k) ℝ))

/-- Factoring out transverse scaling avoids an inverse for the radial block. -/
theorem prepolarMatrix_det (k : ℕ) (r a : ℝ) (u : Fin k → ℝ)
    (ha : a ≠ 0) (hunit : a ^ 2 + ∑ i, (u i) ^ 2 = 1) :
    (prepolarMatrix k r a u).det = r ^ k / a := by
  classical
  have hscalar : a - ((-a⁻¹) * ∑ i : Fin k, (u i) ^ 2) = a⁻¹ := by
    field_simp [ha]
    linarith [hunit]
  have hschur : prepolarA a - prepolarB k a u * prepolarC k u =
      !![a⁻¹, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [prepolarA, prepolarB, prepolarC, Matrix.mul_apply]
    simpa [Finset.mul_sum, pow_two, mul_assoc] using hscalar
  have hfactor : prepolarMatrix k r a u =
      Matrix.fromBlocks (prepolarA a) (prepolarB k a u) (prepolarC k u)
        (1 : Matrix (Fin k) (Fin k) ℝ) *
      Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0
        (r • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
    rw [Matrix.fromBlocks_multiply]
    simp [prepolarMatrix]
  rw [hfactor, Matrix.det_mul, Matrix.det_fromBlocks_one₂₂, hschur,
    Matrix.det_fromBlocks_zero₂₁]
  simp [Matrix.det_fin_two_of, div_eq_mul_inv, mul_comm]

/-- The explicit matrix represents the natural derivative in the product basis. -/
theorem prepolarDerivative_toMatrix (k : ℕ) (r a : ℝ) (u : Rd k) :
    LinearMap.toMatrix (coneBasis k) (coneBasis k)
      (prepolarDerivative k r a u).toLinearMap =
        prepolarMatrix k r a (fun i => u i) := by
  classical
  ext (i | i) (j | j)
  · fin_cases i <;> fin_cases j
    all_goals simp [LinearMap.toMatrix_apply, coneBasis, prepolarDerivative,
      amplitudeDerivative, radialCLM, angleCLM, transverseCLM,
      prepolarMatrix, prepolarA]
  · fin_cases i
    all_goals simp [LinearMap.toMatrix_apply, coneBasis, prepolarDerivative,
      amplitudeDerivative, radialCLM, angleCLM, transverseCLM,
      prepolarMatrix, prepolarB, EuclideanSpace.inner_single_right]
  · fin_cases j
    all_goals simp [LinearMap.toMatrix_apply, coneBasis, prepolarDerivative,
      amplitudeDerivative, radialCLM, angleCLM, transverseCLM,
      prepolarMatrix, prepolarC]
  · simp [LinearMap.toMatrix_apply, coneBasis, prepolarDerivative,
      amplitudeDerivative, radialCLM, angleCLM, transverseCLM,
      prepolarMatrix, Matrix.one_apply]

theorem prepolarDerivative_det (k : ℕ) (r a : ℝ) (u : Rd k)
    (ha : a ≠ 0) (hunit : a ^ 2 + ∑ i, (u i) ^ 2 = 1) :
    (prepolarDerivative k r a u).det = r ^ k / a := by
  change LinearMap.det (prepolarDerivative k r a u).toLinearMap = r ^ k / a
  rw [← LinearMap.det_toMatrix (coneBasis k), prepolarDerivative_toMatrix]
  exact prepolarMatrix_det k r a (fun i => u i) ha hunit

theorem polarProductDerivative_det (k : ℕ) (p : E k) :
    (polarProductDerivative k p).det = p.1.1 := by
  change LinearMap.det
    ((fderivPolarCoordSymm p.1).toLinearMap.prodMap
      (LinearMap.id : Rd k →ₗ[ℝ] Rd k)) = p.1.1
  rw [LinearMap.det_prodMap, LinearMap.det_id, mul_one]
  exact det_fderivPolarCoordSymm p.1

theorem amplitude_pos (k : ℕ) {p : E k} (hu : ‖p.2‖ < 1) :
    0 < amplitude k p := by
  exact Real.sqrt_pos.2 (by nlinarith [norm_nonneg p.2])

theorem amplitude_unit_sum (k : ℕ) {p : E k} (hu : ‖p.2‖ < 1) :
    amplitude k p ^ 2 + ∑ i : Fin k, (p.2 i) ^ 2 = 1 := by
  have hsq : amplitude k p ^ 2 = 1 - ‖p.2‖ ^ 2 :=
    Real.sq_sqrt (by nlinarith [norm_nonneg p.2])
  rw [← EuclideanSpace.real_norm_sq_eq, hsq]
  ring

theorem coneDerivative_det (k : ℕ) {p : E k} (hu : ‖p.2‖ < 1) :
    (coneDerivative k p).det = p.1.1 ^ (k + 1) := by
  have ha : amplitude k p ≠ 0 := (amplitude_pos k hu).ne'
  have hcomp : (coneDerivative k p).det =
      (polarProductDerivative k (prepolar k p)).det *
        (prepolarDerivative k p.1.1 (amplitude k p) p.2).det :=
    LinearMap.det_comp _ _
  rw [hcomp, polarProductDerivative_det,
    prepolarDerivative_det k _ _ _ ha (amplitude_unit_sum k hu)]
  dsimp only [prepolar]
  simp [div_eq_mul_inv, mul_left_comm, ha, pow_succ]

theorem hasFDerivAt_amplitude (k : ℕ) {p : E k} (hu : ‖p.2‖ < 1) :
    HasFDerivAt (amplitude k) (amplitudeDerivative k (amplitude k p) p.2) p := by
  have ht : HasFDerivAt (fun q : E k => q.2) (transverseCLM k) p :=
    (transverseCLM k).hasFDerivAt
  have hi := ht.norm_sq.const_sub (1 : ℝ)
  have hne : 1 - ‖p.2‖ ^ 2 ≠ 0 := ne_of_gt (by nlinarith [norm_nonneg p.2])
  convert! hi.sqrt hne using 1
  refine ContinuousLinearMap.ext (fun q => ?_)
  simp [amplitude, amplitudeDerivative, transverseCLM]
  ring

theorem hasFDerivAt_prepolar (k : ℕ) {p : E k} (hu : ‖p.2‖ < 1) :
    HasFDerivAt (prepolar k)
      (prepolarDerivative k p.1.1 (amplitude k p) p.2) p := by
  have hr : HasFDerivAt (fun q : E k => q.1.1) (radialCLM k) p :=
    (radialCLM k).hasFDerivAt
  have hv : HasFDerivAt (fun q : E k => q.1.2) (angleCLM k) p :=
    (angleCLM k).hasFDerivAt
  have ht : HasFDerivAt (fun q : E k => q.2) (transverseCLM k) p :=
    (transverseCLM k).hasFDerivAt
  simpa only [prepolar, prepolarDerivative] using!
    ((hr.mul (hasFDerivAt_amplitude k hu)).prodMk hv).prodMk (hr.smul ht)

theorem hasFDerivAt_polarProduct (k : ℕ) (p : E k) :
    HasFDerivAt (polarProduct k) (polarProductDerivative k p) p := by
  exact HasFDerivAt.prodMap p (hasFDerivAt_polarCoord_symm p.1) (hasFDerivAt_id p.2)

theorem hasFDerivAt_cone (k : ℕ) {p : E k} (hu : ‖p.2‖ < 1) :
    HasFDerivAt (cone k) (coneDerivative k p) p := by
  exact (hasFDerivAt_polarProduct k (prepolar k p)).comp p (hasFDerivAt_prepolar k hu)

theorem coneDerivative_abs_det (k : ℕ) {p : E k}
    (hu : ‖p.2‖ < 1) (hr : 0 ≤ p.1.1) :
    |(coneDerivative k p).det| = p.1.1 ^ (k + 1) := by
  rw [coneDerivative_det k hu, abs_of_nonneg (pow_nonneg hr _)]

end EqualAreaCone

/-- The exact measure-preserving insertion of one Euclidean coordinate. -/
def equalAreaConsMeasurableEquiv (k : ℕ) : (ℝ × Rd k) ≃ᵐ Rd (k + 1) :=
  (((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm).trans
      (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ))

@[simp]
theorem equalAreaConsMeasurableEquiv_apply (k : ℕ) (p : ℝ × Rd k) :
    equalAreaConsMeasurableEquiv k p = euclideanCons k p.1 p.2 := by
  change WithLp.toLp 2
    ((0 : Fin (k + 1)).insertNth p.1 (fun i : Fin k => p.2 i)) =
      euclideanCons k p.1 p.2
  rw [Fin.insertNth_zero']
  rfl

theorem equalAreaConsMeasurableEquiv_measurePreserving (k : ℕ) :
    MeasurePreserving (equalAreaConsMeasurableEquiv k)
      ((volume : Measure ℝ).prod (volume : Measure (Rd k)))
      (volume : Measure (Rd (k + 1))) := by
  have hfirst : MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr
        (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm)
      ((volume : Measure ℝ).prod (volume : Measure (Rd k)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin k → ℝ))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_ofLp (Fin k))
  have hmiddle : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm
      ((volume : Measure ℝ).prod (volume : Measure (Fin k → ℝ)))
      (volume : Measure (Fin (k + 1) → ℝ)) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm
  have hlast : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ))
      (volume : Measure (Fin (k + 1) → ℝ)) (volume : Measure (Rd (k + 1))) :=
    PiLp.volume_preserving_toLp (Fin (k + 1))
  exact (hfirst.trans hmiddle).trans hlast

/-- Product coordinates packed into the ambient Euclidean space. -/
def equalAreaPackingMeasurableEquiv (k : ℕ) :
    ((ℝ × ℝ) × Rd k) ≃ᵐ Rd (k + 2) :=
  ((MeasurableEquiv.prodAssoc : ((ℝ × ℝ) × Rd k) ≃ᵐ ℝ × (ℝ × Rd k)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (equalAreaConsMeasurableEquiv k))).trans
      (equalAreaConsMeasurableEquiv (k + 1))

@[simp]
theorem equalAreaPackingMeasurableEquiv_apply (k : ℕ) (p : (ℝ × ℝ) × Rd k) :
    equalAreaPackingMeasurableEquiv k p =
      euclideanCons (k + 1) p.1.1 (euclideanCons k p.1.2 p.2) := by
  change equalAreaConsMeasurableEquiv (k + 1)
    (p.1.1, equalAreaConsMeasurableEquiv k (p.1.2, p.2)) = _
  simp only [equalAreaConsMeasurableEquiv_apply]

theorem equalAreaPackingMeasurableEquiv_measurePreserving (k : ℕ) :
    MeasurePreserving (equalAreaPackingMeasurableEquiv k)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
        (volume : Measure (Rd k)))
      (volume : Measure (Rd (k + 2))) := by
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((ℝ × ℝ) × Rd k) ≃ᵐ ℝ × (ℝ × Rd k))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure (Rd k)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Rd k)))) :=
    measurePreserving_prodAssoc volume volume volume
  have hprod : MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr (equalAreaConsMeasurableEquiv k))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Rd k))))
      ((volume : Measure ℝ).prod (volume : Measure (Rd (k + 1)))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (equalAreaConsMeasurableEquiv_measurePreserving k)
  exact (hassoc.trans hprod).trans (equalAreaConsMeasurableEquiv_measurePreserving (k + 1))

open scoped Classical

/-- A total sphere-valued chart, agreeing with the cylinder formula on its domain. -/
def equalAreaCapPoint (k : ℕ) (x : Rd (k + 1)) : Sphere (k + 1) :=
  if hx : ‖euclideanTail k x‖ < 1 then
    ⟨equalAreaCapVector k x, equalAreaCapVector_norm k x hx⟩
  else normalPoint (k + 1) 1 0

theorem equalAreaCapPoint_val (k : ℕ) {x : Rd (k + 1)}
    (hx : ‖euclideanTail k x‖ < 1) :
    (equalAreaCapPoint k x).val = equalAreaCapVector k x := by
  simp [equalAreaCapPoint, hx]

theorem equalAreaCone_packing (k : ℕ) (p : EqualAreaCone.E k) :
    equalAreaPackingMeasurableEquiv k (EqualAreaCone.cone k p) =
      p.1.1 • equalAreaCapVector k (euclideanCons k p.1.2 p.2) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [EqualAreaCone.cone, EqualAreaCone.polarProduct, EqualAreaCone.prepolar,
      EqualAreaCone.amplitude, equalAreaCapVector, equalAreaCapAmplitude,
      euclideanCons, euclideanTail, mul_assoc]
  · refine Fin.cases ?_ (fun j => ?_) j
    all_goals simp [EqualAreaCone.cone, EqualAreaCone.polarProduct, EqualAreaCone.prepolar,
      EqualAreaCone.amplitude, equalAreaCapVector, equalAreaCapAmplitude,
      euclideanCons, euclideanTail, mul_assoc]

/-- Separate radial coordinate from the Euclidean chart parameter. -/
def equalAreaParameterMeasurableEquiv (k : ℕ) :
    EqualAreaCone.E k ≃ᵐ ℝ × Rd (k + 1) :=
  (MeasurableEquiv.prodAssoc : ((ℝ × ℝ) × Rd k) ≃ᵐ ℝ × (ℝ × Rd k)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (equalAreaConsMeasurableEquiv k))

@[simp]
theorem equalAreaParameterMeasurableEquiv_apply (k : ℕ) (p : EqualAreaCone.E k) :
    equalAreaParameterMeasurableEquiv k p = (p.1.1, euclideanCons k p.1.2 p.2) := by
  change (p.1.1, equalAreaConsMeasurableEquiv k (p.1.2, p.2)) = _
  simp only [equalAreaConsMeasurableEquiv_apply]

theorem equalAreaParameterMeasurableEquiv_measurePreserving (k : ℕ) :
    MeasurePreserving (equalAreaParameterMeasurableEquiv k)
      (volume : Measure (EqualAreaCone.E k))
      ((volume : Measure ℝ).prod (volume : Measure (Rd (k + 1)))) := by
  exact (measurePreserving_prodAssoc (volume : Measure ℝ) volume volume).trans
    (show MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr (equalAreaConsMeasurableEquiv k))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Rd k))))
      ((volume : Measure ℝ).prod (volume : Measure (Rd (k + 1)))) from
        (MeasurePreserving.id (volume : Measure ℝ)).prod
          (equalAreaConsMeasurableEquiv_measurePreserving k))

theorem exists_equalAreaCapVector_injOn (k : ℕ) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 / 2 ∧
      Set.InjOn (equalAreaCapVector k) (Metric.ball (0 : Rd (k + 1)) rho) := by
  obtain ⟨rho, hrho, hsmall, hdist⟩ :=
    exists_equalAreaCapVector_relative_distortion k (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨rho, hrho, hsmall, ?_⟩
  intro x hx y hy hxy
  have hlo := (hdist x hx y hy).1
  rw [hxy, sub_self, norm_zero] at hlo
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (x - y)]))

theorem equalAreaCone_packing_norm (k : ℕ) (p : EqualAreaCone.E k)
    (hu : ‖p.2‖ < 1) (hr : 0 ≤ p.1.1) :
    ‖equalAreaPackingMeasurableEquiv k (EqualAreaCone.cone k p)‖ = p.1.1 := by
  rw [equalAreaCone_packing, norm_smul,
    equalAreaCapVector_norm k _ (show ‖euclideanTail k (euclideanCons k p.1.2 p.2)‖ < 1 from hu)]
  simp [Real.norm_eq_abs, abs_of_nonneg hr]

/-- Cone injectivity follows by recovering positive radius in the true ambient norm. -/
theorem equalAreaCone_injOn (k : ℕ) (D : Set (Rd (k + 1)))
    (hD : ∀ x ∈ D, ‖euclideanTail k x‖ < 1)
    (hinj : Set.InjOn (equalAreaCapVector k) D) :
    Set.InjOn (EqualAreaCone.cone k)
      (equalAreaParameterMeasurableEquiv k ⁻¹' (Set.Ioo (0 : ℝ) 1 ×ˢ D)) := by
  intro p hp q hq hpq
  simp only [Set.mem_preimage, equalAreaParameterMeasurableEquiv_apply,
    Set.mem_prod, Set.mem_Ioo] at hp hq
  have hpu : ‖p.2‖ < 1 := hD (euclideanCons k p.1.2 p.2) hp.2
  have hqu : ‖q.2‖ < 1 := hD (euclideanCons k q.1.2 q.2) hq.2
  have hr : p.1.1 = q.1.1 := by
    simpa only [equalAreaCone_packing_norm k p hpu hp.1.1.le,
      equalAreaCone_packing_norm k q hqu hq.1.1.le] using
      congrArg (fun z => ‖equalAreaPackingMeasurableEquiv k z‖) hpq
  have hscaled := congrArg (equalAreaPackingMeasurableEquiv k) hpq
  rw [equalAreaCone_packing, equalAreaCone_packing, ← hr] at hscaled
  have hx : euclideanCons k p.1.2 p.2 = euclideanCons k q.1.2 q.2 :=
    hinj hp.2 hq.2 ((smul_right_injective (Rd (k + 2)) hp.1.1.ne') hscaled)
  exact (equalAreaParameterMeasurableEquiv k).injective
    (by simp only [equalAreaParameterMeasurableEquiv_apply, hr, hx])

/-- The packed cone is precisely the open radial cone over the chart image. -/
theorem equalAreaCone_image (k : ℕ) (D : Set (Rd (k + 1))) :
    equalAreaPackingMeasurableEquiv k ''
      (EqualAreaCone.cone k ''
        (equalAreaParameterMeasurableEquiv k ⁻¹' (Set.Ioo (0 : ℝ) 1 ×ˢ D))) =
      Set.Ioo (0 : ℝ) 1 • (equalAreaCapVector k '' D) := by
  have hcomp : equalAreaPackingMeasurableEquiv k ∘ EqualAreaCone.cone k =
      (fun q : ℝ × Rd (k + 1) => q.1 • equalAreaCapVector k q.2) ∘
        equalAreaParameterMeasurableEquiv k := by
    funext p
    simp only [Function.comp_apply, equalAreaCone_packing, equalAreaParameterMeasurableEquiv_apply]
  rw [← Set.image_comp, hcomp, Set.image_comp,
    Set.image_preimage_eq _ (equalAreaParameterMeasurableEquiv k).surjective]
  ext z
  simp only [Set.mem_image, Set.mem_smul, Set.mem_prod, Prod.exists]
  aesop

theorem equalArea_lintegral_radial_pow (d : ℕ) :
    (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ d)) =
      ((d + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  have hint : IntegrableOn (fun r : ℝ => r ^ d) (Set.Ioo 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
      ((continuous_id.pow d).intervalIntegrable 0 1)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (fun r : ℝ => r ^ d) :=
    (ae_restrict_mem measurableSet_Ioo).mono fun r hr => pow_nonneg hr.1.le d
  have hreal : (∫ r in Set.Ioo (0 : ℝ) 1, r ^ d) = 1 / ((d + 1 : ℕ) : ℝ) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg, hreal]
  simp only [one_div,
    ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < (d + 1 : ℕ)),
    ENNReal.ofReal_natCast]

theorem equalArea_radial_product_volume (d : ℕ) (D : Set (Rd d)) :
    (∫⁻ p in Set.Ioo (0 : ℝ) 1 ×ˢ D, ENNReal.ofReal (p.1 ^ d)
      ∂((volume : Measure ℝ).prod (volume : Measure (Rd d)))) =
      ((d + 1 : ℕ) : ℝ≥0∞)⁻¹ * (volume : Measure (Rd d)) D := by
  rw [setLIntegral_prod_symm _ ((measurable_fst.pow_const d).ennreal_ofReal.aemeasurable)]
  simp only [equalArea_lintegral_radial_pow, lintegral_const, Measure.restrict_apply_univ]

/-- Exact cone volume for every measurable injective chart piece. -/
theorem equalAreaCone_volume (k : ℕ) (D : Set (Rd (k + 1)))
    (hD : MeasurableSet D) (hcyl : ∀ x ∈ D, ‖euclideanTail k x‖ < 1)
    (hinj : Set.InjOn (equalAreaCapVector k) D) :
    (volume : Measure (Rd (k + 2)))
      (Set.Ioo (0 : ℝ) 1 • (equalAreaCapVector k '' D)) =
        ((k + 2 : ℕ) : ℝ≥0∞)⁻¹ * (volume : Measure (Rd (k + 1))) D := by
  let S := equalAreaParameterMeasurableEquiv k ⁻¹' (Set.Ioo (0 : ℝ) 1 ×ˢ D)
  have hS : MeasurableSet S :=
    (equalAreaParameterMeasurableEquiv k).measurable (measurableSet_Ioo.prod hD)
  have hderiv : ∀ p ∈ S, HasFDerivWithinAt (EqualAreaCone.cone k)
      (EqualAreaCone.coneDerivative k p) S p := fun p hp =>
    (EqualAreaCone.hasFDerivAt_cone k
      (hcyl (euclideanCons k p.1.2 p.2)
        (by simpa only [equalAreaParameterMeasurableEquiv_apply] using hp.2))).hasFDerivWithinAt
  letI : Measure.IsAddHaarMeasure (volume : Measure (EqualAreaCone.E k)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hJac := lintegral_abs_det_fderiv_eq_addHaar_image
    (volume : Measure (EqualAreaCone.E k)) hS hderiv (equalAreaCone_injOn k D hcyl hinj)
  have hpack : (volume : Measure (EqualAreaCone.E k)) (EqualAreaCone.cone k '' S) =
      (volume : Measure (Rd (k + 2)))
        (equalAreaPackingMeasurableEquiv k '' (EqualAreaCone.cone k '' S)) := by
    simpa only [Set.preimage_image_eq _ (equalAreaPackingMeasurableEquiv k).injective] using!
      (equalAreaPackingMeasurableEquiv_measurePreserving k).measure_preimage_emb
        (equalAreaPackingMeasurableEquiv k).measurableEmbedding
        (equalAreaPackingMeasurableEquiv k '' (EqualAreaCone.cone k '' S))
  have hdet : ∀ p ∈ S, |(EqualAreaCone.coneDerivative k p).det| =
      (equalAreaParameterMeasurableEquiv k p).1 ^ (k + 1) := by
    intro p hp
    simp only [S, Set.mem_preimage, equalAreaParameterMeasurableEquiv_apply,
      Set.mem_prod, Set.mem_Ioo] at hp ⊢
    exact EqualAreaCone.coneDerivative_abs_det k (hcyl (euclideanCons k p.1.2 p.2) hp.2)
      hp.1.1.le
  rw [← equalAreaCone_image, ← hpack, ← hJac]
  have hrad := (equalAreaParameterMeasurableEquiv_measurePreserving k).setLIntegral_comp_preimage_emb
      (equalAreaParameterMeasurableEquiv k).measurableEmbedding
      (fun q : ℝ × Rd (k + 1) => ENNReal.ofReal (q.1 ^ (k + 1)))
      (Set.Ioo (0 : ℝ) 1 ×ˢ D)
  rw [← equalArea_radial_product_volume (k + 1) D, ← hrad]
  apply lintegral_congr_ae
  exact (ae_restrict_mem hS).mono fun p hp => congrArg ENNReal.ofReal (hdet p hp)

theorem equalAreaCapPoint_continuousOn (k : ℕ) (D : Set (Rd (k + 1)))
    (hcyl : ∀ x ∈ D, ‖euclideanTail k x‖ < 1) :
    ContinuousOn (equalAreaCapPoint k) D := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  have hcont : ContinuousOn (equalAreaCapVector k) D := fun x hx =>
    (equalAreaCapVector_contDiffAt k 1 (hcyl x hx)).continuousAt.continuousWithinAt
  exact hcont.congr fun x hx => equalAreaCapPoint_val k (hcyl x hx)

theorem equalAreaCapPoint_injOn (k : ℕ) (D : Set (Rd (k + 1)))
    (hcyl : ∀ x ∈ D, ‖euclideanTail k x‖ < 1)
    (hinj : Set.InjOn (equalAreaCapVector k) D) : Set.InjOn (equalAreaCapPoint k) D := by
  exact fun x hx y hy hxy => hinj hx hy
    (by simpa only [equalAreaCapPoint_val k (hcyl x hx),
      equalAreaCapPoint_val k (hcyl y hy)] using congrArg Subtype.val hxy)

/-- Exact normalized area for every measurable injective cylinder piece. -/
theorem equalAreaCapPoint_sphericalMeasure (k : ℕ) (D : Set (Rd (k + 1)))
    (hD : MeasurableSet D) (hcyl : ∀ x ∈ D, ‖euclideanTail k x‖ < 1)
    (hinj : Set.InjOn (equalAreaCapVector k) D) :
    sphericalMeasure (k + 1) (equalAreaCapPoint k '' D) =
      (ENNReal.ofReal (omega (k + 1)))⁻¹ * (volume : Measure (Rd (k + 1))) D := by
  let e := problem1SphereIsometryEquiv (k + 1)
  let Φ := e ∘ equalAreaCapPoint k
  have hpointmeas : MeasurableSet (equalAreaCapPoint k '' D) :=
    hD.image_of_continuousOn_injOn (equalAreaCapPoint_continuousOn k D hcyl)
      (equalAreaCapPoint_injOn k D hcyl hinj)
  have hrawmeas : MeasurableSet (Φ '' D) := by
    simpa only [Φ, Set.image_comp] using!
      e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hpointmeas
  have hvalimage : Subtype.val '' (Φ '' D) = equalAreaCapVector k '' D := by
    rw [Set.image_image]
    exact Set.image_congr fun x hx => equalAreaCapPoint_val k (hcyl x hx)
  have harea : (volume : Measure (Rd (k + 2))).toSphere (Φ '' D) =
      (volume : Measure (Rd (k + 1))) D := by
    rw [Measure.toSphere_apply' _ hrawmeas, hvalimage, equalAreaCone_volume k D hD hcyl hinj]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    exact ENNReal.mul_inv_cancel_left (by positivity) (by finiteness)
  have hpre : e.symm ⁻¹' (equalAreaCapPoint k '' D) = Φ '' D := by
    simpa only [Φ, Set.image_comp] using!
      (e.toEquiv.image_eq_preimage_symm (equalAreaCapPoint k '' D)).symm
  have hm := congrArg
    (fun μ : Measure (Sphere (k + 1)) => μ (equalAreaCapPoint k '' D))
    (unitSphere_toSphere_map_eq (k + 1))
  rw [Measure.map_apply e.symm.continuous.measurable hpointmeas,
    hpre, Measure.smul_apply, smul_eq_mul, harea] at hm
  rw [hm]
  exact (ENNReal.inv_mul_cancel_left
    (ENNReal.ofReal_pos.mpr (Riesz.Asymptotics.omega_pos (k + 1))).ne'
    ENNReal.ofReal_ne_top).symm

/-- Local charts have exact area and arbitrarily small relative distortion. -/
theorem exists_equalAreaCapPoint_chart (k : ℕ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon' : epsilon < 1) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 / 2 ∧
      ContinuousOn (equalAreaCapPoint k) (Metric.ball 0 rho) ∧
      Set.InjOn (equalAreaCapPoint k) (Metric.ball 0 rho) ∧
      (∀ D : Set (Rd (k + 1)), MeasurableSet D → D ⊆ Metric.ball 0 rho →
        sphericalMeasure (k + 1) (equalAreaCapPoint k '' D) =
          (ENNReal.ofReal (omega (k + 1)))⁻¹ * (volume : Measure (Rd (k + 1))) D) ∧
      (∀ x ∈ Metric.ball (0 : Rd (k + 1)) rho, ∀ y ∈ Metric.ball 0 rho,
        (1 - epsilon) * ‖x - y‖ ≤ chord (k + 1) (equalAreaCapPoint k x) (equalAreaCapPoint k y) ∧
        chord (k + 1) (equalAreaCapPoint k x) (equalAreaCapPoint k y) ≤
          (1 + epsilon) * ‖x - y‖) := by
  obtain ⟨rho, hrho, hsmall, hdist⟩ := exists_equalAreaCapVector_relative_distortion k hepsilon
  have hcyl : ∀ x ∈ Metric.ball (0 : Rd (k + 1)) rho, ‖euclideanTail k x‖ < 1 := by
    intro x hx
    have hxnorm : ‖x‖ < rho := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    linarith [equalAreaTail_norm_le k x]
  have hinj : Set.InjOn (equalAreaCapVector k) (Metric.ball (0 : Rd (k + 1)) rho) := by
    intro x hx y hy hxy
    have hlo := (hdist x hx y hy).1
    rw [hxy, sub_self, norm_zero] at hlo
    exact sub_eq_zero.mp (norm_eq_zero.mp
      (by nlinarith [norm_nonneg (x - y), sub_pos.mpr hepsilon']))
  refine ⟨rho, hrho, hsmall, equalAreaCapPoint_continuousOn k _ hcyl,
    equalAreaCapPoint_injOn k _ hcyl hinj, ?_, ?_⟩
  · exact fun D hD hsub => equalAreaCapPoint_sphericalMeasure k D hD
      (fun x hx => hcyl x (hsub hx)) (hinj.mono hsub)
  · intro x hx y hy
    simpa only [chord, equalAreaCapPoint_val k (hcyl x hx),
      equalAreaCapPoint_val k (hcyl y hy)] using hdist x hx y hy

end Riesz.Geometry
