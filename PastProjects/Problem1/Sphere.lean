import Riesz.PastProjects.Problem1.Foundations
open MeasureTheory Set Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator
set_option autoImplicit false
universe u
namespace Problem1
noncomputable section

/-!
Part 2: complete Stage 10 typing scaffold.
Authority: Part 2/Part2_Sphere_and_Harmonic_Core.tex and Part 2/Blueprint.md.
Blueprint gate: Part 2/execution-evidence/BlueprintGateReview.json.
Temporary proof holes are inventoried in scaffold-layout-001.json.
This file is not certified; substantive implementation waits for the entire scaffold to compile.
-/

-- def:coordinate-candidate-measure: Problem1.candidateCoordinateMeasure
noncomputable def candidateCoordinateMeasure (d : ℕ) :
  Measure ℝ := by
  classical
  exact (
    (volume.restrict (Set.Icc (-1 : ℝ) 1)).withDensity (fun t => ENNReal.ofReal (coordinateNormConst d * coordinateWeight d t))
  )

-- lem:candidate-density: Problem1.candidate_density
theorem candidate_density (d : ℕ) (hd : 2 ≤ d) :
  Measurable (fun t : ℝ => ENNReal.ofReal (coordinateNormConst d * coordinateWeight d t)) ∧ ∀ t : ℝ, ENNReal.ofReal (coordinateNormConst d * coordinateWeight d t) < ⊤ ∧ (ENNReal.ofReal (coordinateNormConst d * coordinateWeight d t)).toReal = coordinateNormConst d * coordinateWeight d t ∧ 0 ≤ coordinateNormConst d * coordinateWeight d t := by
  exact ⟨ENNReal.continuous_ofReal.measurable.comp
    (measurable_const.mul (coordinate_weight_measurable d hd).1),
    fun t => ⟨ENNReal.ofReal_lt_top,
      ENNReal.toReal_ofReal (mul_nonneg (coordinate_normalizer_gamma d hd).2.1.le
        ((coordinate_weight_measurable d hd).2 t)),
      mul_nonneg (coordinate_normalizer_gamma d hd).2.1.le
        ((coordinate_weight_measurable d hd).2 t)⟩⟩

-- lem:candidate-mass: Problem1.candidate_measure_univ
theorem candidate_measure_univ (d : ℕ) (hd : 2 ≤ d) :
  candidateCoordinateMeasure d Set.univ = 1 := by
  rw [candidateCoordinateMeasure, withDensity_apply _ MeasurableSet.univ]
  rw [Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
    (show Integrable (fun t : ℝ => coordinateNormConst d * coordinateWeight d t)
      (volume.restrict (Set.Icc (-1 : ℝ) 1)) from
      by simpa using ((coordinate_moment d 0 hd).1.const_mul (coordinateNormConst d)))
    (ae_of_all _ fun t => ((candidate_density d hd).2 t).2.2)]
  rw [integral_const_mul]
  change ENNReal.ofReal (coordinateNormConst d * coordinateNormalizer d) = 1
  rw [(coordinate_normalizer_gamma d hd).2.2, ENNReal.ofReal_one]

-- lem:candidate-concentration: Problem1.candidate_measure_concentrated
theorem candidate_measure_concentrated (d : ℕ) (hd : 2 ≤ d) :
  candidateCoordinateMeasure d (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  simp [candidateCoordinateMeasure, withDensity_apply _ measurableSet_Icc.compl]

-- cor:coordinate-candidate-probability: Problem1.candidate_isProbabilityMeasure
theorem candidate_isProbabilityMeasure (d : ℕ) (hd : 2 ≤ d) :
  IsProbabilityMeasure (candidateCoordinateMeasure d) := by
  exact ⟨candidate_measure_univ d hd⟩

-- cor:coordinate-candidate-probability: Problem1.candidate_probability
theorem candidate_probability (d : ℕ) (hd : 2 ≤ d) :
  IsProbabilityMeasure (candidateCoordinateMeasure d) ∧ IsFiniteMeasure (candidateCoordinateMeasure d) ∧ candidateCoordinateMeasure d (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  letI := candidate_isProbabilityMeasure d hd
  exact ⟨inferInstance, inferInstance, candidate_measure_concentrated d hd⟩

-- lem:candidate-integrability: Problem1.candidate_integrability_iff
theorem candidate_integrability_iff (d : ℕ) (hd : 2 ≤ d) (F : ℝ → ℝ) (hF : Measurable F) :
  Integrable F (candidateCoordinateMeasure d) ↔ IntegrableOn (fun t => F t * coordinateWeight d t) (Set.Icc (-1 : ℝ) 1) volume := by
  rw [candidateCoordinateMeasure, integrable_withDensity_iff (candidate_density d hd).1
    (ae_of_all _ fun t => ((candidate_density d hd).2 t).1)]
  simpa only [IntegrableOn, ((candidate_density d hd).2 _).2.1, mul_left_comm] using
    (integrable_const_mul_iff (μ := volume.restrict (Set.Icc (-1 : ℝ) 1))
      (ne_of_gt (coordinate_normalizer_gamma d hd).2.1).isUnit
      (fun t => F t * coordinateWeight d t))

-- lem:coordinate-candidate-integral: Problem1.candidate_integral
theorem candidate_integral (d : ℕ) (hd : 2 ≤ d) (F : ℝ → ℝ) (hF : Measurable F) (hFw : IntegrableOn (fun t => F t * coordinateWeight d t) (Set.Icc (-1 : ℝ) 1) volume) :
  (∫ t, F t ∂candidateCoordinateMeasure d) = coordinateNormConst d * ∫ t in Set.Icc (-1 : ℝ) 1, F t * coordinateWeight d t ∂volume := by
  rw [candidateCoordinateMeasure,
    integral_withDensity_eq_integral_toReal_smul (candidate_density d hd).1
      (ae_of_all _ fun t => ((candidate_density d hd).2 t).1) F]
  simpa only [((candidate_density d hd).2 _).2.1, smul_eq_mul,
    mul_assoc, mul_comm, mul_left_comm] using
    (integral_const_mul_of_integrable (c := coordinateNormConst d) hFw)

-- def:coordinate-pushforward: Problem1.sphereCoordinate
noncomputable def sphereCoordinate (d : ℕ) (x : Sphere d) (y : Sphere d) :
  ℝ := by
  classical
  exact (
    inner ℝ (x : Euclidean d) (y : Euclidean d)
  )

-- def:coordinate-pushforward: Problem1.coordinateLawMeasure
noncomputable def coordinateLawMeasure (d : ℕ) :
  Measure ℝ := by
  classical
  exact (
    Measure.map (sphereCoordinate d (northPole d)) (sigma d)
  )

-- lem:coordinate-pushforward-support: Problem1.sphereCoordinate_continuous
theorem sphereCoordinate_continuous (d : ℕ) (x : Sphere d) :
  Continuous (sphereCoordinate d x) := by
  exact continuous_const.inner continuous_subtype_val

-- lem:coordinate-pushforward-support: Problem1.sphereCoordinate_abs_le_one
theorem sphereCoordinate_abs_le_one (d : ℕ) (x y : Sphere d) :
  |sphereCoordinate d x y| ≤ 1 := by
  simpa only [sphereCoordinate, unitSphereN_norm, one_mul] using
    (abs_real_inner_le_norm (x : Euclidean d) (y : Euclidean d))

-- lem:coordinate-pushforward-support: Problem1.sphereCoordinate_north_apply
theorem sphereCoordinate_north_apply (d : ℕ) (y : Sphere d) :
  sphereCoordinate d (northPole d) y = (y : Euclidean d) (0 : Fin (d + 1)) := by
  simp [sphereCoordinate, northPole, northPoleN, northPoleVector,
    EuclideanSpace.inner_single_left]

-- lem:coordinate-pushforward-support: Problem1.coordinate_law_probability
theorem coordinate_law_probability (d : ℕ) (hd : 2 ≤ d) :
  IsProbabilityMeasure (coordinateLawMeasure d) ∧ coordinateLawMeasure d (Set.Icc (-1 : ℝ) 1) = 1 ∧ coordinateLawMeasure d (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  have hpre : sphereCoordinate d (northPole d) ⁻¹' Set.Icc (-1 : ℝ) 1 = Set.univ :=
    Set.eq_univ_of_forall fun y => abs_le.mp (sphereCoordinate_abs_le_one d (northPole d) y)
  refine ⟨Measure.isProbabilityMeasure_map
    (sphereCoordinate_continuous d (northPole d)).measurable.aemeasurable, ?_, ?_⟩
  all_goals
    simp only [coordinateLawMeasure,
      Measure.map_apply (sphereCoordinate_continuous d (northPole d)).measurable measurableSet_Icc,
      Measure.map_apply (sphereCoordinate_continuous d (northPole d)).measurable measurableSet_Icc.compl,
      Set.preimage_compl, hpre, Set.compl_univ, measure_univ, measure_empty]

-- def:exact-ambient-polynomial-carriers: Problem1.Ambient
abbrev Ambient (d : ℕ) : Type := by
  classical
  exact (
    MvPolynomial (Fin (d + 1)) ℝ
  )

-- def:exact-ambient-polynomial-carriers: Problem1.P
noncomputable def P (d n : ℕ) : Submodule ℝ (Ambient d) := by
  classical
  exact (
    MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℝ n
  )

-- lem:coordinate-polynomial-integrable: Problem1.coordinate_polynomial_integrable
theorem coordinate_polynomial_integrable (d : ℕ) (hd : 2 ≤ d) (P : Polynomial ℝ) :
  Integrable (fun t => P.eval t) (coordinateLawMeasure d) ∧ Integrable (fun t => P.eval t) (candidateCoordinateMeasure d) := by
  letI := (coordinate_law_probability d hd).1
  letI := candidate_isProbabilityMeasure d hd
  constructor
  · simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
      (ae_iff.mpr (coordinate_law_probability d hd).2.2)] using
      (P.continuous.integrableOn_Icc (μ := coordinateLawMeasure d) (a := (-1 : ℝ)) (b := 1))
  · simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
      (ae_iff.mpr (candidate_measure_concentrated d hd))] using
      (P.continuous.integrableOn_Icc (μ := candidateCoordinateMeasure d) (a := (-1 : ℝ)) (b := 1))

-- def:coordinate-rotation-raw: Problem1.SphereRotationPair
abbrev SphereRotationPair (d : ℕ) :
  Type := by
  classical
  exact (
    {p : Fin (d + 1) × Fin (d + 1) // p.1 < p.2}
  )

-- def:coordinate-rotation-raw: Problem1.planeRotationMatrix
noncomputable def planeRotationMatrix (d : ℕ) (p : SphereRotationPair d) (t : ℝ) :
  Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := by
  classical
  exact (
    fun k l => if k = p.1.1 then (if l = p.1.1 then Real.cos t else if l = p.1.2 then -Real.sin t else 0) else if k = p.1.2 then (if l = p.1.1 then Real.sin t else if l = p.1.2 then Real.cos t else 0) else if k = l then 1 else 0
  )

-- lem:coordinate-rotation-orthogonal: Problem1.planeRotationMatrix_mem
theorem planeRotationMatrix_mem (d : ℕ) (p : SphereRotationPair d) (t : ℝ) :
  planeRotationMatrix d p t ∈ Orthogonal d := by
  apply (Matrix.mem_orthogonalGroup_iff (n := Fin (d + 1)) (R := ℝ)).mpr
  ext k l
  have hp : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  simp +contextual [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    planeRotationMatrix, ite_mul, mul_ite, Finset.sum_ite, hp.symm,
    Finset.filter_eq', ← sq, Real.sin_sq_add_cos_sq, Real.cos_sq_add_sin_sq, mul_comm]
  grind

-- lem:coordinate-rotation-orthogonal: Problem1.planeRotation
noncomputable def planeRotation (d : ℕ) (p : SphereRotationPair d) (t : ℝ) :
  Orthogonal d := by
  classical
  exact (
    ⟨planeRotationMatrix d p t, planeRotationMatrix_mem d p t⟩
  )

-- lem:coordinate-rotation-orthogonal: Problem1.planeRotation_zero
theorem planeRotation_zero (d : ℕ) (p : SphereRotationPair d) :
  planeRotation d p 0 = 1 := by
  ext k l
  simp +contextual [planeRotation, planeRotationMatrix, Matrix.one_apply]
  grind

-- lem:coordinate-rotation-orthogonal: Problem1.planeRotation_mul
theorem planeRotation_mul (d : ℕ) (p : SphereRotationPair d) (t u : ℝ) :
  planeRotation d p t * planeRotation d p u = planeRotation d p (t + u) := by
  ext k l
  have hp : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  simp +contextual [Matrix.mul_apply, planeRotation,
    planeRotationMatrix, ite_mul, mul_ite, Finset.sum_ite, Finset.filter_eq',
    hp.symm, Real.cos_add, Real.sin_add, sub_eq_add_neg, mul_comm]
  grind

-- lem:coordinate-rotation-orthogonal: Problem1.planeRotation_inv
theorem planeRotation_inv (d : ℕ) (p : SphereRotationPair d) (t : ℝ) :
  (planeRotation d p t)⁻¹ = planeRotation d p (-t) := by
  apply inv_eq_of_mul_eq_one_right
  simp [planeRotation_mul, planeRotation_zero]

-- lem:coordinate-rotation-orthogonal: Problem1.planeRotation_continuous
theorem planeRotation_continuous (d : ℕ) (p : SphereRotationPair d) :
  Continuous (planeRotation d p) := by
  unfold planeRotation planeRotationMatrix
  apply Continuous.subtype_mk
  refine continuous_pi fun k => continuous_pi fun l => ?_
  split_ifs
  all_goals fun_prop

-- lem:coordinate-rotation-orthogonal: Problem1.planeRotation_action_continuous
theorem planeRotation_action_continuous (d : ℕ) (p : SphereRotationPair d) (x : Sphere d) :
  Continuous (fun t : ℝ => sphereAction (planeRotation d p t) x) := by
  exact (sphereActionN_joint_continuous (d + 1)).comp
    (f := fun t : ℝ => (planeRotation d p t, x))
    ((planeRotation_continuous d p).prodMk continuous_const)

-- lem:coordinate-rotation-orthogonal: Problem1.planeRotation_apply
theorem planeRotation_apply (d : ℕ) (p : SphereRotationPair d) (t : ℝ) (z : Euclidean d) (k : Fin (d + 1)) :
  orthogonalLin (planeRotation d p t) z k = if k = p.1.1 then z p.1.1 * Real.cos t - z p.1.2 * Real.sin t else if k = p.1.2 then z p.1.1 * Real.sin t + z p.1.2 * Real.cos t else z k := by
  rw [orthogonalLin_apply_coordinate]
  simp +contextual [planeRotation, planeRotationMatrix, ite_mul, Finset.sum_ite,
    Finset.filter_eq', (ne_of_lt p.2).symm, sub_eq_add_neg, mul_comm]

-- lem:coordinate-rotation-orthogonal: Problem1.planeRotation_sphere_apply
theorem planeRotation_sphere_apply (d : ℕ) (p : SphereRotationPair d) (t : ℝ) (x : Sphere d) (k : Fin (d + 1)) :
  (sphereAction (planeRotation d p t) x : Euclidean d) k = if k = p.1.1 then (x : Euclidean d) p.1.1 * Real.cos t - (x : Euclidean d) p.1.2 * Real.sin t else if k = p.1.2 then (x : Euclidean d) p.1.1 * Real.sin t + (x : Euclidean d) p.1.2 * Real.cos t else (x : Euclidean d) k := by
  exact planeRotation_apply d p t (x : Euclidean d) k

-- lem:coordinate-rotation-derivative: Problem1.planeRotation_coord_hasDerivAt
theorem planeRotation_coord_hasDerivAt (d : ℕ) (p : SphereRotationPair d) (x : Sphere d) (t : ℝ) (k : Fin (d + 1)) :
  HasDerivAt (fun u : ℝ => (sphereAction (planeRotation d p u) x : Euclidean d) k) (if k = p.1.1 then -(sphereAction (planeRotation d p t) x : Euclidean d) p.1.2 else if k = p.1.2 then (sphereAction (planeRotation d p t) x : Euclidean d) p.1.1 else 0) t := by
  simp only [planeRotation_sphere_apply, if_neg (ne_of_lt p.2).symm, if_true]
  split_ifs with hk₁ hk₂
  · simpa only [mul_neg, sub_eq_add_neg, neg_add] using!
      (((Real.hasDerivAt_cos t).const_mul ((x : Euclidean d) p.1.1)).sub
        ((Real.hasDerivAt_sin t).const_mul ((x : Euclidean d) p.1.2)))
  · simpa only [mul_neg, sub_eq_add_neg] using!
      (((Real.hasDerivAt_sin t).const_mul ((x : Euclidean d) p.1.1)).add
        ((Real.hasDerivAt_cos t).const_mul ((x : Euclidean d) p.1.2)))
  · exact hasDerivAt_const t ((x : Euclidean d) k)

-- lem:coordinate-rotation-derivative: Problem1.rotationU
noncomputable def rotationU (d : ℕ) (t : ℝ) (y : Sphere d) :
  ℝ := by
  classical
  exact (
    (y : Euclidean d) (0 : Fin (d + 1)) * Real.cos t - (y : Euclidean d) (1 : Fin (d + 1)) * Real.sin t
  )

-- lem:coordinate-rotation-derivative: Problem1.rotationV
noncomputable def rotationV (d : ℕ) (t : ℝ) (y : Sphere d) :
  ℝ := by
  classical
  exact (
    (y : Euclidean d) (0 : Fin (d + 1)) * Real.sin t + (y : Euclidean d) (1 : Fin (d + 1)) * Real.cos t
  )

-- lem:coordinate-rotation-derivative: Problem1.rotationIntegrand
noncomputable def rotationIntegrand (d : ℕ) (φ : Polynomial ℝ) (t : ℝ) (y : Sphere d) :
  ℝ := by
  classical
  exact (
    rotationV d t y * φ.eval (rotationU d t y)
  )

-- lem:coordinate-rotation-derivative: Problem1.rotationIntegrandDerivative
noncomputable def rotationIntegrandDerivative (d : ℕ) (φ : Polynomial ℝ) (t : ℝ) (y : Sphere d) :
  ℝ := by
  classical
  exact (
    rotationU d t y * φ.eval (rotationU d t y) - rotationV d t y ^ 2 * φ.derivative.eval (rotationU d t y)
  )

-- lem:coordinate-rotation-derivative: Problem1.rotation_integrand_hasDerivAt
theorem rotation_integrand_hasDerivAt (d : ℕ) (hd : 2 ≤ d) (φ : Polynomial ℝ) (t : ℝ) (y : Sphere d) :
  HasDerivAt (fun u => rotationIntegrand d φ u y) (rotationIntegrandDerivative d φ t y) t := by
  have hu : HasDerivAt (fun u : ℝ => rotationU d u y) (-rotationV d t y) t := by
    simpa only [rotationU, rotationV, mul_neg, sub_eq_add_neg, neg_add] using!
      (((Real.hasDerivAt_cos t).const_mul ((y : Euclidean d) 0)).sub
        ((Real.hasDerivAt_sin t).const_mul ((y : Euclidean d) 1)))
  have hv : HasDerivAt (fun u : ℝ => rotationV d u y) (rotationU d t y) t := by
    simpa only [rotationU, rotationV, mul_neg, sub_eq_add_neg] using!
      (((Real.hasDerivAt_sin t).const_mul ((y : Euclidean d) 0)).add
        ((Real.hasDerivAt_cos t).const_mul ((y : Euclidean d) 1)))
  convert! hv.mul ((φ.hasDerivAt (rotationU d t y)).comp t hu) using 1
  dsimp only [rotationIntegrandDerivative, Function.comp_apply]
  ring

-- lem:coordinate-rotation-derivative-bound: Problem1.rotation_derivative_bound
theorem rotation_derivative_bound (d : ℕ) (hd : 2 ≤ d) (φ : Polynomial ℝ) :
  (∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ) (y : Sphere d), |rotationIntegrandDerivative d φ t y| ≤ M) ∧ ∀ t : ℝ, Continuous (rotationIntegrand d φ t) ∧ Continuous (rotationIntegrandDerivative d φ t) := by
  have hdim : 1 < d + 1 := by omega
  have h01 : (0 : Fin (d + 1)) < 1 := by
    simpa only [Fin.lt_def, Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt hdim] using
      Nat.zero_lt_one
  have hcoord (z : Sphere d) (k : Fin (d + 1)) : |(z : Euclidean d) k| ≤ 1 := by
    simpa only [Real.norm_eq_abs, unitSphereN_norm] using
      PiLp.norm_apply_le (z : Euclidean d) k
  have hu (t : ℝ) (y : Sphere d) : |rotationU d t y| ≤ 1 := by
    simpa [rotationU, planeRotation_sphere_apply] using
      hcoord (sphereAction (planeRotation d ⟨(0, 1), h01⟩ t) y) 0
  have hv (t : ℝ) (y : Sphere d) : |rotationV d t y| ≤ 1 := by
    simpa [rotationV, planeRotation_sphere_apply, h01.ne.symm] using
      hcoord (sphereAction (planeRotation d ⟨(0, 1), h01⟩ t) y) 1
  obtain ⟨B0, hB0⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    φ.continuous.continuousOn
  obtain ⟨B1, hB1⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    φ.derivative.continuous.continuousOn
  have hB0_nonneg : 0 ≤ B0 :=
    (norm_nonneg (φ.eval 0)).trans (hB0 0 (by norm_num))
  have hB1_nonneg : 0 ≤ B1 :=
    (norm_nonneg (φ.derivative.eval 0)).trans (hB1 0 (by norm_num))
  refine ⟨⟨B0 + B1, add_nonneg hB0_nonneg hB1_nonneg, ?_⟩, ?_⟩
  · intro t y
    have hφ : |φ.eval (rotationU d t y)| ≤ B0 := by
      simpa only [Real.norm_eq_abs] using hB0 _ (abs_le.mp (hu t y))
    have hφ' : |φ.derivative.eval (rotationU d t y)| ≤ B1 := by
      simpa only [Real.norm_eq_abs] using hB1 _ (abs_le.mp (hu t y))
    have hvsq : |rotationV d t y| ^ 2 ≤ 1 := by
      simpa only [one_pow] using
        pow_le_pow_left₀ (abs_nonneg (rotationV d t y)) (hv t y) 2
    have htri : |rotationIntegrandDerivative d φ t y| ≤
        |rotationU d t y| * |φ.eval (rotationU d t y)| +
          |rotationV d t y| ^ 2 * |φ.derivative.eval (rotationU d t y)| := by
      simpa only [rotationIntegrandDerivative, Real.norm_eq_abs, abs_mul, abs_pow] using
        norm_sub_le
          (rotationU d t y * φ.eval (rotationU d t y))
          (rotationV d t y ^ (2 : ℕ) * φ.derivative.eval (rotationU d t y))
    exact htri.trans (by
      simpa only [one_mul] using
        add_le_add
          (mul_le_mul (hu t y) hφ (abs_nonneg _) zero_le_one)
          (mul_le_mul hvsq hφ' (abs_nonneg _) zero_le_one))
  · have hc (k : Fin (d + 1)) : Continuous (fun y : Sphere d => (y : Euclidean d) k) :=
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin (d + 1) => ℝ) k).comp
        continuous_subtype_val
    have hU (t : ℝ) : Continuous (rotationU d t) :=
      ((hc 0).mul_const (Real.cos t)).sub ((hc 1).mul_const (Real.sin t))
    have hV (t : ℝ) : Continuous (rotationV d t) :=
      ((hc 0).mul_const (Real.sin t)).add ((hc 1).mul_const (Real.cos t))
    exact fun t =>
      ⟨(hV t).mul (φ.continuous.comp (hU t)),
        ((hU t).mul (φ.continuous.comp (hU t))).sub
          (((hV t).pow 2).mul (φ.derivative.continuous.comp (hU t)))⟩

-- lem:rotation-integral-derivative: Problem1.rotation_integral_hasDerivAt
theorem rotation_integral_hasDerivAt (d : ℕ) (hd : 2 ≤ d) (φ : Polynomial ℝ) :
  Integrable (rotationIntegrandDerivative d φ 0) (sigma d) ∧ HasDerivAt (fun t : ℝ => ∫ y, rotationIntegrand d φ t y ∂sigma d) (∫ y, rotationIntegrandDerivative d φ 0 y ∂sigma d) 0 := by
  obtain ⟨⟨M, hM_nonneg, hM⟩, hc⟩ := rotation_derivative_bound d hd φ
  have hI : Integrable (rotationIntegrand d φ 0) (sigma d) :=
    integrableOn_univ.mp ((hc 0).1.continuousOn.integrableOn_compact isCompact_univ)
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.Ioo (-1 : ℝ) 1) (bound := fun _ : Sphere d => M)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun t => (hc t).1.aestronglyMeasurable)
    hI (hc 0).2.aestronglyMeasurable ?_ (integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun y t _ => hM t y
  · exact Filter.Eventually.of_forall fun y t _ => rotation_integrand_hasDerivAt d hd φ t y

-- lem:rotation-integral-derivative: Problem1.rotation_integral_derivative
theorem rotation_integral_derivative (d : ℕ) (hd : 2 ≤ d) (φ : Polynomial ℝ) :
  deriv (fun t : ℝ => ∫ y, rotationIntegrand d φ t y ∂sigma d) 0 = ∫ y, ((y : Euclidean d) 0 * φ.eval ((y : Euclidean d) 0) - (y : Euclidean d) 1 ^ 2 * φ.derivative.eval ((y : Euclidean d) 0)) ∂sigma d := by
  simpa only [rotationIntegrandDerivative, rotationU, rotationV, Real.cos_zero,
    Real.sin_zero, mul_one, mul_zero, sub_zero, zero_add] using
      (rotation_integral_hasDerivAt d hd φ).2.deriv

-- lem:rotation-ibp: Problem1.rotation_ibp
theorem rotation_ibp (d : ℕ) (hd : 2 ≤ d) (φ : Polynomial ℝ) :
  (∫ y : Sphere d, (y : Euclidean d) 0 * φ.eval ((y : Euclidean d) 0) ∂sigma d) = ∫ y : Sphere d, (y : Euclidean d) 1 ^ 2 * φ.derivative.eval ((y : Euclidean d) 0) ∂sigma d := by
  have h01 : (0 : Fin (d + 1)) < 1 := by
    simpa only [Fin.lt_def, Fin.val_zero, Fin.val_one',
      Nat.mod_eq_of_lt (show 1 < d + 1 by omega)] using Nat.zero_lt_one
  have hc (k : Fin (d + 1)) : Continuous (fun y : Sphere d => (y : Euclidean d) k) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin (d + 1) => ℝ) k).comp
      continuous_subtype_val
  have hbase : Integrable (fun y : Sphere d =>
      (y : Euclidean d) 1 * φ.eval ((y : Euclidean d) 0)) (sigma d) :=
    integrableOn_univ.mp
      (((hc 1).mul (φ.continuous.comp (hc 0))).continuousOn.integrableOn_compact isCompact_univ)
  have hconst (t : ℝ) : (∫ y, rotationIntegrand d φ t y ∂sigma d) =
      ∫ y : Sphere d, (y : Euclidean d) 1 * φ.eval ((y : Euclidean d) 0) ∂sigma d := by
    simpa [rotationIntegrand, rotationU, rotationV, planeRotation_sphere_apply, h01.ne.symm] using
      sigma_integral_sphereAction (planeRotation d ⟨(0, 1), h01⟩ t)
        (fun y : Sphere d => (y : Euclidean d) 1 * φ.eval ((y : Euclidean d) 0)) hbase
  have hzero : deriv (fun t : ℝ => ∫ y, rotationIntegrand d φ t y ∂sigma d) 0 = 0 := by
    simp only [hconst, deriv_const]
  have hA : Integrable (fun y : Sphere d =>
      (y : Euclidean d) 0 * φ.eval ((y : Euclidean d) 0)) (sigma d) :=
    integrableOn_univ.mp
      (((hc 0).mul (φ.continuous.comp (hc 0))).continuousOn.integrableOn_compact isCompact_univ)
  have hB : Integrable (fun y : Sphere d =>
      (y : Euclidean d) 1 ^ 2 * φ.derivative.eval ((y : Euclidean d) 0)) (sigma d) :=
    integrableOn_univ.mp
      ((((hc 1).pow 2).mul (φ.derivative.continuous.comp (hc 0))).continuousOn.integrableOn_compact
        isCompact_univ)
  exact sub_eq_zero.mp (by
    simpa only [integral_sub hA hB] using
      (rotation_integral_derivative d hd φ).symm.trans hzero)

-- lem:coordinate-permutation-integrals: Problem1.coordinate_permutation_integrals
theorem coordinate_permutation_integrals (d : ℕ) (hd : 2 ≤ d) (ψ : Polynomial ℝ) (j : Fin (d + 1)) (hj : 1 ≤ j.val) :
  Integrable (fun y : Sphere d => (y : Euclidean d) j ^ 2 * ψ.eval ((y : Euclidean d) 0)) (sigma d) ∧ Integrable (fun y : Sphere d => (y : Euclidean d) 1 ^ 2 * ψ.eval ((y : Euclidean d) 0)) (sigma d) ∧ Integrable (fun y : Sphere d => (1 - (y : Euclidean d) 0 ^ 2) * ψ.eval ((y : Euclidean d) 0)) (sigma d) ∧ (∫ y : Sphere d, (y : Euclidean d) j ^ 2 * ψ.eval ((y : Euclidean d) 0) ∂sigma d) = (∫ y : Sphere d, (y : Euclidean d) 1 ^ 2 * ψ.eval ((y : Euclidean d) 0) ∂sigma d) ∧ (d : ℝ) * (∫ y : Sphere d, (y : Euclidean d) 1 ^ 2 * ψ.eval ((y : Euclidean d) 0) ∂sigma d) = ∫ y : Sphere d, (1 - (y : Euclidean d) 0 ^ 2) * ψ.eval ((y : Euclidean d) 0) ∂sigma d := by
  have hc (k : Fin (d + 1)) : Continuous (fun y : Sphere d => (y : Euclidean d) k) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin (d + 1) => ℝ) k).comp
      continuous_subtype_val
  have hI (k : Fin (d + 1)) : Integrable (fun y : Sphere d =>
      (y : Euclidean d) k ^ 2 * ψ.eval ((y : Euclidean d) 0)) (sigma d) :=
    integrableOn_univ.mp
      ((((hc k).pow 2).mul (ψ.continuous.comp (hc 0))).continuousOn.integrableOn_compact
        isCompact_univ)
  have hJ : Integrable (fun y : Sphere d =>
      (1 - (y : Euclidean d) 0 ^ 2) * ψ.eval ((y : Euclidean d) 0)) (sigma d) :=
    integrableOn_univ.mp
      (((continuous_const.sub ((hc 0).pow 2)).mul (ψ.continuous.comp (hc 0))).continuousOn.integrableOn_compact
        isCompact_univ)
  have hperm (p : Equiv.Perm (Fin (d + 1))) : p.permMatrix ℝ ∈ Orthogonal d := by
    simp only [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_permMatrix,
      ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  have hact (p : Equiv.Perm (Fin (d + 1))) (y : Sphere d) (k : Fin (d + 1)) :
      (sphereAction ⟨p.permMatrix ℝ, hperm p⟩ y : Euclidean d) k = (y : Euclidean d) (p k) := by
    simpa only [sphereAction, sphereActionN_coe, orthogonalLin_apply_coordinate,
      Matrix.mulVec, dotProduct, Function.comp_apply] using
        congrFun (Matrix.permMatrix_mulVec (R := ℝ) p
          (v := fun i => (y : Euclidean d) i)) k
  have h01 : (0 : Fin (d + 1)) < 1 := by
    simpa only [Fin.lt_def, Fin.val_zero, Fin.val_one',
      Nat.mod_eq_of_lt (show 1 < d + 1 by omega)] using Nat.zero_lt_one
  have hEq (k : Fin (d + 1)) (hk : 1 ≤ k.val) :
      (∫ y : Sphere d, (y : Euclidean d) k ^ 2 * ψ.eval ((y : Euclidean d) 0) ∂sigma d) =
        ∫ y : Sphere d, (y : Euclidean d) 1 ^ 2 * ψ.eval ((y : Euclidean d) 0) ∂sigma d := by
    simpa only [hact, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (a := (1 : Fin (d + 1))) (b := k) (x := 0) h01.ne
        (fun h => (ne_of_lt (lt_of_lt_of_le Nat.zero_lt_one hk)) (congrArg Fin.val h))] using
        sigma_integral_sphereAction
          ⟨(Equiv.swap (1 : Fin (d + 1)) k).permMatrix ℝ, hperm _⟩
          (fun y : Sphere d => (y : Euclidean d) 1 ^ (2 : ℕ) * ψ.eval ((y : Euclidean d) 0))
          (hI 1)
  have htotal (y : Sphere d) : (∑ k : Fin (d + 1), (y : Euclidean d) k ^ 2) = 1 := by
    simpa only [unitSphereN_norm, one_pow, Real.norm_eq_abs, sq_abs] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin (d + 1) => ℝ) (y : Euclidean d)).symm
  have hsq (y : Sphere d) : (∑ k : Fin d, (y : Euclidean d) k.succ ^ 2) =
      1 - (y : Euclidean d) 0 ^ 2 := by
    exact eq_sub_iff_add_eq.mpr (by
      simpa only [Fin.sum_univ_succ, add_comm] using htotal y)
  have hsum : (∫ y : Sphere d, (1 - (y : Euclidean d) 0 ^ 2) *
      ψ.eval ((y : Euclidean d) 0) ∂sigma d) =
      ∑ k : Fin d, ∫ y : Sphere d, (y : Euclidean d) k.succ ^ 2 *
        ψ.eval ((y : Euclidean d) 0) ∂sigma d := by
    simpa only [← Finset.sum_mul, hsq] using
      integral_finsetSum (Finset.univ : Finset (Fin d)) (fun k _ => hI k.succ)
  exact ⟨hI j, hI 1, hJ, hEq j hj, by
    simpa [hEq, nsmul_eq_mul] using hsum.symm⟩

-- lem:coordinate-stein: Problem1.coordinate_stein
theorem coordinate_stein (d : ℕ) (hd : 2 ≤ d) (φ : Polynomial ℝ) :
  (∫ t, t * φ.eval t ∂coordinateLawMeasure d) = (1 / (d : ℝ)) * ∫ t, (1 - t ^ 2) * φ.derivative.eval t ∂coordinateLawMeasure d := by
  have hmap (f : ℝ → ℝ) (hf : Continuous f) :
      (∫ t, f t ∂coordinateLawMeasure d) =
        ∫ y : Sphere d, f ((y : Euclidean d) 0) ∂sigma d := by
    simpa only [coordinateLawMeasure, sphereCoordinate_north_apply] using
      integral_map (μ := sigma d)
        (sphereCoordinate_continuous d (northPole d)).measurable.aemeasurable
        hf.aestronglyMeasurable
  have h1 : 1 ≤ (1 : Fin (d + 1)).val := by
    simpa only [Fin.val_one', Nat.mod_eq_of_lt (show 1 < d + 1 by omega)] using
      Nat.le_refl 1
  have hsum := (coordinate_permutation_integrals d hd φ.derivative 1 h1).2.2.2.2
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by omega)
  rw [hmap (fun t : ℝ => t * φ.eval t) (continuous_id.mul φ.continuous),
    hmap (fun t : ℝ => (1 - t ^ (2 : ℕ)) * φ.derivative.eval t)
      ((continuous_const.sub (continuous_id.pow 2)).mul φ.derivative.continuous),
    rotation_ibp d hd φ, ← hsum]
  simp [one_div, hd0]

-- def:coordinate-moments: Problem1.coordinateMoment
noncomputable def coordinateMoment (d k : ℕ) :
  ℝ := by
  classical
  exact (
    ∫ t : ℝ, t ^ k ∂coordinateLawMeasure d
  )

-- def:coordinate-moments: Problem1.candidateCoordinateMoment
noncomputable def candidateCoordinateMoment (d k : ℕ) :
  ℝ := by
  classical
  exact (
    ∫ t : ℝ, t ^ k ∂candidateCoordinateMeasure d
  )

-- lem:coordinate-moment-recursion: Problem1.coordinate_moment_recursion
theorem coordinate_moment_recursion (d : ℕ) (hd : 2 ≤ d) :
  coordinateMoment d 0 = 1 ∧ coordinateMoment d 1 = 0 ∧ ∀ k : ℕ, 1 ≤ k → coordinateMoment d (k + 1) = ((k : ℝ) / ((d : ℝ) + k)) * coordinateMoment d (k - 1) := by
  letI := (coordinate_law_probability d hd).1
  have h0 : coordinateMoment d 0 = 1 := by
    simp [coordinateMoment]
  have h1 : coordinateMoment d 1 = 0 := by
    simpa [coordinateMoment] using coordinate_stein d hd (1 : Polynomial ℝ)
  have hInt (n : ℕ) : Integrable (fun t : ℝ => t ^ n) (coordinateLawMeasure d) := by
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
      (coordinate_polynomial_integrable d hd ((Polynomial.X : Polynomial ℝ) ^ n)).1
  refine ⟨h0, h1, fun k hk => ?_⟩
  have hStein : (∫ t : ℝ, t ^ (k + 1) ∂coordinateLawMeasure d) =
      (1 / (d : ℝ)) * ∫ t : ℝ, (1 - t ^ (2 : ℕ)) *
        ((k : ℝ) * t ^ (k - 1)) ∂coordinateLawMeasure d := by
    simpa only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, ← pow_succ'] using
        coordinate_stein d hd ((Polynomial.X : Polynomial ℝ) ^ k)
  have hpow (t : ℝ) : t ^ (2 : ℕ) * t ^ (k - 1) = t ^ (k + 1) := by
    rw [← pow_add, show 2 + (k - 1) = k + 1 by omega]
  have hpoly (t : ℝ) : (1 - t ^ (2 : ℕ)) * ((k : ℝ) * t ^ (k - 1)) =
      (k : ℝ) * (t ^ (k - 1) - t ^ (k + 1)) := by
    rw [← hpow t]
    ring
  have hrec : coordinateMoment d (k + 1) = (1 / (d : ℝ)) *
      ((k : ℝ) * (coordinateMoment d (k - 1) - coordinateMoment d (k + 1))) := by
    simpa only [hpoly, integral_const_mul, integral_sub (hInt (k - 1)) (hInt (k + 1)),
      coordinateMoment] using hStein
  have hnonzero : (d : ℝ) ≠ 0 ∧ (d : ℝ) + k ≠ 0 := by
    exact ⟨by exact_mod_cast (show d ≠ 0 by omega),
      by exact_mod_cast (show d + k ≠ 0 by omega)⟩
  field_simp [hnonzero.1, hnonzero.2] at hrec ⊢
  linear_combination hrec

-- lem:moment-recursion-unique: Problem1.moment_recursion_unique
theorem moment_recursion_unique (d : ℕ) (hd : 2 ≤ d) (a b : ℕ → ℝ) (h0 : a 0 = b 0) (h1 : a 1 = b 1) (ha : ∀ k : ℕ, 1 ≤ k → a (k + 1) = ((k : ℝ) / ((d : ℝ) + k)) * a (k - 1)) (hb : ∀ k : ℕ, 1 ≤ k → b (k + 1) = ((k : ℝ) / ((d : ℝ) + k)) * b (k - 1)) :
  a = b := by
  refine funext (Nat.twoStepInduction h0 h1 (fun n hn _ => ?_))
  simp [ha (n + 1) (Nat.succ_pos n), hb (n + 1) (Nat.succ_pos n), hn]

-- lem:candidate-odd-moments: Problem1.candidate_odd_moments
theorem candidate_odd_moments (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
  candidateCoordinateMoment d (2 * r + 1) = 0 := by
  have hInt : Integrable (fun t : ℝ => t ^ (2 * r + 1)) (candidateCoordinateMeasure d) := by
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
      (coordinate_polynomial_integrable d hd ((Polynomial.X : Polynomial ℝ) ^ (2 * r + 1))).2
  have hIw := (candidate_integrability_iff d hd _
    (continuous_id.pow (2 * r + 1)).measurable).mp hInt
  rw [candidateCoordinateMoment, candidate_integral d hd (fun t : ℝ => t ^ (2 * r + 1))
    (continuous_id.pow (2 * r + 1)).measurable hIw]
  have hflip : (∫ t in Set.Icc (-1 : ℝ) 1,
      (-t) ^ (2 * r + 1) * coordinateWeight d (-t)) =
      ∫ t in Set.Icc (-1 : ℝ) 1, t ^ (2 * r + 1) * coordinateWeight d t := by
    simpa only [neg_neg, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] using
      (intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
        (fun t : ℝ => t ^ (2 * r + 1) * coordinateWeight d t))
  have hodd (t : ℝ) : (-t) ^ (2 * r + 1) * coordinateWeight d (-t) =
      -(t ^ (2 * r + 1) * coordinateWeight d t) := by
    simp only [(coordinate_even d r t).1, pow_add, pow_mul, neg_sq, pow_one, mul_neg, neg_mul]
  simp only [hodd, integral_neg] at hflip
  simp [show (∫ t in Set.Icc (-1 : ℝ) 1,
    t ^ (2 * r + 1) * coordinateWeight d t) = 0 by linarith]

-- lem:candidate-even-moments: Problem1.candidate_even_moments
theorem candidate_even_moments (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
  candidateCoordinateMoment d (2 * r) = coordinateNormConst d * ProbabilityTheory.beta ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) ∧ candidateCoordinateMoment d (2 * r) = ProbabilityTheory.beta ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) / ProbabilityTheory.beta (1 / 2) ((d : ℝ) / 2) := by
  have h : candidateCoordinateMoment d (2 * r) =
      coordinateNormConst d * ProbabilityTheory.beta ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) := by
    rw [candidateCoordinateMoment, candidate_integral d hd (fun t : ℝ => t ^ (2 * r))
      (continuous_id.pow (2 * r)).measurable (coordinate_moment d r hd).1,
      (coordinate_moment d r hd).2]
  exact ⟨h, by simpa only [coordinateNormConst, (coordinate_normalizer_positive d hd).1,
    div_eq_mul_inv, mul_comm] using h⟩

-- lem:coordinate-candidate-moments: Problem1.coordinate_candidate_moments
theorem coordinate_candidate_moments (d : ℕ) (hd : 2 ≤ d) (k : ℕ) :
  candidateCoordinateMoment d k = coordinateMoment d k := by
  have hdim : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast (show 0 < d by omega)) (by norm_num)
  have h0 : candidateCoordinateMoment d 0 = 1 := by
    simpa only [mul_zero, Nat.cast_zero, zero_add,
      div_self (ne_of_gt (beta_positive (1 / 2) ((d : ℝ) / 2) (by norm_num) hdim))] using
      (candidate_even_moments d hd 0).2
  have h1 : candidateCoordinateMoment d 1 = 0 := by
    simpa only [mul_zero, zero_add] using candidate_odd_moments d hd 0
  suffices hrec : ∀ n : ℕ, 1 ≤ n → candidateCoordinateMoment d (n + 1) =
      ((n : ℝ) / ((d : ℝ) + n)) * candidateCoordinateMoment d (n - 1) by
    exact congrFun (moment_recursion_unique d hd _ _
      (h0.trans (coordinate_moment_recursion d hd).1.symm)
      (h1.trans (coordinate_moment_recursion d hd).2.1.symm)
      hrec (coordinate_moment_recursion d hd).2.2) k
  intro n hn
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' n
  case inr =>
    rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega,
      show 2 * r + 1 - 1 = 2 * r by omega,
      (candidate_even_moments d hd (r + 1)).1, (candidate_even_moments d hd r).1]
    rw [show ((r + 1 : ℕ) : ℝ) + 1 / 2 = ((r : ℝ) + 1 / 2) + 1 by
      simp only [Nat.cast_add, Nat.cast_one, add_right_comm],
      beta_recurrence_left ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) (by positivity) hdim]
    push_cast
    field_simp
    ring
  case inl =>
    simp only [show 2 * r - 1 = 2 * (r - 1) + 1 by omega,
      candidate_odd_moments d hd, mul_zero]

-- lem:coordinate-polynomial-tests: Problem1.coordinate_polynomial_tests
theorem coordinate_polynomial_tests (d : ℕ) (hd : 2 ≤ d) (P : Polynomial ℝ) :
  (∫ t, P.eval t ∂coordinateLawMeasure d) = ∫ t, P.eval t ∂candidateCoordinateMeasure d := by
  refine Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)
  · simp only [Polynomial.eval_add,
      integral_add (coordinate_polynomial_integrable d hd p).1
        (coordinate_polynomial_integrable d hd q).1,
      integral_add (coordinate_polynomial_integrable d hd p).2
        (coordinate_polynomial_integrable d hd q).2, hp, hq]
  · simpa only [Polynomial.eval_monomial, integral_const_mul,
      coordinateMoment, candidateCoordinateMoment] using
      congrArg (fun m : ℝ => a * m) (coordinate_candidate_moments d hd n).symm

-- lem:compact-test-error: Problem1.compact_test_error
theorem compact_test_error (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0) (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) (hfB : BddAbove ((fun t => |f t|) '' Set.Icc (-1 : ℝ) 1)) (hgB : BddAbove ((fun t => |g t|) '' Set.Icc (-1 : ℝ) 1)) (ε : ℝ) (hε : 0 ≤ ε) (hfg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t - g t| ≤ ε) :
  Integrable f μ ∧ Integrable g μ ∧ |(∫ t, f t ∂μ) - ∫ t, g t ∂μ| ≤ ε := by
  have hmem : ∀ᵐ t ∂μ, t ∈ Set.Icc (-1 : ℝ) 1 := ae_iff.mpr hμ
  have hInt (u : ℝ → ℝ) (hu : Measurable u)
      (huB : BddAbove ((fun t => |u t|) '' Set.Icc (-1 : ℝ) 1)) : Integrable u μ := by
    obtain ⟨C, hC⟩ := huB
    exact ⟨hu.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (hmem.mono fun t ht => by
        simpa only [Real.norm_eq_abs] using hC ⟨t, ht, rfl⟩)⟩
  refine ⟨hInt f hf hfB, hInt g hg hgB, ?_⟩
  simpa [integral_sub (hInt f hf hfB) (hInt g hg hgB)] using
    (norm_integral_le_of_norm_le_const (f := fun t => f t - g t) (C := ε)
      (hmem.mono fun t ht => by simpa only [Real.norm_eq_abs] using hfg t ht))

-- lem:coordinate-continuous-tests: Problem1.coordinate_continuous_tests
theorem coordinate_continuous_tests (d : ℕ) (hd : 2 ≤ d) (f : BoundedContinuousFunction ℝ ℝ) :
  (∫ t, f t ∂coordinateLawMeasure d) = ∫ t, f t ∂candidateCoordinateMeasure d := by
  refine eq_of_forall_dist_le (fun ε hε => ?_)
  obtain ⟨Q, hQ⟩ := exists_polynomial_near_of_continuousOn (-1) 1 f
    f.continuous.continuousOn (ε / 2) (half_pos hε)
  have hError (μ : Measure ℝ) [IsProbabilityMeasure μ]
      (hμ : μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0) :
      |(∫ t, f t ∂μ) - ∫ t, Q.eval t ∂μ| ≤ ε / 2 := by
    exact (compact_test_error μ hμ f (fun t => Q.eval t)
      f.continuous.measurable Q.continuous.measurable
      (isCompact_Icc.bddAbove_image f.continuous.abs.continuousOn)
      (isCompact_Icc.bddAbove_image Q.continuous.abs.continuousOn)
      (ε / 2) (half_pos hε).le (fun t ht => by
        simpa only [abs_sub_comm] using (hQ t ht).le)).2.2
  have hErrors := And.intro
    (@hError (coordinateLawMeasure d) (coordinate_law_probability d hd).1
      (coordinate_law_probability d hd).2.2)
    (@hError (candidateCoordinateMeasure d) (candidate_isProbabilityMeasure d hd)
      (candidate_measure_concentrated d hd))
  calc
    dist (∫ t, f t ∂coordinateLawMeasure d) (∫ t, f t ∂candidateCoordinateMeasure d) ≤
        dist (∫ t, f t ∂coordinateLawMeasure d) (∫ t, Q.eval t ∂coordinateLawMeasure d) +
        dist (∫ t, Q.eval t ∂coordinateLawMeasure d) (∫ t, f t ∂candidateCoordinateMeasure d) :=
      dist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add
      (by simpa only [Real.dist_eq] using hErrors.1)
      (by simpa only [Real.dist_eq, coordinate_polynomial_tests d hd Q, abs_sub_comm]
        using hErrors.2)
    _ = ε := add_halves ε

-- lem:coordinate-measure-equality: Problem1.coordinate_measure_equality
theorem coordinate_measure_equality (d : ℕ) (hd : 2 ≤ d) :
  coordinateLawMeasure d = candidateCoordinateMeasure d := by
  letI := (coordinate_law_probability d hd).1
  letI := candidate_isProbabilityMeasure d hd
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure (coordinate_continuous_tests d hd)

-- lem:coordinate-law-north: Problem1.coordinate_law_north_integrable_iff
theorem coordinate_law_north_integrable_iff (d : ℕ) (hd : 2 ≤ d) (F : ℝ → ℝ) (hF : Measurable F) :
  Integrable (fun y => F (sphereCoordinate d (northPole d) y)) (sigma d) ↔ IntegrableOn (fun t => F t * coordinateWeight d t) (Set.Icc (-1 : ℝ) 1) volume := by
  rw [← candidate_integrability_iff d hd F hF, ← coordinate_measure_equality d hd]
  exact (integrable_map_measure (μ := sigma d) hF.aestronglyMeasurable
    (sphereCoordinate_continuous d (northPole d)).measurable.aemeasurable).symm

-- lem:coordinate-law-north: Problem1.coordinate_law_north
theorem coordinate_law_north (d : ℕ) (hd : 2 ≤ d) (F : ℝ → ℝ) (hF : Measurable F) (hFw : IntegrableOn (fun t => F t * coordinateWeight d t) (Set.Icc (-1 : ℝ) 1) volume) :
  (∫ y, F (sphereCoordinate d (northPole d) y) ∂sigma d) = coordinateNormConst d * ∫ t in Set.Icc (-1 : ℝ) 1, F t * coordinateWeight d t ∂volume := by
  rw [← candidate_integral d hd F hF hFw, ← coordinate_measure_equality d hd]
  exact (integral_map (μ := sigma d)
    (sphereCoordinate_continuous d (northPole d)).measurable.aemeasurable
    hF.aestronglyMeasurable).symm

-- eq:coordinate-law, lem:coordinate-law: Problem1.coordinate_law_integrable_iff
theorem coordinate_law_integrable_iff (d : ℕ) (hd : 2 ≤ d) (x : Sphere d) (F : ℝ → ℝ) (hF : Measurable F) :
  Integrable (fun y => F (sphereCoordinate d x y)) (sigma d) ↔ IntegrableOn (fun t => F t * coordinateWeight d t) (Set.Icc (-1 : ℝ) 1) volume := by
  obtain ⟨U, hU⟩ := orthogonal_north_transitive (d + 1) (Nat.succ_pos d) x
  have hcoord (y : Sphere d) : sphereCoordinate d x (sphereAction U y) =
      sphereCoordinate d (northPole d) y := by
    simpa only [sphereCoordinate, ← hU, sphereAction, sphereActionN_coe, northPole] using
      orthogonalLin_inner U (northPole d : Euclidean d) (y : Euclidean d)
  rw [← coordinate_law_north_integrable_iff d hd F hF]
  simpa only [Function.comp_def, hcoord] using
    (integrable_sphereAction_iff U (fun y => F (sphereCoordinate d x y))).symm

-- eq:coordinate-law, lem:coordinate-law: Problem1.coordinate_law
theorem coordinate_law (d : ℕ) (hd : 2 ≤ d) (x : Sphere d) (F : ℝ → ℝ) (hF : Measurable F) (hFw : IntegrableOn (fun t => F t * coordinateWeight d t) (Set.Icc (-1 : ℝ) 1) volume) :
  (∫ y, F (sphereCoordinate d x y) ∂sigma d) = coordinateNormConst d * ∫ t in Set.Icc (-1 : ℝ) 1, F t * coordinateWeight d t ∂volume := by
  obtain ⟨U, hU⟩ := orthogonal_north_transitive (d + 1) (Nat.succ_pos d) x
  have hcoord (y : Sphere d) : sphereCoordinate d x (sphereAction U y) =
      sphereCoordinate d (northPole d) y := by
    simpa only [sphereCoordinate, ← hU, sphereAction, sphereActionN_coe, northPole] using
      orthogonalLin_inner U (northPole d : Euclidean d) (y : Euclidean d)
  rw [← coordinate_law_north d hd F hF hFw]
  simpa only [hcoord] using
    (sigma_integral_sphereAction U (fun y => F (sphereCoordinate d x y))
      ((coordinate_law_integrable_iff d hd x F hF).mpr hFw)).symm

-- lem:cap-geometry: Problem1.sphere_dist_sq
theorem sphere_dist_sq (d : ℕ) (x y : Sphere d) :
  dist x y ^ 2 = 2 * (1 - sphereCoordinate d x y) := by
  rw [unitSphereN_dist_eq, norm_sub_sq_real, unitSphereN_norm, unitSphereN_norm]
  dsimp only [sphereCoordinate]
  ring

-- lem:cap-geometry: Problem1.cap_geometry
theorem cap_geometry (d : ℕ) (x y : Sphere d) (r : ℝ) (hr : 0 < r) (hr2 : r ≤ 2) :
  (dist x y ≤ r ↔ 1 - r ^ 2 / 2 ≤ sphereCoordinate d x y) ∧ 1 - r ^ 2 / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · rw [← sq_le_sq₀ dist_nonneg hr.le, sphere_dist_sq]
    constructor <;> intro h <;> linarith
  · have hsq := (sq_le_sq₀ hr.le (by norm_num : (0 : ℝ) ≤ 2)).mpr hr2
    constructor <;> nlinarith [sq_nonneg r]

-- lem:cap-integral: Problem1.cap_integral
theorem cap_integral (d : ℕ) (hd : 2 ≤ d) (x : Sphere d) (r : ℝ) (hr : 0 < r) (hr2 : r ≤ 2) :
  (sigma d {y | dist x y ≤ r}).toReal = coordinateNormConst d * ∫ t in Set.Icc (1 - r ^ 2 / 2) 1, Real.rpow (1 - t ^ 2) (coordinateExponent d) ∂volume := by
  have hw : IntegrableOn (coordinateWeight d) (Set.Icc (-1 : ℝ) 1) volume := by
    simpa using (coordinate_weight_beta d 0 hd).1
  let F : ℝ → ℝ := (Set.Icc (1 - r ^ 2 / 2) 1).indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator measurableSet_Icc
  have hFw : IntegrableOn (fun t => F t * coordinateWeight d t)
      (Set.Icc (-1 : ℝ) 1) volume := by
    simpa only [F, ← Set.indicator_mul_left, one_mul] using hw.indicator measurableSet_Icc
  have hpre : sphereCoordinate d x ⁻¹' Set.Icc (1 - r ^ 2 / 2) 1 =
      {y | dist x y ≤ r} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq,
      ← (cap_geometry d x y r hr hr2).1,
      (abs_le.mp (sphereCoordinate_abs_le_one d x y)).2, and_true]
  have hmeas : MeasurableSet {y | dist x y ≤ r} :=
    hpre ▸ measurableSet_Icc.preimage (sphereCoordinate_continuous d x).measurable
  have hmass : (∫ y, F (sphereCoordinate d x y) ∂sigma d) =
      (sigma d {y | dist x y ≤ r}).toReal := by
    simpa only [F, ← Set.indicator_comp_right, Function.comp_def, hpre,
      Measure.real, smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := sigma d) (1 : ℝ) hmeas)
  rw [← hmass, coordinate_law d hd x F hF hFw]
  simp only [F, ← Set.indicator_mul_left, one_mul, setIntegral_indicator measurableSet_Icc]
  rw [Set.inter_eq_right.mpr
    (Set.Icc_subset_Icc (cap_geometry d x x r hr hr2).2.1 le_rfl)]
  refine congrArg (fun z => coordinateNormConst d * z) (setIntegral_congr_fun measurableSet_Icc ?_)
  exact fun t ht => if_pos (Set.Icc_subset_Icc (cap_geometry d x x r hr hr2).2.1 le_rfl ht)

-- lem:cap-scalar-bound: Problem1.cap_scalar_bound
theorem cap_scalar_bound (d : ℕ) (hd : 2 ≤ d) (r : ℝ) (hr : 0 < r) (hr2 : r ≤ 2) :
  IntegrableOn (fun t : ℝ => Real.rpow (1 - t ^ 2) (coordinateExponent d)) (Set.Icc (1 - r ^ 2 / 2) 1) volume ∧ (∫ t in Set.Icc (1 - r ^ 2 / 2) 1, Real.rpow (1 - t ^ 2) (coordinateExponent d) ∂volume) ≤ r ^ d / (d : ℝ) := by
  have ha := (coordinate_parameters d 0 hd).1
  have hf : Continuous (fun t : ℝ => Real.rpow (1 - t ^ 2) (coordinateExponent d)) :=
    (Real.continuous_rpow_const ha).comp (continuous_const.sub (continuous_id.pow 2))
  refine ⟨hf.integrableOn_Icc, ?_⟩
  have hg : Continuous (fun t : ℝ => Real.rpow (2 - 2 * t) (coordinateExponent d)) :=
    (Real.continuous_rpow_const ha).comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hab : 1 - r ^ 2 / 2 ≤ 1 := by nlinarith [sq_nonneg r]
  have hvalue : (∫ t in Set.Icc (1 - r ^ 2 / 2) 1,
      Real.rpow (2 - 2 * t) (coordinateExponent d) ∂volume) = r ^ d / (d : ℝ) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_comp_sub_mul (fun t : ℝ => Real.rpow t (coordinateExponent d))
        (by norm_num : (2 : ℝ) ≠ 0) 2]
    simp only [mul_one, sub_self, show (2 : ℝ) - 2 * (1 - r ^ 2 / 2) = r ^ 2 by ring,
      Real.rpow_eq_pow,
      integral_rpow (Or.inl (by linarith : -1 < coordinateExponent d)),
      Real.zero_rpow (by linarith : coordinateExponent d + 1 ≠ 0), sub_zero, smul_eq_mul]
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, Nat.cast_ofNat,
      show (2 : ℝ) * (coordinateExponent d + 1) = (d : ℝ) by dsimp [coordinateExponent]; ring,
      Real.rpow_natCast]
    rw [show coordinateExponent d + 1 = (d : ℝ) / 2 by dsimp [coordinateExponent]; ring,
      div_div_eq_mul_div]
    ring
  refine (setIntegral_mono_on hf.integrableOn_Icc hg.integrableOn_Icc
    measurableSet_Icc (fun t ht => ?_)).trans_eq hvalue
  have ht_lower : -1 ≤ t := by
    nlinarith [ht.1, (sq_le_sq₀ hr.le (by norm_num : (0 : ℝ) ≤ 2)).mpr hr2]
  exact Real.rpow_le_rpow
    (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one t).mpr (abs_le.mpr ⟨ht_lower, ht.2⟩)))
    (by nlinarith [sq_nonneg (t - 1)]) ha

-- eq:cap-bound, lem:spherical-cap-estimate: Problem1.capConstant
noncomputable def capConstant (d : ℕ) :
  ℝ := by
  classical
  exact (
    coordinateNormConst d / (d : ℝ)
  )

-- eq:cap-bound, lem:spherical-cap-estimate: Problem1.cap_constant_positive
theorem cap_constant_positive (d : ℕ) (hd : 2 ≤ d) :
  0 < capConstant d := by
  exact div_pos (coordinate_normalizer_gamma d hd).2.1 (Nat.cast_pos.mpr (by omega))

-- eq:cap-bound, lem:spherical-cap-estimate: Problem1.spherical_cap_estimate
theorem spherical_cap_estimate (d : ℕ) (hd : 2 ≤ d) (x : Sphere d) (r : ℝ) (hr : 0 < r) (hr2 : r ≤ 2) :
  sigma d {y | dist x y ≤ r} ≤ ENNReal.ofReal (capConstant d * r ^ d) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (sigma d) {y | dist x y ≤ r})]
  apply ENNReal.ofReal_le_ofReal
  rw [cap_integral d hd x r hr hr2]
  simpa only [capConstant, div_mul_eq_mul_div, mul_div_assoc] using
    mul_le_mul_of_nonneg_left (cap_scalar_bound d hd r hr hr2).2
      (coordinate_normalizer_gamma d hd).2.1.le

-- lem:sphere-atomless: Problem1.sphere_atomless
theorem sphere_atomless (d : ℕ) (hd : 2 ≤ d) (x : Sphere d) :
  sigma d {x} = 0 := by
  have hd0 : d ≠ 0 := by omega
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
      (capConstant d * (1 / ((n : ℝ) + 1)) ^ d)) atTop (𝓝 0) := by
    simpa only [zero_pow hd0, mul_zero, ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto _).comp
        (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow d).const_mul (capConstant d))
  refine le_antisymm (ge_of_tendsto hlim (Eventually.of_forall (fun n => ?_))) bot_le
  have hr : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hr2 : 1 / ((n : ℝ) + 1) ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  refine (measure_mono ?_).trans (spherical_cap_estimate d hd x (1 / ((n : ℝ) + 1)) hr hr2)
  simpa only [Set.singleton_subset_iff, Set.mem_setOf_eq, dist_self] using hr.le

-- lem:sphere-atomless: Problem1.sphere_nullSingletonClass
theorem sphere_nullSingletonClass (d : ℕ) (hd : 2 ≤ d) :
  NullSingletonClass (sigma d) := by
  exact ⟨sphere_atomless d hd⟩

-- def:dyadic-shells: Problem1.nearShell
noncomputable def nearShell (d : ℕ) (x : Sphere d) (R : ℝ) (k : ℕ) :
  Set (Sphere d) := by
  classical
  exact (
    {y | Real.rpow 2 (-((k : ℝ) + 1)) * R < dist x y ∧ dist x y ≤ Real.rpow 2 (-(k : ℝ)) * R}
  )

-- def:dyadic-shells: Problem1.farShell
noncomputable def farShell (d : ℕ) (x : Sphere d) (R : ℝ) (k : ℕ) :
  Set (Sphere d) := by
  classical
  exact (
    {y | (2 : ℝ) ^ k * R < dist x y ∧ dist x y ≤ (2 : ℝ) ^ (k + 1) * R}
  )

-- lem:dyadic-shell-partitions: Problem1.dyadic_shell_partitions
theorem dyadic_shell_partitions (d : ℕ) (x : Sphere d) (R : ℝ) (hR : 0 < R) (hR1 : R ≤ 1) :
  (∀ k, MeasurableSet (nearShell d x R k)) ∧ Pairwise (fun k l => Disjoint (nearShell d x R k) (nearShell d x R l)) ∧ (⋃ k, nearShell d x R k) = {y | 0 < dist x y ∧ dist x y ≤ R} ∧ (∀ k, MeasurableSet (farShell d x R k)) ∧ Pairwise (fun k l => Disjoint (farShell d x R k) (farShell d x R l)) ∧ (⋃ k, farShell d x R k) = {y | R < dist x y} := by
  have hpow (k : ℕ) : Real.rpow 2 (-(k : ℝ)) = (2⁻¹ : ℝ) ^ k := by
    simp only [Real.rpow_eq_pow, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_natCast, inv_pow]
  have hnear (k : ℕ) : nearShell d x R k =
      {y | (2⁻¹ : ℝ) ^ (k + 1) * R < dist x y ∧ dist x y ≤ (2⁻¹ : ℝ) ^ k * R} := by
    simp only [nearShell, ← Nat.cast_add_one, hpow]
  have hfar_exists (ρ : ℝ) (hρ : R < ρ) :
      ∃ k : ℕ, (2 : ℝ) ^ k * R < ρ ∧ ρ ≤ (2 : ℝ) ^ (k + 1) * R := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (ρ / R) (by norm_num : (1 : ℝ) < 2)
    have hmem : ρ ∈ Set.Ioc ((2 : ℝ) ^ 0 * R) ((2 : ℝ) ^ N * R) :=
      ⟨by simpa only [pow_zero, one_mul] using hρ, ((div_lt_iff₀ hR).mp hN).le⟩
    obtain ⟨k, _, hk⟩ : ∃ k ∈ Finset.range N,
        ρ ∈ Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R) := by
      simpa only [Set.mem_iUnion, exists_prop] using
        (Ioc_subset_biUnion_Ioc N (fun k => (2 : ℝ) ^ k * R) hmem)
    exact ⟨k, hk⟩
  have hnear_exists (ρ : ℝ) (hρ0 : 0 < ρ) (hρ : ρ ≤ R) :
      ∃ k : ℕ, (2⁻¹ : ℝ) ^ (k + 1) * R < ρ ∧ ρ ≤ (2⁻¹ : ℝ) ^ k * R := by
    obtain ⟨k, hklo, hkup⟩ := exists_nat_pow_near_of_lt_one (div_pos hρ0 hR)
      ((div_le_iff₀ hR).mpr (by simpa only [one_mul] using hρ))
      (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2⁻¹ : ℝ) < 1)
    exact ⟨k, (lt_div_iff₀ hR).mp hklo, (div_le_iff₀ hR).mp hkup⟩
  have hdist : Measurable (fun y : Sphere d => dist x y) :=
    (continuous_const.dist continuous_id).measurable
  refine ⟨fun k => (measurableSet_lt measurable_const hdist).inter
    (measurableSet_le hdist measurable_const), ?_, ?_,
    fun k => (measurableSet_lt measurable_const hdist).inter
      (measurableSet_le hdist measurable_const), ?_, ?_⟩
  · simp only [Pairwise, hnear, Set.disjoint_left, Set.mem_setOf_eq]
    intro k l hkl y hk hl
    rcases lt_or_gt_of_ne hkl with hlt | hlt
    · exact hk.1.not_ge (hl.2.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2⁻¹ : ℝ) ≤ 1) (Nat.succ_le_of_lt hlt)) hR.le))
    · exact hl.1.not_ge (hk.2.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2⁻¹ : ℝ) ≤ 1) (Nat.succ_le_of_lt hlt)) hR.le))
  · ext y
    simp only [Set.mem_iUnion, hnear, Set.mem_setOf_eq]
    refine ⟨?_, fun hy => hnear_exists (dist x y) hy.1 hy.2⟩
    exact fun ⟨k, hlo, hup⟩ =>
      ⟨(mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) _) hR).trans hlo,
        hup.trans (by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
              (by norm_num : (2⁻¹ : ℝ) ≤ 1) : (2⁻¹ : ℝ) ^ k ≤ 1) hR.le)⟩
  · simp only [Pairwise, farShell, Set.disjoint_left, Set.mem_setOf_eq]
    exact fun k l hkl y hk hl => (lt_or_gt_of_ne hkl).elim
      (fun hlt => hl.1.not_ge (hk.2.trans (mul_le_mul_of_nonneg_right
        (pow_right_mono₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_of_lt hlt)) hR.le)))
      (fun hlt => hk.1.not_ge (hl.2.trans (mul_le_mul_of_nonneg_right
        (pow_right_mono₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_of_lt hlt)) hR.le)))
  · ext y
    simp only [Set.mem_iUnion, farShell, Set.mem_setOf_eq]
    exact ⟨fun ⟨k, hlo, _⟩ => lt_of_le_of_lt (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ k) hR.le) hlo,
      hfar_exists (dist x y)⟩

-- lem:near-shell-contribution: Problem1.near_shell_contribution
theorem near_shell_contribution (d : ℕ) (hd : 2 ≤ d) (α : ℝ) (hα : 0 < α) (hα2 : α < 2) (x : Sphere d) (R : ℝ) (hR : 0 < R) (hR1 : R ≤ 1) (k : ℕ) :
  (∫⁻ y in nearShell d x R k, ENNReal.ofReal (Real.rpow (dist x y) (2 - (d : ℝ) - α)) ∂sigma d) ≤ ENNReal.ofReal (capConstant d * Real.rpow 2 ((d : ℝ) + α - 2) * Real.rpow R (2 - α) * Real.rpow 2 (-((k : ℝ) * (2 - α)))) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hq : 2 - (d : ℝ) - α < 0 := by linarith
  have hrad (t : ℝ) : 0 < Real.rpow 2 t * R :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) t) hR
  have hu : Real.rpow 2 (-(k : ℝ)) * R ≤ R := by
    simpa only [Real.rpow_eq_pow, one_mul] using mul_le_mul_of_nonneg_right
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
        (neg_nonpos.mpr (Nat.cast_nonneg k) : -(k : ℝ) ≤ 0)) hR.le
  have hmass : sigma d (nearShell d x R k) ≤
      ENNReal.ofReal (capConstant d * (Real.rpow 2 (-(k : ℝ)) * R) ^ d) :=
    (measure_mono (show nearShell d x R k ⊆
        {y | dist x y ≤ Real.rpow 2 (-(k : ℝ)) * R} from fun _ hy => hy.2)).trans
      (spherical_cap_estimate d hd x _ (hrad _)
        (hu.trans (hR1.trans (by norm_num : (1 : ℝ) ≤ 2))))
  have hmajor (y : Sphere d) (hy : y ∈ nearShell d x R k) :
      ENNReal.ofReal (Real.rpow (dist x y) (2 - (d : ℝ) - α)) ≤
        ENNReal.ofReal (Real.rpow (Real.rpow 2 (-((k : ℝ) + 1)) * R)
          (2 - (d : ℝ) - α)) := by
    simpa only [Real.rpow_eq_pow] using ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (hrad _) hy.1.le hq.le)
  have hint : (∫⁻ y in nearShell d x R k,
      ENNReal.ofReal (Real.rpow (dist x y) (2 - (d : ℝ) - α)) ∂sigma d) ≤
      ENNReal.ofReal (Real.rpow (Real.rpow 2 (-((k : ℝ) + 1)) * R)
        (2 - (d : ℝ) - α)) * sigma d (nearShell d x R k) := by
    simpa only [lintegral_const, Measure.restrict_apply_univ] using
      (setLIntegral_mono (μ := sigma d) measurable_const hmajor)
  refine (hint.trans (mul_le_mul_right hmass _)).trans_eq ?_
  simp only [Real.rpow_eq_pow]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [← Real.rpow_natCast,
    Real.mul_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hR.le,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ = capConstant d *
        ((2 : ℝ) ^ (-((k : ℝ) + 1) * (2 - (d : ℝ) - α)) *
          (2 : ℝ) ^ (-(k : ℝ) * (d : ℝ))) *
        (R ^ (2 - (d : ℝ) - α) * R ^ (d : ℝ)) := by ring
    _ = capConstant d *
        (2 : ℝ) ^ (-((k : ℝ) + 1) * (2 - (d : ℝ) - α) +
          (-(k : ℝ) * (d : ℝ))) * R ^ ((2 - (d : ℝ) - α) + (d : ℝ)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_add hR]
    _ = capConstant d * (2 : ℝ) ^ (((d : ℝ) + α - 2) +
        (-((k : ℝ) * (2 - α)))) * R ^ (2 - α) := by ring_nf
    _ = _ := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring

-- lem:far-shell-contribution: Problem1.far_shell_contribution
theorem far_shell_contribution (d : ℕ) (hd : 2 ≤ d) (α : ℝ) (hα : 0 < α) (hα2 : α < 2) (x : Sphere d) (R : ℝ) (hR : 0 < R) (hR1 : R ≤ 1) (k : ℕ) :
  (∫⁻ y in farShell d x R k, ENNReal.ofReal (Real.rpow (dist x y) (-(d : ℝ) - α)) ∂sigma d) ≤ ENNReal.ofReal ((capConstant d * (2 : ℝ) ^ d + 1) * Real.rpow R (-α) * Real.rpow 2 (-((k : ℝ) * α))) := by
  simp only [Real.rpow_eq_pow]
  let a : ℝ := (2 : ℝ) ^ k * R
  have ha : 0 < a := mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) k) hR
  have hq : -(d : ℝ) - α < 0 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hdiam (y : Sphere d) : dist x y ≤ 2 := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using (unitSphereN_geometry x y).2.1
  have hscale : a ^ (-α) = R ^ (-α) * (2 : ℝ) ^ (-((k : ℝ) * α)) := by
    simp only [a, ← Real.rpow_natCast,
      Real.mul_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hR.le,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  have hmajor (y : Sphere d) (hy : y ∈ farShell d x R k) :
      ENNReal.ofReal (dist x y ^ (-(d : ℝ) - α)) ≤
        ENNReal.ofReal (a ^ (-(d : ℝ) - α)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos ha hy.1.le hq.le)
  have hint : (∫⁻ y in farShell d x R k,
      ENNReal.ofReal (dist x y ^ (-(d : ℝ) - α)) ∂sigma d) ≤
      ENNReal.ofReal (a ^ (-(d : ℝ) - α)) * sigma d (farShell d x R k) := by
    simpa only [lintegral_const, Measure.restrict_apply_univ] using
      (setLIntegral_mono (μ := sigma d) measurable_const hmajor)
  rw [mul_assoc, ← hscale]
  by_cases ha2 : 2 ≤ a
  · have hempty : farShell d x R k = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun y hy =>
        (ha2.trans_lt hy.1).not_ge (hdiam y)
    simp [hempty]
  · by_cases ha1 : a ≤ 1
    · have hsub : farShell d x R k ⊆ {y | dist x y ≤ 2 * a} := fun y hy => by
        simpa only [Set.mem_setOf_eq, a, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hy.2
      have hmass : sigma d (farShell d x R k) ≤
          ENNReal.ofReal (capConstant d * (2 * a) ^ d) :=
        (measure_mono hsub).trans
          (spherical_cap_estimate d hd x (2 * a) (by positivity) (by linarith))
      have hprod : a ^ (-(d : ℝ) - α) * (capConstant d * (2 * a) ^ d) =
          (capConstant d * (2 : ℝ) ^ d) * a ^ (-α) := by
        rw [mul_pow, ← Real.rpow_natCast a d]
        calc
          _ = (capConstant d * (2 : ℝ) ^ d) *
              (a ^ (-(d : ℝ) - α) * a ^ (d : ℝ)) := by ring
          _ = _ := by
            rw [← Real.rpow_add ha, show -(d : ℝ) - α + (d : ℝ) = -α by ring]
      refine (hint.trans (mul_le_mul_right hmass _)).trans ?_
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _), hprod]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)) (Real.rpow_nonneg ha.le _))
    · have hmass : sigma d (farShell d x R k) ≤ 1 :=
        (measure_mono (Set.subset_univ _)).trans_eq (sphere_mass_one d)
      have hpower : a ^ (-(d : ℝ) - α) ≤ a ^ (-α) :=
        Real.rpow_le_rpow_of_exponent_le (lt_of_not_ge ha1).le
          (by linarith [Nat.cast_nonneg (α := ℝ) d])
      have hC : 1 ≤ capConstant d * (2 : ℝ) ^ d + 1 :=
        le_add_of_nonneg_left (mul_nonneg (cap_constant_positive d hd).le
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d))
      have hbase : (∫⁻ y in farShell d x R k,
          ENNReal.ofReal (dist x y ^ (-(d : ℝ) - α)) ∂sigma d) ≤
          ENNReal.ofReal (a ^ (-(d : ℝ) - α)) := by
        simpa only [mul_one] using hint.trans (mul_le_mul_right hmass _)
      exact hbase.trans (ENNReal.ofReal_le_ofReal
        (hpower.trans (le_mul_of_one_le_left (Real.rpow_nonneg ha.le _) hC)))

-- lem:geometric-integral-bridge: Problem1.geometric_integral_bridge
theorem geometric_integral_bridge {X : Type u} [MeasurableSpace X] (μ : Measure X) (S : ℕ → Set X) (hS : ∀ k, MeasurableSet (S k)) (hdisj : Pairwise (fun k l => Disjoint (S k) (S l))) (f : X → ℝ) (hf : Measurable ((⋃ k, S k).indicator f)) (hf0 : ∀ x ∈ (⋃ k, S k), 0 ≤ f x) (B q : ℝ) (hB : 0 ≤ B) (hq : 0 < q) (hq1 : q < 1) (hbound : ∀ k, (∫⁻ x in S k, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal (B * q ^ k)) :
  IntegrableOn f (⋃ k, S k) μ ∧ (∫ x in (⋃ k, S k), f x ∂μ) ≤ B / (1 - q) := by
  have hU : MeasurableSet (⋃ k, S k) := MeasurableSet.iUnion hS
  have hmeas : AEStronglyMeasurable f (μ.restrict (⋃ k, S k)) :=
    (aestronglyMeasurable_indicator_iff hU).mp hf.aestronglyMeasurable
  have hn : ∀ᵐ x ∂μ.restrict (⋃ k, S k), 0 ≤ f x :=
    (ae_restrict_mem hU).mono fun x hx => hf0 x hx
  have hgeom : HasSum (fun k : ℕ => B * q ^ k) (B / (1 - q)) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_abs_lt_one (r := q)
        (by simpa only [abs_of_pos hq] using hq1)).mul_left B
  have hsum : (∑' k : ℕ, ENNReal.ofReal (B * q ^ k)) = ENNReal.ofReal (B / (1 - q)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun k => mul_nonneg hB (pow_nonneg hq.le k)) hgeom.summable, hgeom.tsum_eq]
  have hlin : (∫⁻ x in (⋃ k, S k), ENNReal.ofReal (f x) ∂μ) ≤
      ENNReal.ofReal (B / (1 - q)) :=
    (lintegral_iUnion (μ := μ) hS hdisj (fun x => ENNReal.ofReal (f x))).trans_le
      ((ENNReal.tsum_le_tsum hbound).trans_eq hsum)
  have hI : IntegrableOn f (⋃ k, S k) μ :=
    ⟨hmeas, (hasFiniteIntegral_iff_ofReal hn).2 (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  exact ⟨hI, (integral_eq_lintegral_of_nonneg_ae hn hmeas).trans_le
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin).trans_eq
      (ENNReal.toReal_ofReal (div_nonneg hB (sub_pos.mpr hq1).le)))⟩

-- eq:near-dyadic, lem:near-shell-bound: Problem1.nearDyadicConstant
noncomputable def nearDyadicConstant (d : ℕ) (α : ℝ) :
  ℝ := by
  classical
  exact (
    (capConstant d * Real.rpow 2 ((d : ℝ) + α - 2)) / (1 - Real.rpow 2 (-(2 - α)))
  )

-- eq:far-dyadic, lem:far-shell-bound: Problem1.farDyadicConstant
noncomputable def farDyadicConstant (d : ℕ) (α : ℝ) :
  ℝ := by
  classical
  exact (
    (capConstant d * (2 : ℝ) ^ d + 1) / (1 - Real.rpow 2 (-α))
  )

-- lem:cap-and-dyadic: Problem1.dyadicConstant
noncomputable def dyadicConstant (d : ℕ) (α : ℝ) :
  ℝ := by
  classical
  exact (
    nearDyadicConstant d α + farDyadicConstant d α
  )

-- eq:near-dyadic, lem:near-shell-bound: Problem1.near_shell_bound
theorem near_shell_bound (d : ℕ) (hd : 2 ≤ d) (α : ℝ) (hα : 0 < α) (hα2 : α < 2) :
  0 < nearDyadicConstant d α ∧ ∀ (x : Sphere d) (R : ℝ), 0 < R → R ≤ 1 → IntegrableOn (fun y => Real.rpow (dist x y) (2 - (d : ℝ) - α)) {y | 0 < dist x y ∧ dist x y ≤ R} (sigma d) ∧ (∫ y in {y | 0 < dist x y ∧ dist x y ≤ R}, Real.rpow (dist x y) (2 - (d : ℝ) - α) ∂sigma d) ≤ nearDyadicConstant d α * Real.rpow R (2 - α) := by
  have hq0 : 0 < Real.rpow 2 (-(2 - α)) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hq1 : Real.rpow 2 (-(2 - α)) < 1 := by
    simpa only [Real.rpow_eq_pow] using
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
        (by linarith : -(2 - α) < 0))
  have hA : 0 < capConstant d * Real.rpow 2 ((d : ℝ) + α - 2) :=
    mul_pos (cap_constant_positive d hd)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  refine ⟨div_pos hA (sub_pos.mpr hq1), ?_⟩
  intro x R hR hR1
  have hpart := dyadic_shell_partitions d x R hR hR1
  have hfm : Measurable (fun y : Sphere d => Real.rpow (dist x y) (2 - (d : ℝ) - α)) := by
    simpa only [Real.rpow_eq_pow] using
      (continuous_const.dist continuous_id : Continuous (fun y : Sphere d => dist x y)).measurable.pow_const
        (2 - (d : ℝ) - α)
  have hqpow (k : ℕ) : (Real.rpow 2 (-(2 - α))) ^ k =
      Real.rpow 2 (-((k : ℝ) * (2 - α))) := by
    simp only [Real.rpow_eq_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  have hbound (k : ℕ) : (∫⁻ y in nearShell d x R k,
      ENNReal.ofReal (Real.rpow (dist x y) (2 - (d : ℝ) - α)) ∂sigma d) ≤
      ENNReal.ofReal ((capConstant d * Real.rpow 2 ((d : ℝ) + α - 2) *
        Real.rpow R (2 - α)) * (Real.rpow 2 (-(2 - α))) ^ k) := by
    simpa only [hqpow] using near_shell_contribution d hd α hα hα2 x R hR hR1 k
  simpa only [hpart.2.2.1, nearDyadicConstant, div_mul_eq_mul_div] using
    (geometric_integral_bridge (sigma d) (nearShell d x R) hpart.1 hpart.2.1
      (fun y => Real.rpow (dist x y) (2 - (d : ℝ) - α))
      (hfm.indicator (MeasurableSet.iUnion hpart.1))
      (fun y _ => Real.rpow_nonneg dist_nonneg _)
      (capConstant d * Real.rpow 2 ((d : ℝ) + α - 2) * Real.rpow R (2 - α))
      (Real.rpow 2 (-(2 - α)))
      (mul_nonneg hA.le (Real.rpow_nonneg hR.le _)) hq0 hq1 hbound)

-- eq:far-dyadic, lem:far-shell-bound: Problem1.far_shell_bound
theorem far_shell_bound (d : ℕ) (hd : 2 ≤ d) (α : ℝ) (hα : 0 < α) (hα2 : α < 2) :
  0 < farDyadicConstant d α ∧ ∀ (x : Sphere d) (R : ℝ), 0 < R → R ≤ 1 → IntegrableOn (fun y => Real.rpow (dist x y) (-(d : ℝ) - α)) {y | R < dist x y} (sigma d) ∧ (∫ y in {y | R < dist x y}, Real.rpow (dist x y) (-(d : ℝ) - α) ∂sigma d) ≤ farDyadicConstant d α * Real.rpow R (-α) := by
  have hq0 : 0 < Real.rpow 2 (-α) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hq1 : Real.rpow 2 (-α) < 1 := by
    simpa only [Real.rpow_eq_pow] using
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (neg_neg_of_pos hα))
  have hA : 0 < capConstant d * (2 : ℝ) ^ d + 1 :=
    add_pos (mul_pos (cap_constant_positive d hd) (pow_pos (by norm_num : (0 : ℝ) < 2) d))
      (by norm_num : (0 : ℝ) < 1)
  refine ⟨div_pos hA (sub_pos.mpr hq1), ?_⟩
  intro x R hR hR1
  have hpart := (dyadic_shell_partitions d x R hR hR1).2.2.2
  have hfm : Measurable (fun y : Sphere d => Real.rpow (dist x y) (-(d : ℝ) - α)) := by
    simpa only [Real.rpow_eq_pow] using
      (continuous_const.dist continuous_id : Continuous (fun y : Sphere d => dist x y)).measurable.pow_const
        (-(d : ℝ) - α)
  have hqpow (k : ℕ) : (Real.rpow 2 (-α)) ^ k =
      Real.rpow 2 (-((k : ℝ) * α)) := by
    simp only [Real.rpow_eq_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  have hbound (k : ℕ) : (∫⁻ y in farShell d x R k,
      ENNReal.ofReal (Real.rpow (dist x y) (-(d : ℝ) - α)) ∂sigma d) ≤
      ENNReal.ofReal (((capConstant d * (2 : ℝ) ^ d + 1) * Real.rpow R (-α)) *
        (Real.rpow 2 (-α)) ^ k) := by
    simpa only [hqpow] using far_shell_contribution d hd α hα hα2 x R hR hR1 k
  simpa only [hpart.2.2, farDyadicConstant, div_mul_eq_mul_div] using
    (geometric_integral_bridge (sigma d) (farShell d x R) hpart.1 hpart.2.1
      (fun y => Real.rpow (dist x y) (-(d : ℝ) - α))
      (hfm.indicator (MeasurableSet.iUnion hpart.1))
      (fun y _ => Real.rpow_nonneg dist_nonneg _)
      ((capConstant d * (2 : ℝ) ^ d + 1) * Real.rpow R (-α))
      (Real.rpow 2 (-α))
      (mul_nonneg hA.le (Real.rpow_nonneg hR.le _)) hq0 hq1 hbound)

-- lem:cap-and-dyadic: Problem1.cap_and_dyadic
theorem cap_and_dyadic (d : ℕ) (hd : 2 ≤ d) (α : ℝ) (hα : 0 < α) (hα2 : α < 2) :
  0 < capConstant d ∧ 0 < dyadicConstant d α ∧ (∀ (x : Sphere d) (r : ℝ), 0 < r → r ≤ 2 → sigma d {y | dist x y ≤ r} ≤ ENNReal.ofReal (capConstant d * r ^ d)) ∧ (∀ x : Sphere d, sigma d {x} = 0) ∧ ∀ (x : Sphere d) (R : ℝ), 0 < R → R ≤ 1 → (IntegrableOn (fun y => Real.rpow (dist x y) (2 - (d : ℝ) - α)) {y | 0 < dist x y ∧ dist x y ≤ R} (sigma d) ∧ (∫ y in {y | 0 < dist x y ∧ dist x y ≤ R}, Real.rpow (dist x y) (2 - (d : ℝ) - α) ∂sigma d) ≤ dyadicConstant d α * Real.rpow R (2 - α)) ∧ (IntegrableOn (fun y => Real.rpow (dist x y) (-(d : ℝ) - α)) {y | R < dist x y} (sigma d) ∧ (∫ y in {y | R < dist x y}, Real.rpow (dist x y) (-(d : ℝ) - α) ∂sigma d) ≤ dyadicConstant d α * Real.rpow R (-α)) := by
  have hnear := near_shell_bound d hd α hα hα2
  have hfar := far_shell_bound d hd α hα hα2
  refine ⟨cap_constant_positive d hd, add_pos hnear.1 hfar.1,
    spherical_cap_estimate d hd, sphere_atomless d hd, ?_⟩
  intro x R hR hR1
  refine ⟨⟨(hnear.2 x R hR hR1).1, ?_⟩, ⟨(hfar.2 x R hR hR1).1, ?_⟩⟩
  · exact (hnear.2 x R hR hR1).2.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hfar.1.le) (Real.rpow_nonneg hR.le _))
  · exact (hfar.2 x R hR hR1).2.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hnear.1.le) (Real.rpow_nonneg hR.le _))

-- def:coordinate-kernel: Problem1.coordinateKernel
noncomputable def coordinateKernel (s t : ℝ) :
  ℝ := by
  classical
  exact (
    if t ∈ Set.Ico (-1 : ℝ) 1 then (if s = 0 then -(1 / 2 : ℝ) * Real.log (2 * (1 - t)) else (1 / s) * Real.rpow (2 * (1 - t)) (-s / 2)) else 0
  )

-- lem:coordinate-kernel-representative: Problem1.coordinate_kernel_measurable
theorem coordinate_kernel_measurable (s : ℝ) :
  Measurable (coordinateKernel s) := by
  unfold coordinateKernel
  refine Measurable.ite measurableSet_Ico ?_ measurable_const
  split_ifs with hs
  · fun_prop
  · simp only [Real.rpow_eq_pow]
    fun_prop

-- lem:coordinate-kernel-representative: Problem1.coordinate_kernel_representative
theorem coordinate_kernel_representative (d : ℕ) (s : ℝ) (x y : Sphere d) :
  kernel d s x y = coordinateKernel s (sphereCoordinate d x y) := by
  rcases eq_or_ne x y with rfl | hxy
  · have hcoord : sphereCoordinate d x x = 1 := by
      nlinarith [sphere_dist_sq d x x, dist_self x]
    simp [kernel_diag, hcoord, coordinateKernel]
  · have hr : 0 < dist x y := sphere_dist_pos hxy
    have hcoord : sphereCoordinate d x y ∈ Set.Ico (-1 : ℝ) 1 :=
      ⟨(abs_le.mp (sphereCoordinate_abs_le_one d x y)).1,
        by nlinarith [sphere_dist_sq d x y, sq_pos_of_pos hr]⟩
    rw [coordinateKernel, if_pos hcoord, ← sphere_dist_sq d x y]
    rcases eq_or_ne s 0 with rfl | hs
    · rw [if_pos rfl, kernel_zero_offDiag hxy, Real.log_pow]
      ring
    · rw [if_neg hs, kernel_ne_zero_offDiag hs hxy]
      simp only [Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      ring_nf

-- lem:affine-endpoint-substitution: Problem1.affine_endpoint_geometry
theorem affine_endpoint_geometry  :
  Set.BijOn (fun u : ℝ => 1 - 2 * u) (Set.Ioo 0 1) (Set.Ioo (-1) 1) ∧ (∀ u : ℝ, 2 * (1 - (1 - 2 * u)) = 4 * u ∧ 1 - (1 - 2 * u) ^ 2 = 4 * u * (1 - u)) ∧ (∀ u : ℝ, HasDerivAt (fun v : ℝ => 1 - 2 * v) (-2) u) ∧ |(-2 : ℝ)| = 2 := by
  refine ⟨Set.BijOn.mk ?_ ?_ ?_, ?_, ?_, by norm_num⟩
  · rintro u ⟨hu0, hu1⟩
    exact ⟨by linarith, by linarith⟩
  · intro u hu v hv huv
    linarith
  · rintro t ⟨ht0, ht1⟩
    exact ⟨(1 - t) / 2, ⟨by linarith, by linarith⟩, by ring⟩
  · intro u
    exact ⟨by ring, by ring⟩
  · intro u
    simpa using HasDerivAt.const_sub (1 : ℝ)
      (HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id u))

-- lem:affine-endpoint-substitution: Problem1.affine_endpoint_integrable_iff
theorem affine_endpoint_integrable_iff (g : ℝ → ℝ) (hg : Measurable g) :
  IntegrableOn g (Set.Ioo (-1 : ℝ) 1) volume ↔ IntegrableOn (fun u => g (1 - 2 * u)) (Set.Ioo (0 : ℝ) 1) volume := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun u _ => (affine_endpoint_geometry.2.2.1 u).hasDerivWithinAt)
    affine_endpoint_geometry.1.injOn g
  simpa only [affine_endpoint_geometry.1.image_eq, affine_endpoint_geometry.2.2.2,
    smul_eq_mul, IntegrableOn,
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℝ) ≠ 0))] using hchange

-- lem:affine-endpoint-substitution: Problem1.affine_endpoint_substitution
theorem affine_endpoint_substitution (g : ℝ → ℝ) (hg : Measurable g) (hgi : IntegrableOn g (Set.Ioo (-1 : ℝ) 1) volume) :
  (∫ t in Set.Ioo (-1 : ℝ) 1, g t ∂volume) = 2 * ∫ u in Set.Ioo (0 : ℝ) 1, g (1 - 2 * u) ∂volume := by
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u _ => (affine_endpoint_geometry.2.2.1 u).hasDerivWithinAt)
    affine_endpoint_geometry.1.injOn g
  simpa only [affine_endpoint_geometry.1.image_eq, affine_endpoint_geometry.2.2.2,
    smul_eq_mul, integral_const_mul] using hchange

-- lem:power-kernel-weight-integrable: Problem1.power_kernel_weight_integrable
theorem power_kernel_weight_integrable (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : s < (d : ℝ)) (hs0 : s ≠ 0) :
  IntegrableOn (fun t => coordinateKernel s t * coordinateWeight d t) (Set.Icc (-1 : ℝ) 1) volume ∧ (∫ t in Set.Icc (-1 : ℝ) 1, |coordinateKernel s t| * coordinateWeight d t ∂volume) = |s|⁻¹ * Real.rpow 2 ((d : ℝ) - 1 - s) * ProbabilityTheory.beta (((d : ℝ) - s) / 2) ((d : ℝ) / 2) := by
  have ha : 0 < ((d : ℝ) - s) / 2 := by linarith
  have hb : 0 < (d : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr (by omega)) (by norm_num)
  let C : ℝ := |s|⁻¹ * Real.rpow 2 ((d : ℝ) - 2 - s)
  have hbeta := (beta_integrable (((d : ℝ) - s) / 2) ((d : ℝ) / 2) ha hb).1
  have htransform (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
      |coordinateKernel s (1 - 2 * u)| * coordinateWeight d (1 - 2 * u) =
        C * betaRealDensity (((d : ℝ) - s) / 2) ((d : ℝ) / 2) u := by
    have ht := affine_endpoint_geometry.1.mapsTo hu
    rw [coordinateKernel, if_pos ⟨ht.1.le, ht.2⟩, if_neg hs0,
      coordinateWeight, if_pos ⟨ht.1.le, ht.2.le⟩,
      coordinateExponent, betaRealDensity, if_pos (show 0 < u ∧ u < 1 from hu)]
    rw [(affine_endpoint_geometry.2.1 u).1, (affine_endpoint_geometry.2.1 u).2]
    simp only [Real.rpow_eq_pow, abs_mul, one_div,
      abs_of_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hu.1.le) (-s / 2))]
    simp only [abs_inv, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hu.1.le,
      Real.mul_rpow (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hu.1.le)
        (sub_nonneg.mpr hu.2.le)]
    calc
      _ = |s|⁻¹ * ((4 : ℝ) ^ (-s / 2) * (4 : ℝ) ^ (((d : ℝ) - 2) / 2)) *
          (u ^ (-s / 2) * u ^ (((d : ℝ) - 2) / 2)) *
          (1 - u) ^ (((d : ℝ) - 2) / 2) := by ring
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4), ← Real.rpow_add hu.1]
        simp only [C, Real.rpow_eq_pow, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring_nf
  have hmeas : Measurable (fun t => |coordinateKernel s t| * coordinateWeight d t) :=
    (coordinate_kernel_measurable s).abs.mul (coordinate_weight_measurable d hd).1
  have hcomp : IntegrableOn
      (fun u => |coordinateKernel s (1 - 2 * u)| * coordinateWeight d (1 - 2 * u))
      (Set.Ioo (0 : ℝ) 1) volume :=
    (hbeta.const_mul C).integrableOn.congr_fun
      (fun u hu => (htransform u hu).symm) measurableSet_Ioo
  have habsOpen : IntegrableOn
      (fun t => |coordinateKernel s t| * coordinateWeight d t) (Set.Ioo (-1 : ℝ) 1) volume :=
    (affine_endpoint_integrable_iff _ hmeas).mpr hcomp
  have habs : IntegrableOn
      (fun t => |coordinateKernel s t| * coordinateWeight d t) (Set.Icc (-1 : ℝ) 1) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioo
      (f := fun t => |coordinateKernel s t| * coordinateWeight d t)
      (μ := volume) (a := -1) (b := 1) (by finiteness) (by finiteness)).mpr habsOpen
  have hnorm (t : ℝ) : ‖coordinateKernel s t * coordinateWeight d t‖ =
      |coordinateKernel s t| * coordinateWeight d t := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((coordinate_weight_measurable d hd).2 t)]
  refine ⟨Integrable.mono' habs
    ((coordinate_kernel_measurable s).mul (coordinate_weight_measurable d hd).1).aestronglyMeasurable
    (ae_of_all _ fun t => (hnorm t).le), ?_⟩
  rw [integral_Icc_eq_integral_Ioo, affine_endpoint_substitution _ hmeas habsOpen]
  rw [setIntegral_congr_fun measurableSet_Ioo htransform, integral_const_mul]
  have hsupport :
      (∫ u in Set.Ioo (0 : ℝ) 1, betaRealDensity (((d : ℝ) - s) / 2) ((d : ℝ) / 2) u ∂volume) =
        ∫ u : ℝ, betaRealDensity (((d : ℝ) - s) / 2) ((d : ℝ) / 2) u ∂volume :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => if_neg hu)
  simp only [hsupport, beta_integral_value _ _ ha hb, C]
  simp only [Real.rpow_eq_pow, show (d : ℝ) - 1 - s = ((d : ℝ) - 2 - s) + 1 by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  ring

-- lem:power-kernel-weight-value: Problem1.power_kernel_weight_value
theorem power_kernel_weight_value (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : s < (d : ℝ)) (hs0 : s ≠ 0) :
  coordinateNormConst d * (∫ t in Set.Icc (-1 : ℝ) 1, coordinateKernel s t * coordinateWeight d t ∂volume) = (coordinateNormConst d / s) * Real.rpow 2 ((d : ℝ) - 1 - s) * ProbabilityTheory.beta (((d : ℝ) - s) / 2) ((d : ℝ) / 2) := by
  have hweight := power_kernel_weight_integrable d hd s hs hs0
  have hsign (t : ℝ) : coordinateKernel s t * coordinateWeight d t =
      (|s| / s) * (|coordinateKernel s t| * coordinateWeight d t) := by
    by_cases ht : t ∈ Set.Ico (-1 : ℝ) 1
    · simp only [coordinateKernel, if_pos ht, if_neg hs0, Real.rpow_eq_pow,
        one_div, abs_mul, abs_inv,
        abs_of_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (sub_nonneg.mpr ht.2.le)) (-s / 2))]
      field_simp [hs0]
    · simp only [coordinateKernel, if_neg ht, zero_mul, abs_zero, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Icc (fun t _ => hsign t),
    integral_const_mul, hweight.2]
  field_simp [hs0]

-- lem:log-scalar-bound: Problem1.log_scalar_bound
theorem log_scalar_bound (q u : ℝ) (hq : 0 < q) (hu : 0 < u) (hu1 : u ≤ 1) :
  |Real.log u| ≤ q⁻¹ * Real.rpow u (-q) := by
  rw [abs_of_nonpos (Real.log_nonpos hu.le hu1), Real.rpow_eq_pow,
    Real.rpow_def_of_pos hu, inv_mul_eq_div, le_div_iff₀ hq]
  nlinarith [Real.add_one_le_exp (Real.log u * -q)]

-- lem:log-beta-domination: Problem1.log_beta_integrable
theorem log_beta_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  IntegrableOn (fun u : ℝ => |Real.log u| * Real.rpow u (a - 1) * Real.rpow (1 - u) (b - 1)) (Set.Ioo 0 1) volume := by
  have ha2 : 0 < a / 2 := div_pos ha (by norm_num)
  have hbeta := (beta_integrable (a / 2) b ha2 hb).1
  have hmeas : Measurable
      (fun u : ℝ => |Real.log u| * Real.rpow u (a - 1) * Real.rpow (1 - u) (b - 1)) :=
    (measurable_id.log.abs.mul (measurable_id.pow_const (a - 1))).mul
      ((measurable_const.sub measurable_id).pow_const (b - 1))
  have hdom (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
      ‖|Real.log u| * Real.rpow u (a - 1) * Real.rpow (1 - u) (b - 1)‖ ≤
        (a / 2)⁻¹ * betaRealDensity (a / 2) b u := by
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, Real.rpow_eq_pow,
      abs_of_nonneg (Real.rpow_nonneg hu.1.le (a - 1)),
      abs_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hu.2.le) (b - 1)),
      betaRealDensity, if_pos (show 0 < u ∧ u < 1 from hu)]
    calc
      _ ≤ ((a / 2)⁻¹ * u ^ (-(a / 2))) * u ^ (a - 1) * (1 - u) ^ (b - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (log_scalar_bound (a / 2) u ha2 hu.1 hu.2.le)
            (Real.rpow_nonneg hu.1.le (a - 1)))
          (Real.rpow_nonneg (sub_nonneg.mpr hu.2.le) (b - 1))
      _ = _ := by
        rw [mul_assoc ((a / 2)⁻¹) (u ^ (-(a / 2))) (u ^ (a - 1)),
          ← Real.rpow_add hu.1, show -(a / 2) + (a - 1) = a / 2 - 1 by ring, mul_assoc]
  exact Integrable.mono' (hbeta.const_mul ((a / 2)⁻¹)).integrableOn
    hmeas.aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioo).mono (fun u hu => hdom u hu))

-- lem:log-kernel-weight: Problem1.log_kernel_weight
theorem log_kernel_weight (d : ℕ) (hd : 2 ≤ d) :
  IntegrableOn (fun t => coordinateKernel 0 t * coordinateWeight d t) (Set.Icc (-1 : ℝ) 1) volume ∧ IntegrableOn (fun u : ℝ => (-Real.log 2 - (1 / 2 : ℝ) * Real.log u) * Real.rpow u ((d : ℝ) / 2 - 1) * Real.rpow (1 - u) ((d : ℝ) / 2 - 1)) (Set.Ioo 0 1) volume ∧ coordinateNormConst d * (∫ t in Set.Icc (-1 : ℝ) 1, coordinateKernel 0 t * coordinateWeight d t ∂volume) = coordinateNormConst d * Real.rpow 2 ((d : ℝ) - 1) * ∫ u in Set.Ioo (0 : ℝ) 1, (-Real.log 2 - (1 / 2 : ℝ) * Real.log u) * Real.rpow u ((d : ℝ) / 2 - 1) * Real.rpow (1 - u) ((d : ℝ) / 2 - 1) ∂volume := by
  have ha : 0 < (d : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr (by omega)) (by norm_num)
  have hweights := And.intro
    (beta_integrable ((d : ℝ) / 2) ((d : ℝ) / 2) ha ha).1
    (log_beta_integrable ((d : ℝ) / 2) ((d : ℝ) / 2) ha ha)
  let G : ℝ → ℝ := fun u =>
    (-Real.log 2 - (1 / 2 : ℝ) * Real.log u) * Real.rpow u ((d : ℝ) / 2 - 1) *
      Real.rpow (1 - u) ((d : ℝ) / 2 - 1)
  have hG : IntegrableOn G (Set.Ioo (0 : ℝ) 1) volume :=
    ((hweights.1.const_mul (-Real.log 2)).integrableOn.add
      (Integrable.const_mul hweights.2 (1 / 2 : ℝ))).congr_fun
      (fun u hu => by
        simp only [Pi.add_apply, G, betaRealDensity, if_pos (show 0 < u ∧ u < 1 from hu),
          abs_of_nonpos (Real.log_nonpos hu.1.le hu.2.le), Real.rpow_eq_pow]
        ring) measurableSet_Ioo
  have htransform (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
      coordinateKernel 0 (1 - 2 * u) * coordinateWeight d (1 - 2 * u) =
        Real.rpow 2 ((d : ℝ) - 2) * G u := by
    have ht := affine_endpoint_geometry.1.mapsTo hu
    rw [coordinateKernel, if_pos ⟨ht.1.le, ht.2⟩, if_pos (rfl : (0 : ℝ) = 0),
      coordinateWeight, if_pos ⟨ht.1.le, ht.2.le⟩, coordinateExponent,
      (affine_endpoint_geometry.2.1 u).1, (affine_endpoint_geometry.2.1 u).2]
    simp only [G, Real.rpow_eq_pow, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hu.1.ne',
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hu.1.le,
      Real.mul_rpow (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hu.1.le)
        (sub_nonneg.mpr hu.2.le)]
    simp only [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    simp only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  have hmeas : Measurable (fun t => coordinateKernel 0 t * coordinateWeight d t) :=
    (coordinate_kernel_measurable 0).mul (coordinate_weight_measurable d hd).1
  have hgi : IntegrableOn (fun t => coordinateKernel 0 t * coordinateWeight d t)
      (Set.Ioo (-1 : ℝ) 1) volume :=
    (affine_endpoint_integrable_iff _ hmeas).mpr
      (IntegrableOn.congr_fun (Integrable.const_mul hG (Real.rpow 2 ((d : ℝ) - 2)))
        (fun u hu => (htransform u hu).symm) measurableSet_Ioo)
  refine ⟨(integrableOn_Icc_iff_integrableOn_Ioo
    (f := fun t => coordinateKernel 0 t * coordinateWeight d t)
    (μ := volume) (a := -1) (b := 1) (by finiteness) (by finiteness)).mpr hgi, hG, ?_⟩
  rw [integral_Icc_eq_integral_Ioo, affine_endpoint_substitution _ hmeas hgi,
    setIntegral_congr_fun measurableSet_Ioo htransform, integral_const_mul]
  simp only [G, Real.rpow_eq_pow, show (d : ℝ) - 1 = ((d : ℝ) - 2) + 1 by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  ring

-- lem:kernel-section-integrable: Problem1.kernel_section_integrable
theorem kernel_section_integrable (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : s < (d : ℝ)) (x : Sphere d) :
  Integrable (kernel d s x) (sigma d) := by
  rw [show kernel d s x = (fun y => coordinateKernel s (sphereCoordinate d x y)) from
    funext (coordinate_kernel_representative d s x),
    coordinate_law_integrable_iff d hd x (coordinateKernel s) (coordinate_kernel_measurable s)]
  by_cases hs0 : s = 0
  · simpa only [hs0] using (log_kernel_weight d hd).1
  · exact (power_kernel_weight_integrable d hd s hs hs0).1

-- lem:I-center-independent: Problem1.continuous_energy_center
theorem continuous_energy_center (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : s < (d : ℝ)) (x : Sphere d) :
  (∫ y, kernel d s x y ∂sigma d) = continuousEnergy d s := by
  have hrep (z : Sphere d) : kernel d s z =
      (fun y => coordinateKernel s (sphereCoordinate d z y)) :=
    funext (coordinate_kernel_representative d s z)
  have hweight :=
    (coordinate_law_integrable_iff d hd x (coordinateKernel s) (coordinate_kernel_measurable s)).mp
      ((hrep x) ▸ kernel_section_integrable d hd s hs x)
  rw [continuousEnergy, hrep x, hrep (northPole d),
    coordinate_law d hd x (coordinateKernel s) (coordinate_kernel_measurable s) hweight,
    coordinate_law d hd (northPole d) (coordinateKernel s) (coordinate_kernel_measurable s) hweight]

-- eq:I-formula, eq:I-log-formula, lem:I-formula: Problem1.continuous_energy_power_formula
theorem continuous_energy_power_formula (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : s < (d : ℝ)) (hs0 : s ≠ 0) :
  continuousEnergy d s = (coordinateNormConst d / s) * Real.rpow 2 ((d : ℝ) - 1 - s) * ProbabilityTheory.beta (((d : ℝ) - s) / 2) ((d : ℝ) / 2) := by
  rw [continuousEnergy, show kernel d s (northPole d) =
      (fun y => coordinateKernel s (sphereCoordinate d (northPole d) y)) from
    funext (coordinate_kernel_representative d s (northPole d)),
    coordinate_law d hd (northPole d) (coordinateKernel s) (coordinate_kernel_measurable s)
      (power_kernel_weight_integrable d hd s hs hs0).1]
  exact power_kernel_weight_value d hd s hs hs0

-- eq:I-formula, eq:I-log-formula, lem:I-formula: Problem1.continuous_energy_log_formula
theorem continuous_energy_log_formula (d : ℕ) (hd : 2 ≤ d) :
  IntegrableOn (fun u : ℝ => (-Real.log 2 - (1 / 2 : ℝ) * Real.log u) * Real.rpow u ((d : ℝ) / 2 - 1) * Real.rpow (1 - u) ((d : ℝ) / 2 - 1)) (Set.Ioo 0 1) volume ∧ continuousEnergy d 0 = coordinateNormConst d * Real.rpow 2 ((d : ℝ) - 1) * ∫ u in Set.Ioo (0 : ℝ) 1, (-Real.log 2 - (1 / 2 : ℝ) * Real.log u) * Real.rpow u ((d : ℝ) / 2 - 1) * Real.rpow (1 - u) ((d : ℝ) / 2 - 1) ∂volume := by
  refine ⟨(log_kernel_weight d hd).2.1, ?_⟩
  rw [continuousEnergy, show kernel d 0 (northPole d) =
      (fun y => coordinateKernel 0 (sphereCoordinate d (northPole d) y)) from
    funext (coordinate_kernel_representative d 0 (northPole d)),
    coordinate_law d hd (northPole d) (coordinateKernel 0) (coordinate_kernel_measurable 0)
      (log_kernel_weight d hd).1]
  exact (log_kernel_weight d hd).2.2

-- eq:I-formula, eq:I-log-formula, lem:I-formula: Problem1.I_formula
theorem I_formula (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : s < (d : ℝ)) :
  (∀ x : Sphere d, Integrable (kernel d s x) (sigma d) ∧ (∫ y, kernel d s x y ∂sigma d) = continuousEnergy d s) ∧ (s ≠ 0 → continuousEnergy d s = (coordinateNormConst d / s) * Real.rpow 2 ((d : ℝ) - 1 - s) * ProbabilityTheory.beta (((d : ℝ) - s) / 2) ((d : ℝ) / 2)) ∧ IntegrableOn (fun u : ℝ => (-Real.log 2 - (1 / 2 : ℝ) * Real.log u) * Real.rpow u ((d : ℝ) / 2 - 1) * Real.rpow (1 - u) ((d : ℝ) / 2 - 1)) (Set.Ioo 0 1) volume ∧ (s = 0 → continuousEnergy d s = coordinateNormConst d * Real.rpow 2 ((d : ℝ) - 1) * ∫ u in Set.Ioo (0 : ℝ) 1, (-Real.log 2 - (1 / 2 : ℝ) * Real.log u) * Real.rpow u ((d : ℝ) / 2 - 1) * Real.rpow (1 - u) ((d : ℝ) / 2 - 1) ∂volume) := by
  refine ⟨fun x => ⟨kernel_section_integrable d hd s hs x,
    continuous_energy_center d hd s hs x⟩, continuous_energy_power_formula d hd s hs,
    (continuous_energy_log_formula d hd).1, ?_⟩
  exact fun hs0 => by simpa only [hs0] using (continuous_energy_log_formula d hd).2

-- lem:I-sign: Problem1.continuous_energy_pos
theorem continuous_energy_pos (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 < s) (hs : s < (d : ℝ)) :
  0 < continuousEnergy d s := by
  rw [continuous_energy_power_formula d hd s hs hs0.ne']
  have hbeta := beta_positive (((d : ℝ) - s) / 2) ((d : ℝ) / 2)
    (div_pos (sub_pos.mpr hs) (by norm_num))
    (div_pos (Nat.cast_pos.mpr (by omega)) (by norm_num))
  exact mul_pos (mul_pos (div_pos (coordinate_normalizer_gamma d hd).2.1 hs0)
    (Real.rpow_pos_of_pos (by norm_num) _)) hbeta

-- lem:I-sign: Problem1.continuous_energy_neg
theorem continuous_energy_neg (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : s < 0) :
  continuousEnergy d s < 0 := by
  have hsd : s < (d : ℝ) := lt_of_lt_of_le hs (Nat.cast_nonneg d)
  rw [continuous_energy_power_formula d hd s hsd hs.ne]
  have hbeta := beta_positive (((d : ℝ) - s) / 2) ((d : ℝ) / 2)
    (div_pos (sub_pos.mpr hsd) (by norm_num))
    (div_pos (Nat.cast_pos.mpr (by omega)) (by norm_num))
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (div_neg_of_pos_of_neg (coordinate_normalizer_gamma d hd).2.1 hs)
      (Real.rpow_pos_of_pos (by norm_num) _)) hbeta

-- lem:positive-radial-limit: Problem1.positive_radial_limit
theorem positive_radial_limit (s : ℝ) (hs : 0 < s) :
  Tendsto (fun r : ℝ => (1 / s) * Real.rpow r (-s)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  exact (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hs)).const_mul_atTop
    (one_div_pos.mpr hs)

-- lem:log-radial-limit: Problem1.log_radial_limit
theorem log_radial_limit  :
  Tendsto (fun r : ℝ => -Real.log r) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  exact tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero

-- lem:negative-radial-limit: Problem1.negative_radial_limit
theorem negative_radial_limit (s : ℝ) (hs : s < 0) :
  Tendsto (fun r : ℝ => (1 / s) * Real.rpow r (-s)) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have hlim : Tendsto (fun r : ℝ => Real.rpow r (-s)) (𝓝 0) (𝓝 0) := by
    simpa only [Real.rpow_eq_pow, Real.zero_rpow (neg_pos.mpr hs).ne'] using
      (Real.continuous_rpow_const (neg_nonneg.mpr hs.le)).tendsto (0 : ℝ)
  simpa only [mul_zero] using
    (hlim.mono_left (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ 𝓝 0)).const_mul (1 / s)

-- lem:riesz-blowup: Problem1.radial_kernel_sequence
theorem radial_kernel_sequence (s : ℝ) (r : ℕ → {r : ℝ // 0 < r}) (hr : Tendsto (fun j => (r j : ℝ)) atTop (𝓝 0)) :
  (0 ≤ s → Tendsto (fun j => radialKernel s (r j)) atTop atTop) ∧ (s < 0 → Tendsto (fun j => radialKernel s (r j)) atTop (𝓝 0)) := by
  have hri : Tendsto (fun j => (r j : ℝ)) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr, Filter.Eventually.of_forall (fun j => (r j).property)⟩
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · rcases hs.eq_or_lt with hs0 | hspos
    · simpa only [← hs0, radialKernel, ite_true, Function.comp_def] using
        log_radial_limit.comp hri
    · simpa only [radialKernel, if_neg hspos.ne', Function.comp_def] using
        (positive_radial_limit s hspos).comp hri
  · simpa only [radialKernel, if_neg hs.ne, Function.comp_def] using
      (negative_radial_limit s hs).comp hri

-- lem:riesz-blowup: Problem1.riesz_blowup
theorem riesz_blowup (s : ℝ) (hs : 0 ≤ s) (M : ℝ) :
  ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℝ) (hr : 0 < r), r < δ → M < radialKernel s ⟨r, hr⟩ := by
  have hlim : Tendsto
      (fun r : ℝ => if s = 0 then -Real.log r else (1 / s) * Real.rpow r (-s))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    rcases hs.eq_or_lt with hs0 | hspos
    · simpa only [← hs0, ite_true] using log_radial_limit
    · simpa only [if_neg hspos.ne'] using positive_radial_limit s hspos
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hlim.eventually (eventually_gt_atTop M))
  exact ⟨δ, hδ, fun r hr hrδ => hbound ⟨hr, hrδ⟩⟩

-- lem:scaled-gamma-integrable: Problem1.scaled_gamma_integrable
theorem scaled_gamma_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  IntegrableOn (fun v : ℝ => Real.rpow v (a - 1) * Real.exp (-b * v)) (Set.Ioi 0) volume := by
  have hscale := (integrableOn_Ioi_comp_mul_left_iff
    (fun w : ℝ => Real.exp (-w) * w ^ (a - 1)) 0 hb).mpr
      (by simpa only [mul_zero] using Real.GammaIntegral_convergent ha)
  refine IntegrableOn.congr_fun (Integrable.const_mul hscale (b ^ (1 - a))) ?_ measurableSet_Ioi
  intro v hv
  simp only [Real.rpow_eq_pow, Real.mul_rpow hb.le (le_of_lt hv), neg_mul]
  rw [mul_left_comm (Real.exp (-(b * v))) (b ^ (a - 1)) (v ^ (a - 1)),
    ← mul_assoc, ← Real.rpow_add hb, show (1 - a) + (a - 1) = 0 by ring,
    Real.rpow_zero, one_mul, mul_comm]

-- lem:scaled-gamma-integral: Problem1.scaled_gamma_integral
theorem scaled_gamma_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  (∫ v in Set.Ioi (0 : ℝ), Real.rpow v (a - 1) * Real.exp (-b * v) ∂volume) = Real.rpow b (-a) * Real.Gamma a := by
  simpa only [Real.rpow_eq_pow, Real.rpow_one, sub_add_cancel, div_one, mul_one] using
    integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := a - 1) (b := b)
      (by norm_num) (by linarith) hb

-- def:gaussian-average: Problem1.gaussianAverage
noncomputable def gaussianAverage (d : ℕ) (t : ℝ) :
  ℝ := by
  classical
  exact (
    ∫ y : Sphere d, Real.exp (-t * dist (northPole d) y ^ 2) ∂sigma d
  )

-- lem:gaussian-center: Problem1.gaussian_center
theorem gaussian_center (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (x : Sphere d) :
  Integrable (fun y => Real.exp (-t * dist x y ^ 2)) (sigma d) ∧ (∫ y, Real.exp (-t * dist x y ^ 2) ∂sigma d) = gaussianAverage d t := by
  have hcont (z : Sphere d) : Continuous (fun y => Real.exp (-t * dist z y ^ 2)) :=
    (continuous_const.mul ((continuous_const.dist continuous_id).pow 2)).rexp
  letI : IsFiniteMeasure (sigma d) := sphere_isFiniteMeasure d
  have hgi (z : Sphere d) : Integrable (fun y => Real.exp (-t * dist z y ^ 2)) (sigma d) :=
    (hcont z).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hgi x, ?_⟩
  obtain ⟨U, hU⟩ := orthogonal_north_transitive (d + 1) (Nat.succ_pos d) x
  have hdist (y : Sphere d) : dist x (sphereAction U y) = dist (northPole d) y := by
    simpa only [← hU, sphereAction, northPole] using sphereActionN_dist U (northPole d) y
  simpa only [hdist, gaussianAverage] using
    (sigma_integral_sphereAction U (fun y => Real.exp (-t * dist x y ^ 2)) (hgi x)).symm

-- lem:gaussian-positive: Problem1.gaussian_positive
theorem gaussian_positive (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (ht : 0 < t) :
  0 < Real.exp (-4 * t) ∧ Real.exp (-4 * t) ≤ gaussianAverage d t := by
  refine ⟨Real.exp_pos _, ?_⟩
  have hdist (y : Sphere d) : dist (northPole d) y ≤ 2 := by
    simpa only [unitSphereN_dist_eq] using (unitSphereN_geometry (northPole d) y).2.1
  have hsq (y : Sphere d) : dist (northPole d) y ^ 2 ≤ 4 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
      (sq_le_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr (hdist y)
  have hbound (y : Sphere d) : Real.exp (-4 * t) ≤ Real.exp (-t * dist (northPole d) y ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr (hsq y))])
  simpa only [gaussianAverage, integral_const, probReal_univ, one_smul] using
    (integral_mono (integrable_const (Real.exp (-4 * t)))
      (gaussian_center d hd t (northPole d)).1 hbound)

-- lem:gaussian-coordinate: Problem1.gaussian_coordinate
theorem gaussian_coordinate (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (ht : 0 < t) :
  IntegrableOn (fun v : ℝ => Real.exp (-2 * t * v) * Real.rpow (v * (2 - v)) ((d : ℝ) / 2 - 1)) (Set.Icc 0 2) volume ∧ gaussianAverage d t = coordinateNormConst d * ∫ v in Set.Icc (0 : ℝ) 2, Real.exp (-2 * t * v) * Real.rpow (v * (2 - v)) ((d : ℝ) / 2 - 1) ∂volume := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : 0 ≤ (d : ℝ) / 2 - 1 := by linarith
  let G : ℝ → ℝ := fun v => Real.exp (-2 * t * v) * Real.rpow (v * (2 - v)) ((d : ℝ) / 2 - 1)
  have hG : Continuous G := by
    simpa only [G, Real.rpow_eq_pow, Function.comp_def, Pi.mul_def, Pi.sub_def, id_eq] using
      ((continuous_const.mul continuous_id).rexp.mul
        ((Real.continuous_rpow_const ha).comp (continuous_id.mul (continuous_const.sub continuous_id))))
  refine ⟨hG.integrableOn_Icc, ?_⟩
  let F : ℝ → ℝ := fun u => Real.exp (-2 * t * (1 - u))
  have hF : Continuous F := (continuous_const.mul (continuous_const.sub continuous_id)).rexp
  have hweight (u : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
      F u * coordinateWeight d u = G (1 - u) := by
    simp only [F, G, coordinateWeight, if_pos hu, coordinateExponent]
    ring_nf
  have hFw : IntegrableOn (fun u => F u * coordinateWeight d u) (Set.Icc (-1 : ℝ) 1) volume :=
    (hG.comp (continuous_const.sub continuous_id)).integrableOn_Icc.congr_fun
      (fun u hu => (hweight u hu).symm) measurableSet_Icc
  have hsub : (∫ u in Set.Icc (-1 : ℝ) 1, G (1 - u)) = ∫ v in Set.Icc (0 : ℝ) 2, G v := by
    simpa only [sub_self, show (1 : ℝ) - -1 = 2 by norm_num,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2), integral_Icc_eq_integral_Ioc] using
      (intervalIntegral.integral_comp_sub_left (a := -1) (b := 1) G 1)
  have hpoint (y : Sphere d) : Real.exp (-t * dist (northPole d) y ^ 2) =
      F (sphereCoordinate d (northPole d) y) := by
    simp only [F, sphere_dist_sq, mul_left_comm, mul_assoc, neg_mul]
  simp only [gaussianAverage, hpoint, coordinate_law d hd (northPole d) F hF.measurable hFw]
  exact congrArg (fun z => coordinateNormConst d * z)
    ((setIntegral_congr_fun measurableSet_Icc hweight).trans hsub)

-- lem:gaussian-upper: Problem1.gaussian_upper
theorem gaussian_upper (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (ht : 0 < t) :
  gaussianAverage d t ≤ (coordinateNormConst d * Real.Gamma ((d : ℝ) / 2) / 2) * Real.rpow t (-(d : ℝ) / 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : 0 ≤ (d : ℝ) / 2 - 1 := by linarith
  let H : ℝ → ℝ := fun v => Real.rpow v ((d : ℝ) / 2 - 1) * Real.exp (-(2 * t) * v)
  have hHi : IntegrableOn (fun v => (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * H v) (Set.Ioi 0) volume :=
    (scaled_gamma_integrable ((d : ℝ) / 2) (2 * t) (by linarith) (by positivity)).const_mul _
  have hHcc : IntegrableOn (fun v => (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * H v) (Set.Icc 0 2) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).mpr (hHi.mono_set (fun _ hv => hv.1))
  have hweight (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 2) :
      Real.rpow (v * (2 - v)) ((d : ℝ) / 2 - 1) ≤
        (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * Real.rpow v ((d : ℝ) / 2 - 1) := by
    simpa only [Real.rpow_eq_pow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hv.1] using
      (Real.rpow_le_rpow (mul_nonneg hv.1 (sub_nonneg.mpr hv.2))
        (show v * (2 - v) ≤ 2 * v by nlinarith [sq_nonneg v]) ha)
  have hbound (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 2) :
      Real.exp (-2 * t * v) * Real.rpow (v * (2 - v)) ((d : ℝ) / 2 - 1) ≤
        (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * H v := by
    simpa only [H, neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_left (hweight v hv) (Real.exp_pos (-2 * t * v)).le)
  have hmono : (∫ v in Set.Icc (0 : ℝ) 2,
      Real.exp (-2 * t * v) * Real.rpow (v * (2 - v)) ((d : ℝ) / 2 - 1)) ≤
      ∫ v in Set.Icc (0 : ℝ) 2, (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * H v :=
    setIntegral_mono_on (gaussian_coordinate d hd t ht).1 hHcc measurableSet_Icc hbound
  have hpos : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun v => (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * H v) :=
    (ae_restrict_mem measurableSet_Ioi).mono (fun v hv =>
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        (mul_nonneg (Real.rpow_nonneg (le_of_lt hv) _) (Real.exp_pos _).le))
  have hext : (∫ v in Set.Icc (0 : ℝ) 2, (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * H v) ≤
      ∫ v in Set.Ioi (0 : ℝ), (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * H v := by
    simpa only [integral_Icc_eq_integral_Ioc] using
      (setIntegral_mono_set (s := Set.Ioc (0 : ℝ) 2) hHi hpos
        (Filter.Eventually.of_forall (fun _ hv => hv.1)))
  have hval : (∫ v in Set.Ioi (0 : ℝ), (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * H v) =
      (2 : ℝ) ^ ((d : ℝ) / 2 - 1) *
        (Real.rpow (2 * t) (-(d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)) := by
    simpa only [H, integral_const_mul, neg_div] using
      congrArg (fun z => (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * z)
        (scaled_gamma_integral ((d : ℝ) / 2) (2 * t) (by linarith) (by positivity))
  have hscale : (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * Real.rpow (2 * t) (-(d : ℝ) / 2) =
      (1 / 2 : ℝ) * Real.rpow t (-(d : ℝ) / 2) := by
    simp only [Real.rpow_eq_pow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht.le]
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show (d : ℝ) / 2 - 1 + -(d : ℝ) / 2 = -1 by ring, Real.rpow_neg_one, one_div]
  calc
    gaussianAverage d t = coordinateNormConst d * ∫ v in Set.Icc (0 : ℝ) 2,
        Real.exp (-2 * t * v) * Real.rpow (v * (2 - v)) ((d : ℝ) / 2 - 1) :=
      (gaussian_coordinate d hd t ht).2
    _ ≤ coordinateNormConst d * ((2 : ℝ) ^ ((d : ℝ) / 2 - 1) *
        (Real.rpow (2 * t) (-(d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left ((hmono.trans hext).trans_eq hval)
        (coordinate_normalizer_gamma d hd).2.1.le
    _ = (coordinateNormConst d * Real.Gamma ((d : ℝ) / 2) / 2) *
        Real.rpow t (-(d : ℝ) / 2) := by
      linear_combination coordinateNormConst d * Real.Gamma ((d : ℝ) / 2) * hscale

-- eq:J-bound, lem:gaussian-average: Problem1.gaussianAverageConstant
noncomputable def gaussianAverageConstant (d : ℕ) :
  ℝ := by
  classical
  exact (
    coordinateNormConst d * Real.Gamma ((d : ℝ) / 2) / 2
  )

-- eq:J-bound, lem:gaussian-average: Problem1.gaussian_average
theorem gaussian_average (d : ℕ) (hd : 2 ≤ d) :
  0 < gaussianAverageConstant d ∧ (∀ t : ℝ, 0 < t → 0 < gaussianAverage d t ∧ gaussianAverage d t ≤ gaussianAverageConstant d * Real.rpow t (-(d : ℝ) / 2)) ∧ ∀ (t : ℝ) (x : Sphere d), Integrable (fun y => Real.exp (-t * dist x y ^ 2)) (sigma d) ∧ (∫ y, Real.exp (-t * dist x y ^ 2) ∂sigma d) = gaussianAverage d t := by
  refine ⟨?_, ?_, gaussian_center d hd⟩
  · exact div_pos (mul_pos (coordinate_normalizer_gamma d hd).2.1
      (Real.Gamma_pos_of_pos (div_pos (Nat.cast_pos.mpr (by omega)) (by norm_num)))) (by norm_num)
  · exact fun t ht => ⟨(gaussian_positive d hd t ht).1.trans_le (gaussian_positive d hd t ht).2,
      gaussian_upper d hd t ht⟩

-- def:exact-ambient-polynomial-carriers: Problem1.AmbientLE
noncomputable def AmbientLE (d L : ℕ) : Submodule ℝ (Ambient d) := by
  classical
  exact (
    MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ L
  )

-- def:exact-ambient-polynomial-carriers: Problem1.laplacian
noncomputable def laplacian (d : ℕ) : Ambient d →ₗ[ℝ] Ambient d := by
  classical
  exact (
    ∑ i : Fin (d + 1), (MvPolynomial.pderiv i).toLinearMap.comp (MvPolynomial.pderiv i).toLinearMap
  )

-- def:exact-ambient-polynomial-carriers: Problem1.eulerOperator
noncomputable def eulerOperator (d : ℕ) : Ambient d →ₗ[ℝ] Ambient d := by
  classical
  exact (
    ∑ i : Fin (d + 1), (LinearMap.mulLeft ℝ (MvPolynomial.X i)).comp (MvPolynomial.pderiv i).toLinearMap
  )

-- def:exact-ambient-polynomial-carriers: Problem1.HAmb
noncomputable def HAmb (d n : ℕ) : Submodule ℝ (Ambient d) := by
  classical
  exact (
    P d n ⊓ LinearMap.ker (laplacian d)
  )

-- def:exact-ambient-polynomial-carriers: Problem1.radialQ
noncomputable def radialQ (d : ℕ) : Ambient d := by
  classical
  exact (
    ∑ i : Fin (d + 1), MvPolynomial.X i ^ 2
  )

-- def:exact-ambient-polynomial-carriers: Problem1.radialMul
noncomputable def radialMul (d : ℕ) : Ambient d →ₗ[ℝ] Ambient d := by
  classical
  exact (
    LinearMap.mulLeft ℝ (radialQ d)
  )

-- def:exact-ambient-polynomial-carriers: Problem1.radialP
noncomputable def radialP (d n : ℕ) : Submodule ℝ (Ambient d) := by
  classical
  exact (
    (P d n).map (radialMul d)
  )

-- def:exact-ambient-polynomial-carriers: Problem1.polynomialEval
noncomputable def polynomialEval (d : ℕ) (p : Ambient d) (z : Euclidean d) : ℝ := by
  classical
  exact (
    MvPolynomial.eval (fun i => z i) p
  )

-- lem:polynomial-evaluation-continuous: Problem1.polynomial_evaluation_continuous
theorem polynomial_evaluation_continuous (d : ℕ) (p : Ambient d) : Continuous (polynomialEval d p) := by
  exact (MvPolynomial.continuous_eval p).comp (PiLp.continuous_ofLp 2 (fun _ : Fin (d + 1) => ℝ))

-- lem:polynomial-evaluation-injective: Problem1.polynomial_evaluation_injective
theorem polynomial_evaluation_injective (d : ℕ) (p q : Ambient d) (h : ∀ z : Euclidean d, polynomialEval d p z = polynomialEval d q z) : p = q := by
  exact polynomial_eq_of_eq_on_open_box (d + 1) p q (fun _ => 0) (fun _ => 1)
    (fun _ => by norm_num) (fun z _ => h (WithLp.toLp 2 z))

-- lem:homogeneous-scaling: Problem1.homogeneous_scaling
theorem homogeneous_scaling (d n : ℕ) (p : P d n) (a : ℝ) (z : Euclidean d) : polynomialEval d p (a • z) = a ^ n * polynomialEval d p z := by
  have hp : MvPolynomial.IsHomogeneous (p : Ambient d) n := p.property
  simp only [polynomialEval, MvPolynomial.eval_eq, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hbdeg : (∑ i ∈ b.support, b i) = n := by
    simpa only [← Finsupp.degree_apply, Finsupp.degree_eq_weight_one, Pi.one_def] using
      hp (MvPolynomial.mem_support_iff.mp hb)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hbdeg, mul_left_comm]

-- lem:homogeneous-components: Problem1.homogeneous_components
theorem homogeneous_components (d : ℕ) (p : Ambient d) : (∀ n : ℕ, MvPolynomial.homogeneousComponent n p ∈ P d n) ∧ (∑ n ∈ Finset.range (p.totalDegree + 1), MvPolynomial.homogeneousComponent n p) = p := by
  exact ⟨fun n => MvPolynomial.homogeneousComponent_mem n p, MvPolynomial.sum_homogeneousComponent p⟩

-- lem:homogeneous-components: Problem1.bounded_homogeneous_components
theorem bounded_homogeneous_components (d L : ℕ) (p : AmbientLE d L) (n : ℕ) (hn : L < n) : MvPolynomial.homogeneousComponent n (p : Ambient d) = 0 := by
  exact MvPolynomial.homogeneousComponent_eq_zero n (p : Ambient d)
    (((MvPolynomial.mem_restrictTotalDegree _ _ _).mp p.property).trans_lt hn)

-- lem:homogeneous-components: Problem1.homogeneous_le_ambientLE
theorem homogeneous_le_ambientLE (d n L : ℕ) (hn : n ≤ L) : P d n ≤ AmbientLE d L := by
  exact fun p hp => (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
    ((show MvPolynomial.IsHomogeneous p n from hp).totalDegree_le.trans hn)

-- lem:formal-derivative-rules: Problem1.formal_derivative_add
theorem formal_derivative_add (d : ℕ) (i : Fin (d + 1)) (p q : Ambient d) : MvPolynomial.pderiv i (p + q) = MvPolynomial.pderiv i p + MvPolynomial.pderiv i q := by
  exact (MvPolynomial.pderiv i).map_add p q

-- lem:formal-derivative-rules: Problem1.formal_derivative_smul
theorem formal_derivative_smul (d : ℕ) (i : Fin (d + 1)) (a : ℝ) (p : Ambient d) : MvPolynomial.pderiv i (a • p) = a • MvPolynomial.pderiv i p := by
  exact (MvPolynomial.pderiv i).map_smul a p

-- lem:formal-derivative-rules: Problem1.formal_derivative_mul
theorem formal_derivative_mul (d : ℕ) (i : Fin (d + 1)) (p q : Ambient d) : MvPolynomial.pderiv i (p * q) = MvPolynomial.pderiv i p * q + p * MvPolynomial.pderiv i q := by
  exact MvPolynomial.pderiv_mul

-- lem:formal-derivative-rules: Problem1.formal_derivative_X
theorem formal_derivative_X (d : ℕ) (i j : Fin (d + 1)) : MvPolynomial.pderiv i (MvPolynomial.X j : Ambient d) = if i = j then 1 else 0 := by
  simpa only [Pi.single_apply, eq_comm] using (MvPolynomial.pderiv_X (R := ℝ) i j)

-- lem:formal-derivative-rules: Problem1.formal_derivative_C
theorem formal_derivative_C (d : ℕ) (i : Fin (d + 1)) (a : ℝ) : MvPolynomial.pderiv i (MvPolynomial.C a : Ambient d) = 0 := by
  exact MvPolynomial.pderiv_C

-- lem:polynomial-curve-derivative: Problem1.polynomial_curve_derivative
theorem polynomial_curve_derivative (d : ℕ) (p : Ambient d) (z : ℝ → Euclidean d) (v : Fin (d + 1) → ℝ) (t₀ : ℝ) (hz : ∀ i, HasDerivAt (fun t => z t i) (v i) t₀) : HasDerivAt (fun t => polynomialEval d p (z t)) (∑ i : Fin (d + 1), polynomialEval d (MvPolynomial.pderiv i p) (z t₀) * v i) t₀ := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa only [formal_derivative_C, polynomialEval, MvPolynomial.eval_C, map_zero, zero_mul,
        Finset.sum_const_zero] using (hasDerivAt_const t₀ a)
  | add p q hp hq =>
      simpa only [formal_derivative_add, polynomialEval, map_add, add_mul, Finset.sum_add_distrib,
        Pi.add_def] using hp.add hq
  | mul_X p j hp =>
      simpa [polynomialEval, formal_derivative_mul, formal_derivative_X, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum, mul_add, Pi.single_apply, apply_ite, mul_ite, add_comm,
        mul_assoc, mul_left_comm, mul_comm, Pi.mul_def] using hp.mul (hz j)

-- lem:mixed-partials: Problem1.mixed_partials
theorem mixed_partials (d : ℕ) (p : Ambient d) (i j : Fin (d + 1)) : MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  by_cases h : i = j
  · simp only [h]
  · ext b
    simp [MvPolynomial.coeff_pderiv, h, Ne.symm h, add_left_comm, add_comm,
      mul_assoc, mul_left_comm, mul_comm]

-- def:linear-substitution: Problem1.linearSubstitution
noncomputable def linearSubstitution (d : ℕ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Ambient d →ₐ[ℝ] Ambient d := by
  classical
  exact (
    MvPolynomial.aeval (fun j => ∑ k : Fin (d + 1), MvPolynomial.C (A j k) * MvPolynomial.X k)
  )

-- lem:substitution-evaluation: Problem1.substitution_evaluation
theorem substitution_evaluation (d : ℕ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (p : Ambient d) (z : Euclidean d) : polynomialEval d (linearSubstitution d A p) z = MvPolynomial.eval (fun j => ∑ k : Fin (d + 1), A j k * z k) p := by
  change MvPolynomial.aeval (fun i => z i)
    (MvPolynomial.aeval
      (fun j => ∑ k : Fin (d + 1), MvPolynomial.C (A j k) * MvPolynomial.X k) p) =
    MvPolynomial.aeval (fun j => ∑ k : Fin (d + 1), A j k * z k) p
  rw [MvPolynomial.comp_aeval_apply]
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply]

-- lem:polynomial-substitution-derivative: Problem1.polynomial_substitution_derivative
theorem polynomial_substitution_derivative (d : ℕ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (p : Ambient d) (i : Fin (d + 1)) : MvPolynomial.pderiv i (linearSubstitution d A p) = ∑ j : Fin (d + 1), A j i • linearSubstitution d A (MvPolynomial.pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [linearSubstitution]
  | add p q hp hq => simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
      have hX : MvPolynomial.pderiv i (linearSubstitution d A (MvPolynomial.X j)) =
          MvPolynomial.C (A j i) := by
        simp [linearSubstitution, Pi.single_apply]
      rw [map_mul, MvPolynomial.pderiv_mul, hp]
      simp [Pi.single_apply, apply_ite, smul_add,
        Finset.sum_add_distrib, Finset.mul_sum, hX,
        MvPolynomial.C_mul', mul_comm, add_comm]

-- lem:substitution-degree: Problem1.substitution_homogeneous
theorem substitution_homogeneous (d n : ℕ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (p : Ambient d) (hp : p ∈ P d n) : linearSubstitution d A p ∈ P d n := by
  simpa only [linearSubstitution, P, MvPolynomial.mem_homogeneousSubmodule, one_mul] using
    (show MvPolynomial.IsHomogeneous p n from hp).aeval
      (fun j => ∑ k : Fin (d + 1), MvPolynomial.C (A j k) * MvPolynomial.X k)
      (fun j => MvPolynomial.IsHomogeneous.sum _ _ 1
        (fun k _ => MvPolynomial.isHomogeneous_C_mul_X (A j k) k))

-- lem:substitution-degree: Problem1.substitution_bounded
theorem substitution_bounded (d L : ℕ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (p : Ambient d) (hp : p ∈ AmbientLE d L) : linearSubstitution d A p ∈ AmbientLE d L := by
  rw [← (homogeneous_components d p).2, map_sum]
  refine (AmbientLE d L).sum_mem fun n _ => ?_
  by_cases hn : n ≤ L
  · exact homogeneous_le_ambientLE d n L hn
      (substitution_homogeneous d n A _ ((homogeneous_components d p).1 n))
  · simpa only [bounded_homogeneous_components d L ⟨p, hp⟩ n (lt_of_not_ge hn), map_zero] using
      (AmbientLE d L).zero_mem

-- lem:euler: Problem1.euler
theorem euler (d n : ℕ) (p : P d n) : eulerOperator d p = (n : ℝ) • (p : Ambient d) := by
  simpa [eulerOperator, Nat.cast_smul_eq_nsmul] using
    (show MvPolynomial.IsHomogeneous (p : Ambient d) n from p.property).sum_X_mul_pderiv

-- lem:fischer-degree-maps: Problem1.partial_homogeneous_degree
theorem partial_homogeneous_degree (d n : ℕ) (i : Fin (d + 1)) (p : Ambient d) (hp : p ∈ P d (n + 1)) : MvPolynomial.pderiv i p ∈ P d n := by
  simpa only [P, MvPolynomial.mem_homogeneousSubmodule, Nat.add_sub_cancel] using
    (show MvPolynomial.IsHomogeneous p (n + 1) from hp).pderiv (i := i)

-- lem:fischer-degree-maps: Problem1.laplacian_homogeneous_degree
theorem laplacian_homogeneous_degree (d n : ℕ) (p : Ambient d) (hp : p ∈ P d (n + 2)) : laplacian d p ∈ P d n := by
  simpa [laplacian] using (P d n).sum_mem (t := Finset.univ)
    (fun (i : Fin (d + 1)) _ => partial_homogeneous_degree d n i _
      (partial_homogeneous_degree d (n + 1) i p hp))

-- lem:fischer-degree-maps: Problem1.radial_homogeneous_degree
theorem radial_homogeneous_degree (d n : ℕ) : radialP d n ≤ P d (n + 2) := by
  rintro q ⟨p, hp, rfl⟩
  simpa [radialMul, radialQ, P, MvPolynomial.mem_homogeneousSubmodule, Nat.add_comm] using
    (MvPolynomial.IsHomogeneous.sum Finset.univ
      (fun i : Fin (d + 1) => (MvPolynomial.X i : Ambient d) ^ 2) 2
      (fun i _ => MvPolynomial.isHomogeneous_X_pow i 2)).mul
      (show MvPolynomial.IsHomogeneous p n from hp)

-- lem:fischer-degree-maps: Problem1.degree_zero_harmonic
theorem degree_zero_harmonic (d : ℕ) (p : P d 0) : laplacian d p = 0 := by
  have hp : (p : Ambient d) = MvPolynomial.C ((p : Ambient d).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (d + 1))).mpr p.property)
  rw [hp]
  simp [laplacian]

-- lem:fischer-degree-maps: Problem1.degree_one_harmonic
theorem degree_one_harmonic (d : ℕ) (p : P d 1) : laplacian d p = 0 := by
  have hC (i : Fin (d + 1)) : MvPolynomial.pderiv i (p : Ambient d) =
      MvPolynomial.C (MvPolynomial.coeff 0 (MvPolynomial.pderiv i (p : Ambient d))) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (d + 1))).mpr
        (partial_homogeneous_degree d 0 i p p.property))
  simp only [laplacian, LinearMap.sum_apply, LinearMap.comp_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  change MvPolynomial.pderiv i (MvPolynomial.pderiv i (p : Ambient d)) = 0
  rw [hC i, MvPolynomial.pderiv_C]

-- lem:restriction-linear: Problem1.polynomial_restriction_continuous
theorem polynomial_restriction_continuous (d : ℕ) (p : Ambient d) : Continuous (fun x : Sphere d => polynomialEval d p (x : Euclidean d)) := by
  exact (polynomial_evaluation_continuous d p).comp continuous_subtype_val

-- lem:restriction-linear: Problem1.restrictionFunction
noncomputable def restrictionFunction (d : ℕ) (p : Ambient d) : C(Sphere d, ℝ) := by
  classical
  exact (
    ⟨fun x => polynomialEval d p (x : Euclidean d), polynomial_restriction_continuous d p⟩
  )

-- lem:restriction-linear: Problem1.restriction_map_add
theorem restriction_map_add (d : ℕ) (p q : Ambient d) : restrictionFunction d (p + q) = restrictionFunction d p + restrictionFunction d q := by
  exact ContinuousMap.ext fun x => map_add (MvPolynomial.eval (fun i => x.1 i)) p q

-- lem:restriction-linear: Problem1.restriction_map_smul
theorem restriction_map_smul (d : ℕ) (a : ℝ) (p : Ambient d) : restrictionFunction d (a • p) = a • restrictionFunction d p := by
  exact ContinuousMap.ext fun x =>
    (MvPolynomial.aeval (R := ℝ) (fun i => x.1 i)).toLinearMap.map_smul a p

-- lem:restriction-linear: Problem1.restriction
noncomputable def restriction (d : ℕ) : Ambient d →ₗ[ℝ] C(Sphere d, ℝ) := by
  classical
  exact (
    { toFun := restrictionFunction d, map_add' := restriction_map_add d, map_smul' := restriction_map_smul d }
  )

-- def:exact-restriction-carriers: Problem1.harmonicRestriction
noncomputable def harmonicRestriction (d n : ℕ) : HAmb d n →ₗ[ℝ] C(Sphere d, ℝ) := by
  classical
  exact (
    (restriction d).domRestrict (HAmb d n)
  )

-- def:exact-restriction-carriers: Problem1.boundedRestriction
noncomputable def boundedRestriction (d L : ℕ) : AmbientLE d L →ₗ[ℝ] C(Sphere d, ℝ) := by
  classical
  exact (
    (restriction d).domRestrict (AmbientLE d L)
  )

-- def:exact-restriction-carriers: Problem1.Harmonic
noncomputable def Harmonic (d n : ℕ) : Submodule ℝ C(Sphere d, ℝ) := by
  classical
  exact (
    LinearMap.range (harmonicRestriction d n)
  )

-- def:exact-restriction-carriers: Problem1.Pi
noncomputable def Pi (d L : ℕ) : Submodule ℝ C(Sphere d, ℝ) := by
  classical
  exact (
    LinearMap.range (boundedRestriction d L)
  )

-- lem:restriction-map-application: Problem1.restriction_apply
theorem restriction_apply (d : ℕ) (p : Ambient d) (x : Sphere d) : restriction d p x = polynomialEval d p (x : Euclidean d) := by
  rfl

-- lem:restriction-map-application: Problem1.harmonicRestriction_apply
theorem harmonicRestriction_apply (d n : ℕ) (h : HAmb d n) (x : Sphere d) : harmonicRestriction d n h x = polynomialEval d h (x : Euclidean d) := by
  rfl

-- lem:restriction-map-application: Problem1.boundedRestriction_apply
theorem boundedRestriction_apply (d L : ℕ) (p : AmbientLE d L) (x : Sphere d) : boundedRestriction d L p x = polynomialEval d p (x : Euclidean d) := by
  rfl

-- lem:restriction-map-application: Problem1.mem_Harmonic_iff
theorem mem_Harmonic_iff (d n : ℕ) (f : C(Sphere d, ℝ)) : f ∈ Harmonic d n ↔ ∃ h : HAmb d n, harmonicRestriction d n h = f := by
  rfl

-- lem:restriction-map-application: Problem1.mem_Pi_iff
theorem mem_Pi_iff (d L : ℕ) (f : C(Sphere d, ℝ)) : f ∈ Pi d L ↔ ∃ p : AmbientLE d L, boundedRestriction d L p = f := by
  rfl

-- lem:homogeneous-restriction-zero: Problem1.homogeneous_restriction_zero
theorem homogeneous_restriction_zero (d n : ℕ) (p : P d n) (hp : ∀ x : Sphere d, polynomialEval d p (x : Euclidean d) = 0) : (p : Ambient d) = 0 := by
  apply polynomial_evaluation_injective d
  intro z
  by_cases hz : z = 0
  · have h0 : polynomialEval d p 0 = 0 := by
      simpa only [zero_smul, hp (northPole d), mul_zero] using
        (homogeneous_scaling d n p 0 (northPole d : Euclidean d))
    simpa only [hz, polynomialEval, map_zero] using h0
  · let x : Sphere d := ⟨‖z‖⁻¹ • z,
      (unitSphereN_mem_iff _).mpr (norm_smul_inv_norm (𝕜 := ℝ) hz)⟩
    have h0 : polynomialEval d p (‖z‖ • (x : Euclidean d)) = 0 := by
      simpa only [hp x, mul_zero] using (homogeneous_scaling d n p ‖z‖ (x : Euclidean d))
    simpa only [x, smul_inv_smul₀ (norm_ne_zero_iff.mpr hz), polynomialEval, map_zero] using h0

-- lem:harmonic-restriction-injective: Problem1.harmonic_restriction_injective
theorem harmonic_restriction_injective (d n : ℕ) : Function.Injective (harmonicRestriction d n) := by
  intro p q h
  refine Subtype.ext (sub_eq_zero.mp (homogeneous_restriction_zero d n
    ⟨(p : Ambient d) - q, (P d n).sub_mem p.property.1 q.property.1⟩ ?_))
  exact fun x => by
    simpa only [harmonicRestriction_apply, polynomialEval, map_sub, sub_eq_zero] using
      congrArg (fun f : C(Sphere d, ℝ) => f x) h

-- lem:polynomial-carrier-containment: Problem1.pi_mono
theorem pi_mono (d L L' : ℕ) (h : L ≤ L') : Pi d L ≤ Pi d L' := by
  rintro f ⟨p, rfl⟩
  exact ⟨⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
    (((MvPolynomial.mem_restrictTotalDegree _ _ _).mp p.property).trans h)⟩, rfl⟩

-- lem:polynomial-carrier-containment: Problem1.harmonic_le_pi
theorem harmonic_le_pi (d n L : ℕ) (h : n ≤ L) : Harmonic d n ≤ Pi d L := by
  rintro f ⟨p, rfl⟩
  exact ⟨⟨p, homogeneous_le_ambientLE d n L h p.property.1⟩, rfl⟩

-- def:canonical-polynomial-inclusions: Problem1.piInclusion
noncomputable def piInclusion (d L L' : ℕ) (h : L ≤ L') : Pi d L →ₗ[ℝ] Pi d L' := by
  classical
  exact (
    Submodule.inclusion (pi_mono d L L' h)
  )

-- def:canonical-polynomial-inclusions: Problem1.harmonicPiInclusion
noncomputable def harmonicPiInclusion (d n L : ℕ) (h : n ≤ L) : Harmonic d n →ₗ[ℝ] Pi d L := by
  classical
  exact (
    Submodule.inclusion (harmonic_le_pi d n L h)
  )

-- lem:canonical-inclusion-application: Problem1.piInclusion_apply
theorem piInclusion_apply (d L L' : ℕ) (h : L ≤ L') (f : Pi d L) (x : Sphere d) : ((piInclusion d L L' h f : Pi d L') : C(Sphere d, ℝ)) x = (f : C(Sphere d, ℝ)) x := by
  rfl

-- lem:canonical-inclusion-application: Problem1.harmonicPiInclusion_apply
theorem harmonicPiInclusion_apply (d n L : ℕ) (h : n ≤ L) (f : Harmonic d n) (x : Sphere d) : ((harmonicPiInclusion d n L h f : Pi d L) : C(Sphere d, ℝ)) x = (f : C(Sphere d, ℝ)) x := by
  rfl

-- lem:canonical-inclusion-application: Problem1.piInclusion_injective
theorem piInclusion_injective (d L L' : ℕ) (h : L ≤ L') : Function.Injective (piInclusion d L L' h) := by
  exact Submodule.inclusion_injective (pi_mono d L L' h)

-- lem:canonical-inclusion-application: Problem1.harmonicPiInclusion_injective
theorem harmonicPiInclusion_injective (d n L : ℕ) (h : n ≤ L) : Function.Injective (harmonicPiInclusion d n L h) := by
  exact Submodule.inclusion_injective (harmonic_le_pi d n L h)

-- lem:Pi-inclusion-functoriality: Problem1.piInclusion_refl
theorem piInclusion_refl (d L : ℕ) : piInclusion d L L le_rfl = LinearMap.id := by
  exact LinearMap.ext fun f => Subtype.ext rfl

-- lem:Pi-inclusion-functoriality: Problem1.piInclusion_trans
theorem piInclusion_trans (d L L' L'' : ℕ) (h : L ≤ L') (h' : L' ≤ L'') : (piInclusion d L' L'' h').comp (piInclusion d L L' h) = piInclusion d L L'' (h.trans h') := by
  exact LinearMap.ext fun f => Subtype.ext rfl

-- lem:harmonic-Pi-inclusion-functoriality: Problem1.harmonicPiInclusion_trans
theorem harmonicPiInclusion_trans (d n L L' : ℕ) (h : n ≤ L) (h' : L ≤ L') : (piInclusion d L L' h').comp (harmonicPiInclusion d n L h) = harmonicPiInclusion d n L' (h.trans h') := by
  exact LinearMap.ext fun f => Subtype.ext rfl

-- lem:ambient-degree-finite: Problem1.homogeneous_finiteDimensional
instance homogeneous_finiteDimensional (d n : ℕ) : FiniteDimensional ℝ (P d n) := by
  exact Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin (d + 1)) ℝ n)

-- lem:ambient-degree-finite: Problem1.ambientLE_finiteDimensional
instance ambientLE_finiteDimensional (d L : ℕ) : FiniteDimensional ℝ (AmbientLE d L) := by
  exact inferInstanceAs (Module.Finite ℝ (MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ L))

-- lem:finite-dimensional-polynomial-carriers: Problem1.hAmb_finiteDimensional
instance hAmb_finiteDimensional (d n : ℕ) : FiniteDimensional ℝ (HAmb d n) := by
  exact Submodule.finiteDimensional_inf_left (P d n) (LinearMap.ker (laplacian d))

-- lem:finite-dimensional-polynomial-carriers: Problem1.harmonic_finiteDimensional
instance harmonic_finiteDimensional (d n : ℕ) : FiniteDimensional ℝ (Harmonic d n) := by
  exact Module.Finite.range (harmonicRestriction d n)

-- lem:finite-dimensional-polynomial-carriers: Problem1.pi_finiteDimensional
instance pi_finiteDimensional (d L : ℕ) : FiniteDimensional ℝ (Pi d L) := by
  exact Module.Finite.range (boundedRestriction d L)

-- lem:finite-dimensional-polynomial-carriers: Problem1.harmonic_finrank
theorem harmonic_finrank (d n : ℕ) : Module.finrank ℝ (Harmonic d n) = Module.finrank ℝ (HAmb d n) := by
  exact LinearMap.finrank_range_of_inj (harmonic_restriction_injective d n)

-- lem:continuous-product-integrable: Problem1.continuous_sphere_integrable
theorem continuous_sphere_integrable (d : ℕ) (f : C(Sphere d, ℝ)) : MeasureTheory.Integrable f (sigma d) := by
  simpa only [MeasureTheory.integrableOn_univ] using
    f.continuous.continuousOn.integrableOn_compact (μ := sigma d) isCompact_univ

-- lem:continuous-product-integrable: Problem1.continuous_product_integrable
theorem continuous_product_integrable (d : ℕ) (hd : 2 ≤ d) (f g : C(Sphere d, ℝ)) : MeasureTheory.Integrable f (sigma d) ∧ MeasureTheory.Integrable (fun x => f x * g x) (sigma d) ∧ MeasureTheory.Integrable (fun x => f x ^ 2) (sigma d) := by
  have _ := hd
  exact ⟨continuous_sphere_integrable d f, continuous_sphere_integrable d (f * g),
    continuous_sphere_integrable d (f ^ 2)⟩

-- lem:Pi-integrable: Problem1.pi_integrable
theorem pi_integrable (d : ℕ) (hd : 2 ≤ d) (L : ℕ) (f : Pi d L) : MeasureTheory.Integrable (f : C(Sphere d, ℝ)) (sigma d) := by
  have _ := hd
  exact continuous_sphere_integrable d (f : C(Sphere d, ℝ))

-- lem:integral-functional-linear: Problem1.integral_functional_add
theorem integral_functional_add (d L : ℕ) (f g : Pi d L) : (∫ x, ((f + g : Pi d L) : C(Sphere d, ℝ)) x ∂sigma d) = (∫ x, (f : C(Sphere d, ℝ)) x ∂sigma d) + ∫ x, (g : C(Sphere d, ℝ)) x ∂sigma d := by
  exact MeasureTheory.integral_add (continuous_sphere_integrable d (f : C(Sphere d, ℝ)))
    (continuous_sphere_integrable d (g : C(Sphere d, ℝ)))

-- lem:integral-functional-linear: Problem1.integral_functional_smul
theorem integral_functional_smul (d L : ℕ) (a : ℝ) (f : Pi d L) : (∫ x, ((a • f : Pi d L) : C(Sphere d, ℝ)) x ∂sigma d) = a • ∫ x, (f : C(Sphere d, ℝ)) x ∂sigma d := by
  exact MeasureTheory.integral_smul a (f : C(Sphere d, ℝ))

-- def:mean-zero-carrier: Problem1.integralFunctional
noncomputable def integralFunctional (d L : ℕ) : Pi d L →ₗ[ℝ] ℝ := by
  classical
  exact (
    { toFun := fun f => ∫ x, (f : C(Sphere d, ℝ)) x ∂sigma d, map_add' := integral_functional_add d L, map_smul' := integral_functional_smul d L }
  )

-- def:mean-zero-carrier: Problem1.MeanZero
noncomputable def MeanZero (d L : ℕ) : Submodule ℝ (Pi d L) := by
  classical
  exact (
    LinearMap.ker (integralFunctional d L)
  )

-- lem:mean-zero-membership: Problem1.meanZero_mem_iff
theorem meanZero_mem_iff (d : ℕ) (hd : 2 ≤ d) (L : ℕ) (f : Pi d L) : f ∈ MeanZero d L ↔ (∫ x, (f : C(Sphere d, ℝ)) x ∂sigma d) = 0 := by
  have _ := hd
  rfl

-- lem:mean-zero-membership: Problem1.meanZero_finiteDimensional
instance meanZero_finiteDimensional (d L : ℕ) : FiniteDimensional ℝ (MeanZero d L) := by
  exact inferInstanceAs (FiniteDimensional ℝ (LinearMap.ker (integralFunctional d L)))

-- lem:laplacian-covariance: Problem1.laplacian_covariance
theorem laplacian_covariance (d : ℕ) (A : Orthogonal d) (p : Ambient d) : laplacian d (linearSubstitution d (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) p) = linearSubstitution d (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (laplacian d p) := by
  have hA (j k : Fin (d + 1)) :
      (∑ i : Fin (d + 1), (A : Matrix _ _ ℝ) j i * (A : Matrix _ _ ℝ) k i) =
        if j = k then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => B j k)
        (orthogonalN_mul_transpose A)
  simp only [laplacian, LinearMap.sum_apply, LinearMap.comp_apply]
  change (∑ i : Fin (d + 1), MvPolynomial.pderiv i
    (MvPolynomial.pderiv i (linearSubstitution d (↑A) p))) =
      linearSubstitution d (↑A) (∑ i : Fin (d + 1), MvPolynomial.pderiv i (MvPolynomial.pderiv i p))
  simp only [polynomial_substitution_derivative, map_sum, Derivation.map_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  simp [← Finset.sum_smul, hA, ite_smul]

-- lem:orthogonal-pullback: Problem1.orthogonal_preserves_hAmb
theorem orthogonal_preserves_hAmb (d n : ℕ) (R : Orthogonal d) (p : Ambient d) (hp : p ∈ HAmb d n) : linearSubstitution d (↑(R⁻¹)) p ∈ HAmb d n := by
  refine ⟨substitution_homogeneous d n (↑(R⁻¹)) p hp.1, ?_⟩
  change laplacian d (linearSubstitution d (↑(R⁻¹)) p) = 0
  rw [laplacian_covariance, (show laplacian d p = 0 from hp.2), map_zero]

-- lem:orthogonal-pullback: Problem1.orthogonal_preserves_ambientLE
theorem orthogonal_preserves_ambientLE (d L : ℕ) (R : Orthogonal d) (p : Ambient d) (hp : p ∈ AmbientLE d L) : linearSubstitution d (↑(R⁻¹)) p ∈ AmbientLE d L := by
  exact substitution_bounded d L (↑(R⁻¹)) p hp

-- lem:pullback-membership: Problem1.spherePullback
noncomputable def spherePullback (d : ℕ) (R : Orthogonal d) (f : C(Sphere d, ℝ)) : C(Sphere d, ℝ) := by
  classical
  exact (
    f.comp (sphereActionEquiv R⁻¹ : C(Sphere d, Sphere d))
  )

-- lem:pullback-membership: Problem1.pullback_mem_pi
theorem pullback_mem_pi (d L : ℕ) (R : Orthogonal d) (f : C(Sphere d, ℝ)) (hf : f ∈ Pi d L) : spherePullback d R f ∈ Pi d L := by
  rcases hf with ⟨p, rfl⟩
  refine ⟨⟨linearSubstitution d (↑(R⁻¹)) p,
    orthogonal_preserves_ambientLE d L R p p.property⟩, ?_⟩
  refine ContinuousMap.ext (fun x => ?_)
  simp only [spherePullback, ContinuousMap.comp_apply, boundedRestriction_apply]
  rw [substitution_evaluation]
  simp [polynomialEval, sphereActionEquiv, sphereActionEquivN_apply,
    sphereActionN_coe, orthogonalLin_apply_coordinate]

-- lem:pullback-membership: Problem1.pullback_mem_harmonic
theorem pullback_mem_harmonic (d n : ℕ) (R : Orthogonal d) (f : C(Sphere d, ℝ)) (hf : f ∈ Harmonic d n) : spherePullback d R f ∈ Harmonic d n := by
  rcases hf with ⟨p, rfl⟩
  refine ⟨⟨linearSubstitution d (↑(R⁻¹)) p,
    orthogonal_preserves_hAmb d n R p p.property⟩, ContinuousMap.ext (fun x => ?_)⟩
  simp only [spherePullback, ContinuousMap.comp_apply, harmonicRestriction_apply,
    substitution_evaluation]
  simp [polynomialEval, sphereActionEquiv, sphereActionEquivN_apply,
    sphereActionN_coe, orthogonalLin_apply_coordinate]

-- lem:pullback-linear-inverse: Problem1.piPullbackFunction
noncomputable def piPullbackFunction (d L : ℕ) (R : Orthogonal d) (f : Pi d L) : Pi d L := by
  classical
  exact (
    ⟨spherePullback d R f, pullback_mem_pi d L R f f.property⟩
  )

-- lem:pullback-linear-inverse: Problem1.harmonicPullbackFunction
noncomputable def harmonicPullbackFunction (d n : ℕ) (R : Orthogonal d) (f : Harmonic d n) : Harmonic d n := by
  classical
  exact (
    ⟨spherePullback d R f, pullback_mem_harmonic d n R f f.property⟩
  )

-- lem:pullback-linear-inverse: Problem1.pi_pullback_add
theorem pi_pullback_add (d L : ℕ) (R : Orthogonal d) (f g : Pi d L) : piPullbackFunction d L R (f + g) = piPullbackFunction d L R f + piPullbackFunction d L R g := by
  exact Subtype.ext (ContinuousMap.ext fun x => rfl)

-- lem:pullback-linear-inverse: Problem1.pi_pullback_smul
theorem pi_pullback_smul (d L : ℕ) (R : Orthogonal d) (a : ℝ) (f : Pi d L) : piPullbackFunction d L R (a • f) = a • piPullbackFunction d L R f := by
  exact Subtype.ext (ContinuousMap.ext fun x => rfl)

-- lem:pullback-linear-inverse: Problem1.pi_pullback_left_inv
theorem pi_pullback_left_inv (d L : ℕ) (R : Orthogonal d) (f : Pi d L) : piPullbackFunction d L R⁻¹ (piPullbackFunction d L R f) = f := by
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  simp [piPullbackFunction, spherePullback, sphereActionEquiv,
    sphereActionEquivN_apply, sphereActionN_inv_left]

-- lem:pullback-linear-inverse: Problem1.pi_pullback_right_inv
theorem pi_pullback_right_inv (d L : ℕ) (R : Orthogonal d) (f : Pi d L) : piPullbackFunction d L R (piPullbackFunction d L R⁻¹ f) = f := by
  simpa only [inv_inv] using pi_pullback_left_inv d L R⁻¹ f

-- lem:pullback-linear-inverse: Problem1.harmonic_pullback_add
theorem harmonic_pullback_add (d n : ℕ) (R : Orthogonal d) (f g : Harmonic d n) : harmonicPullbackFunction d n R (f + g) = harmonicPullbackFunction d n R f + harmonicPullbackFunction d n R g := by
  exact Subtype.ext (ContinuousMap.ext fun x => rfl)

-- lem:pullback-linear-inverse: Problem1.harmonic_pullback_left_inv
theorem harmonic_pullback_left_inv (d n : ℕ) (R : Orthogonal d) (f : Harmonic d n) : harmonicPullbackFunction d n R⁻¹ (harmonicPullbackFunction d n R f) = f := by
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  simp [harmonicPullbackFunction, spherePullback, sphereActionEquiv,
    sphereActionEquivN_apply, sphereActionN_inv_left]

-- lem:pullback-linear-inverse: Problem1.harmonic_pullback_right_inv
theorem harmonic_pullback_right_inv (d n : ℕ) (R : Orthogonal d) (f : Harmonic d n) : harmonicPullbackFunction d n R (harmonicPullbackFunction d n R⁻¹ f) = f := by
  simpa only [inv_inv] using harmonic_pullback_left_inv d n R⁻¹ f

-- lem:pullback-linear-inverse: Problem1.harmonic_pullback_smul
theorem harmonic_pullback_smul (d n : ℕ) (R : Orthogonal d) (a : ℝ) (f : Harmonic d n) : harmonicPullbackFunction d n R (a • f) = a • harmonicPullbackFunction d n R f := by
  exact Subtype.ext (ContinuousMap.ext fun x => rfl)

-- def:Pi-pullback-equiv: Problem1.piPullbackEquiv
noncomputable def piPullbackEquiv (d L : ℕ) (R : Orthogonal d) : Pi d L ≃ₗ[ℝ] Pi d L := by
  classical
  exact (
    { toFun := piPullbackFunction d L R, invFun := piPullbackFunction d L R⁻¹, left_inv := pi_pullback_left_inv d L R, right_inv := pi_pullback_right_inv d L R, map_add' := pi_pullback_add d L R, map_smul' := pi_pullback_smul d L R }
  )

-- def:harmonic-pullback-equiv: Problem1.harmonicPullbackEquiv
noncomputable def harmonicPullbackEquiv (d n : ℕ) (R : Orthogonal d) : Harmonic d n ≃ₗ[ℝ] Harmonic d n := by
  classical
  exact (
    { toFun := harmonicPullbackFunction d n R, invFun := harmonicPullbackFunction d n R⁻¹, left_inv := harmonic_pullback_left_inv d n R, right_inv := harmonic_pullback_right_inv d n R, map_add' := harmonic_pullback_add d n R, map_smul' := harmonic_pullback_smul d n R }
  )

-- lem:pullback-application: Problem1.piPullbackEquiv_apply
theorem piPullbackEquiv_apply (d L : ℕ) (R : Orthogonal d) (f : Pi d L) (x : Sphere d) : ((piPullbackEquiv d L R f : Pi d L) : C(Sphere d, ℝ)) x = (f : C(Sphere d, ℝ)) (sphereAction R⁻¹ x) := by
  rfl

-- lem:pullback-application: Problem1.piPullbackEquiv_symm
theorem piPullbackEquiv_symm (d L : ℕ) (R : Orthogonal d) : (piPullbackEquiv d L R).symm = piPullbackEquiv d L R⁻¹ := by
  exact LinearEquiv.ext fun f => rfl

-- lem:pullback-application: Problem1.harmonicPullbackEquiv_apply
theorem harmonicPullbackEquiv_apply (d n : ℕ) (R : Orthogonal d) (f : Harmonic d n) (x : Sphere d) : ((harmonicPullbackEquiv d n R f : Harmonic d n) : C(Sphere d, ℝ)) x = (f : C(Sphere d, ℝ)) (sphereAction R⁻¹ x) := by
  rfl

-- lem:pullback-application: Problem1.harmonicPullbackEquiv_symm
theorem harmonicPullbackEquiv_symm (d n : ℕ) (R : Orthogonal d) : (harmonicPullbackEquiv d n R).symm = harmonicPullbackEquiv d n R⁻¹ := by
  exact LinearEquiv.ext fun f => rfl

-- lem:pullback-integral-pairing: Problem1.pullback_integral_pairing
theorem pullback_integral_pairing (d : ℕ) (hd : 2 ≤ d) (R : Orthogonal d) (f g : C(Sphere d, ℝ)) : (∫ x, f (sphereAction R⁻¹ x) * g (sphereAction R⁻¹ x) ∂sigma d) = ∫ x, f x * g x ∂sigma d := by
  exact sigma_integral_sphereAction R⁻¹ (fun x => f x * g x)
    (continuous_product_integrable d hd f g).2.1

-- lem:laplacian-product: Problem1.laplacian_product
theorem laplacian_product (d : ℕ) (p q : Ambient d) : laplacian d (p * q) = laplacian d p * q + (2 : ℝ) • (∑ i : Fin (d + 1), MvPolynomial.pderiv i p * MvPolynomial.pderiv i q) + p * laplacian d q := by
  simp only [laplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    Derivation.coeFn_coe, formal_derivative_mul, formal_derivative_add]
  simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, two_smul, add_assoc]

-- lem:radial-power-derivatives: Problem1.radial_power_partial
theorem radial_power_partial (d j : ℕ) (hj : 1 ≤ j) (i : Fin (d + 1)) : MvPolynomial.pderiv i (radialQ d ^ j) = (2 * (j : ℝ)) • (radialQ d ^ (j - 1) * MvPolynomial.X i) := by
  have _ := hj
  have hq : MvPolynomial.pderiv i (radialQ d) = (2 : ℝ) • (MvPolynomial.X i : Ambient d) := by
    simp [radialQ, MvPolynomial.pderiv_X, Pi.single_apply, two_smul]
  rw [MvPolynomial.pderiv_pow, hq]
  simp [MvPolynomial.smul_eq_C_mul, mul_assoc, mul_comm, mul_left_comm]

-- lem:radial-power-derivatives: Problem1.radial_power_laplacian
theorem radial_power_laplacian (d j : ℕ) (hj : 1 ≤ j) : laplacian d (radialQ d ^ j) = (2 * (j : ℝ) * (2 * (j : ℝ) + ((d : ℝ) + 1) - 2)) • radialQ d ^ (j - 1) := by
  rcases hj.eq_or_lt with rfl | hj
  · simp [laplacian, radialQ, MvPolynomial.pderiv_X, Pi.single_apply,
      MvPolynomial.smul_eq_C_mul]
    norm_num [apply_ite, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, mul_comm]
    simp [show (2 : Ambient d) = MvPolynomial.C (2 : ℝ) from (map_ofNat _ _).symm]
  · simp only [laplacian, LinearMap.sum_apply, LinearMap.comp_apply, Derivation.coeFn_coe,
      radial_power_partial d j hj.le, formal_derivative_smul, formal_derivative_mul,
      radial_power_partial d (j - 1) (by omega), MvPolynomial.pderiv_X_self, mul_one]
    simp only [smul_mul_assoc, mul_assoc, ← pow_two, ← Finset.smul_sum,
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← radialQ, pow_sub_one_mul (by omega : j - 1 ≠ 0) (radialQ d)]
    simp only [← Nat.cast_smul_eq_nsmul ℝ, ← add_smul, smul_smul,
      Nat.cast_sub hj.le, Nat.cast_one, Nat.cast_add]
    congr 1
    ring

-- eq:radial-laplacian-general, lem:euler-radial: Problem1.euler_radial
theorem euler_radial (d ℓ j : ℕ) (hj : 1 ≤ j) (p : P d ℓ) : laplacian d (radialQ d ^ j * (p : Ambient d)) = (2 * (j : ℝ) * (2 * (ℓ : ℝ) + ((d : ℝ) + 1) + 2 * (j : ℝ) - 2)) • (radialQ d ^ (j - 1) * (p : Ambient d)) + radialQ d ^ j * laplacian d p := by
  have he : (∑ i : Fin (d + 1), MvPolynomial.X i * MvPolynomial.pderiv i (p : Ambient d)) =
      (ℓ : ℝ) • (p : Ambient d) := by
    simpa [eulerOperator] using euler d ℓ p
  rw [laplacian_product, radial_power_laplacian d j hj]
  simp only [radial_power_partial d j hj, smul_mul_assoc, mul_assoc,
    ← Finset.mul_sum, ← Finset.smul_sum, he, mul_smul_comm, smul_smul, ← add_smul]
  congr 2
  ring

-- eq:radial-laplacian, lem:harmonic-radial: Problem1.harmonic_radial
theorem harmonic_radial (d ℓ j : ℕ) (hj : 1 ≤ j) (h : HAmb d ℓ) : laplacian d (radialQ d ^ j * (h : Ambient d)) = (2 * (j : ℝ) * (2 * (ℓ : ℝ) + ((d : ℝ) + 1) + 2 * (j : ℝ) - 2)) • (radialQ d ^ (j - 1) * (h : Ambient d)) := by
  simpa only [(show laplacian d (h : Ambient d) = 0 from h.property.2), mul_zero, add_zero]
    using euler_radial d ℓ j hj ⟨(h : Ambient d), h.property.1⟩

-- def:fischer-expansion-data: Problem1.FischerIndex
abbrev FischerIndex (n : ℕ) : Type := by
  classical
  exact (
    {j : Fin (n + 1) // 2 * (j : ℕ) ≤ n}
  )

-- def:fischer-expansion-data: Problem1.FischerFamily
abbrev FischerFamily (d n : ℕ) : Type := by
  classical
  exact (
    (j : FischerIndex n) → HAmb d (n - 2 * (j.1 : ℕ))
  )

-- def:fischer-expansion-data: Problem1.fischerSum
noncomputable def fischerSum (d n : ℕ) (g : FischerFamily d n) : Ambient d := by
  classical
  exact (
    ∑ j : FischerIndex n, radialQ d ^ (j.1 : ℕ) * (g j : Ambient d)
  )

-- def:fischer-expansion-data: Problem1.FischerUnique
noncomputable def FischerUnique (d n : ℕ) : Prop := by
  classical
  exact (
    ∀ p : P d n, ∃! g : FischerFamily d n, fischerSum d n g = (p : Ambient d)
  )

-- lem:expansion-degree-linear: Problem1.fischer_sum_mem
theorem fischer_sum_mem (d n : ℕ) (g : FischerFamily d n) : fischerSum d n g ∈ P d n := by
  have hr (k : ℕ) (p : Ambient d) (hp : p ∈ P d k) (j : ℕ) :
      radialQ d ^ j * p ∈ P d (k + 2 * j) := by
    induction j with
    | zero => simpa only [pow_zero, one_mul, mul_zero, add_zero] using hp
    | succ j ih =>
        simpa only [pow_succ', Nat.mul_succ, Nat.add_assoc, mul_assoc] using
          (radial_homogeneous_degree d (k + 2 * j)
            (show radialQ d * (radialQ d ^ j * p) ∈ radialP d (k + 2 * j) from ⟨_, ih, rfl⟩))
  refine (P d n).sum_mem (t := Finset.univ) (fun j _ => ?_)
  simpa only [Nat.sub_add_cancel j.property] using
    hr (n - 2 * (j.1 : ℕ)) (g j) (g j).property.1 (j.1 : ℕ)

-- lem:expansion-degree-linear: Problem1.fischer_sum_add
theorem fischer_sum_add (d n : ℕ) (g h : FischerFamily d n) : fischerSum d n (g + h) = fischerSum d n g + fischerSum d n h := by
  simp [fischerSum, mul_add, Finset.sum_add_distrib]

-- lem:expansion-degree-linear: Problem1.fischer_sum_smul
theorem fischer_sum_smul (d n : ℕ) (a : ℝ) (g : FischerFamily d n) : fischerSum d n (a • g) = a • fischerSum d n g := by
  simp [fischerSum, Finset.smul_sum]

-- lem:expansion-degree-linear: Problem1.fischerSumLinear
noncomputable def fischerSumLinear (d n : ℕ) : FischerFamily d n →ₗ[ℝ] Ambient d := by
  classical
  exact (
    { toFun := fischerSum d n, map_add' := fischer_sum_add d n, map_smul' := fischer_sum_smul d n }
  )

-- lem:fischer-base: Problem1.fischer_base_zero
theorem fischer_base_zero (d : ℕ) : FischerUnique d 0 := by
  letI : Unique (FischerIndex 0) :=
    { default := ⟨0, by decide⟩
      uniq := fun j => Subtype.ext (Fin.ext (by omega)) }
  refine fun p => ⟨uniqueElim ⟨(p : Ambient d), ⟨p.property, degree_zero_harmonic d p⟩⟩, ?_, ?_⟩
  · simp [fischerSum]
  · refine fun h hh => funext (fun i => Subtype.ext ?_)
    rw [Unique.eq_default i]
    simpa [fischerSum, Fintype.sum_unique] using hh

-- lem:fischer-base: Problem1.fischer_base_one
theorem fischer_base_one (d : ℕ) : FischerUnique d 1 := by
  letI : Unique (FischerIndex 1) :=
    { default := ⟨0, by decide⟩
      uniq := fun j => Subtype.ext (Fin.ext (by
        have hj : 2 * (j.1 : ℕ) ≤ 1 := j.property
        change (j.1 : ℕ) = 0
        omega)) }
  refine fun p => ⟨uniqueElim ⟨(p : Ambient d), ⟨p.property, degree_one_harmonic d p⟩⟩, ?_, ?_⟩
  · simp [fischerSum,
      show ((default : FischerIndex 1).1 : ℕ) = 0 from rfl]
  · refine fun h hh => funext (fun i => Subtype.ext ?_)
    rw [Unique.eq_default i]
    simpa [fischerSum, Fintype.sum_unique,
      show ((default : FischerIndex 1).1 : ℕ) = 0 from rfl] using hh

-- lem:fischer-reindex: Problem1.fischer_index_succ_lt
theorem fischer_index_succ_lt (n : ℕ) (j : FischerIndex n) : (j.1 : ℕ) + 1 < n + 2 + 1 := by
  exact lt_trans (Nat.succ_lt_succ j.1.isLt) (Nat.lt_succ_self (n + 2))

-- lem:fischer-reindex: Problem1.fischer_index_succ_bound
theorem fischer_index_succ_bound (n : ℕ) (j : FischerIndex n) : 2 * ((j.1 : ℕ) + 1) ≤ n + 2 := by
  simpa only [Nat.mul_succ] using Nat.add_le_add_right j.property 2

-- lem:fischer-reindex: Problem1.fischerIndexZero
abbrev fischerIndexZero (n : ℕ) : FischerIndex n := by
  classical
  exact (
    ⟨⟨0, Nat.zero_lt_succ n⟩, Nat.zero_le n⟩
  )

-- lem:fischer-reindex: Problem1.fischerIndexSucc
abbrev fischerIndexSucc (n : ℕ) (j : FischerIndex n) : FischerIndex (n + 2) := by
  classical
  exact (
    ⟨⟨(j.1 : ℕ) + 1, fischer_index_succ_lt n j⟩, fischer_index_succ_bound n j⟩
  )

-- lem:fischer-reindex: Problem1.fischerIndexInsert
noncomputable def fischerIndexInsert (n : ℕ) : Option (FischerIndex n) → FischerIndex (n + 2) := by
  classical
  exact (
    fun j => match j with | none => fischerIndexZero (n + 2) | some k => fischerIndexSucc n k
  )

-- lem:fischer-reindex: Problem1.fischer_index_insert_bijective
theorem fischer_index_insert_bijective (n : ℕ) : Function.Bijective (fischerIndexInsert n) := by
  refine ⟨?_, ?_⟩
  · rintro (_ | i) (_ | j) h <;>
      simp_all only [fischerIndexInsert, fischerIndexZero, fischerIndexSucc,
        Subtype.ext_iff, Fin.ext_iff, Nat.zero_ne_add_one, Nat.add_one_ne_zero,
        Option.some.injEq, Nat.add_right_cancel_iff]
  · rintro ⟨⟨k, hklt⟩, hk⟩
    change 2 * k ≤ n + 2 at hk
    cases k with
    | zero => exact ⟨none, rfl⟩
    | succ k => exact ⟨some ⟨⟨k, by omega⟩, (show 2 * k ≤ n from by omega)⟩, rfl⟩

-- lem:fischer-reindex: Problem1.fischerIndexEquiv
noncomputable def fischerIndexEquiv (n : ℕ) : Option (FischerIndex n) ≃ FischerIndex (n + 2) := by
  classical
  exact (
    Equiv.ofBijective (fischerIndexInsert n) (fischer_index_insert_bijective n)
  )

-- lem:fischer-reindex: Problem1.fischer_degree_shift
theorem fischer_degree_shift (n : ℕ) (j : FischerIndex n) : (n + 2) - 2 * ((j.1 : ℕ) + 1) = n - 2 * (j.1 : ℕ) := by
  simp only [Nat.mul_succ, Nat.add_sub_add_right]

-- lem:fischer-reindex: Problem1.fischerFamilySplit
noncomputable def fischerFamilySplit (d n : ℕ) (g : FischerFamily d (n + 2)) : HAmb d (n + 2) × FischerFamily d n := by
  classical
  exact (
    (g (fischerIndexZero (n + 2)), fun j => (fischer_degree_shift n j) ▸ g (fischerIndexSucc n j))
  )

-- lem:fischer-reindex: Problem1.fischer_family_split_bijective
theorem fischer_family_split_bijective (d n : ℕ) : Function.Bijective (fischerFamilySplit d n) := by
  let e := (Equiv.piCongrLeft'
    (fun k : FischerIndex (n + 2) => HAmb d ((n + 2) - 2 * (k.1 : ℕ)))
    (fischerIndexEquiv n).symm).trans Equiv.piOptionEquivProd
  have hcast : Function.Bijective
      (fun f : (j : FischerIndex n) → HAmb d ((n + 2) - 2 * ((j.1 : ℕ) + 1)) =>
        fun j => (fischer_degree_shift n j) ▸ f j) :=
    Function.Bijective.piMap
      (fun j => eq_rec_on_bijective (C := fun k => HAmb d k)
        (fischer_degree_shift n j))
  exact ((Equiv.refl (HAmb d (n + 2))).bijective.prodMap hcast).comp e.bijective

-- lem:fischer-reindex: Problem1.fischerFamilyEquiv
noncomputable def fischerFamilyEquiv (d n : ℕ) : FischerFamily d (n + 2) ≃ (HAmb d (n + 2) × FischerFamily d n) := by
  classical
  exact (
    Equiv.ofBijective (fischerFamilySplit d n) (fischer_family_split_bijective d n)
  )

-- lem:fischer-reindex: Problem1.fischer_reindex_sum
theorem fischer_reindex_sum (d n : ℕ) (g : FischerFamily d (n + 2)) : fischerSum d (n + 2) g = ((fischerFamilySplit d n g).1 : Ambient d) + radialQ d * fischerSum d n (fischerFamilySplit d n g).2 := by
  have hcoe {a b : ℕ} (h : a = b) (p : HAmb d a) :
      ((h ▸ p : HAmb d b) : Ambient d) = (p : Ambient d) := by cases h; rfl
  rw [fischerSum, ← (fischer_index_insert_bijective n).sum_comp]
  simp only [Fintype.sum_option, fischerIndexInsert, fischerIndexZero,
    fischerIndexSucc, fischerFamilySplit, fischerSum, pow_zero, one_mul,
    pow_succ', Finset.mul_sum, mul_assoc, hcoe]

-- def:fischer-coefficients: Problem1.fischerCoefficient
noncomputable def fischerCoefficient (d n : ℕ) (j : FischerIndex n) : ℝ := by
  classical
  exact (
    2 * ((j.1 : ℝ) + 1) * (2 * (n : ℝ) + ((d : ℝ) + 1) - 2 * (j.1 : ℝ))
  )

-- lem:fischer-coefficient-positive: Problem1.fischer_coefficient_positive
theorem fischer_coefficient_positive (d n : ℕ) (j : FischerIndex n) : 0 < fischerCoefficient d n j ∧ fischerCoefficient d n j ≠ 0 := by
  have hj : 2 * (j.1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 2 * (j.1 : ℕ) ≤ n from j.property)
  have hlast : 0 < 2 * (n : ℝ) + ((d : ℝ) + 1) - 2 * (j.1 : ℝ) := by
    linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) d]
  have hp : 0 < fischerCoefficient d n j := mul_pos (by positivity) hlast
  exact ⟨hp, ne_of_gt hp⟩

-- lem:fischer-component-laplacian: Problem1.fischer_component_laplacian
theorem fischer_component_laplacian (d n : ℕ) (j : FischerIndex n) (g : HAmb d (n - 2 * (j.1 : ℕ))) : laplacian d (radialQ d ^ ((j.1 : ℕ) + 1) * (g : Ambient d)) = fischerCoefficient d n j • (radialQ d ^ (j.1 : ℕ) * (g : Ambient d)) := by
  rw [harmonic_radial d _ _ (Nat.succ_le_succ (Nat.zero_le _)) g]
  simp only [Nat.succ_sub_one, Nat.cast_succ, Nat.cast_sub j.property,
    Nat.cast_mul, Nat.cast_zero, fischerCoefficient]
  congr 1
  ring

-- lem:fischer-correction: Problem1.fischerCorrectionQ
noncomputable def fischerCorrectionQ (d n : ℕ) (g : FischerFamily d n) : Ambient d := by
  classical
  exact (
    ∑ j : FischerIndex n, (fischerCoefficient d n j)⁻¹ • (radialQ d ^ (j.1 : ℕ) * (g j : Ambient d))
  )

-- lem:fischer-correction: Problem1.fischerCorrectionR
noncomputable def fischerCorrectionR (d n : ℕ) (g : FischerFamily d n) : Ambient d := by
  classical
  exact (
    radialQ d * fischerCorrectionQ d n g
  )

-- lem:fischer-correction: Problem1.fischer_correction
theorem fischer_correction (d n : ℕ) (g : FischerFamily d n) : fischerCorrectionQ d n g ∈ P d n ∧ fischerCorrectionR d n g ∈ radialP d n ∧ fischerCorrectionR d n g ∈ P d (n + 2) ∧ laplacian d (fischerCorrectionR d n g) = fischerSum d n g := by
  have hQ : fischerCorrectionQ d n g ∈ P d n := by
    simpa [fischerSum, fischerCorrectionQ] using
      fischer_sum_mem d n (fun j => (fischerCoefficient d n j)⁻¹ • g j)
  have hR : fischerCorrectionR d n g ∈ radialP d n := ⟨_, hQ, rfl⟩
  refine ⟨hQ, hR, radial_homogeneous_degree d n hR, ?_⟩
  simp only [fischerCorrectionR, fischerCorrectionQ, Finset.mul_sum,
    mul_smul_comm, ← mul_assoc, ← pow_succ', map_sum, map_smul,
    fischer_component_laplacian, smul_smul, fischerSum,
    fun j => inv_mul_cancel₀ (fischer_coefficient_positive d n j).2, one_smul]

-- lem:fischer-step-existence: Problem1.fischer_step_existence
theorem fischer_step_existence (d n : ℕ) (hU : FischerUnique d n) (p : P d (n + 2)) : ∃ h : HAmb d (n + 2), ∃ q : P d n, (p : Ambient d) = (h : Ambient d) + radialQ d * (q : Ambient d) := by
  obtain ⟨g, hg, _⟩ := hU ⟨laplacian d p, laplacian_homogeneous_degree d n p p.property⟩
  obtain ⟨hQ, _, hR, hΔ⟩ := fischer_correction d n g
  have hh : laplacian d ((p : Ambient d) - fischerCorrectionR d n g) = 0 := by
    rw [map_sub, hΔ, hg, sub_self]
  refine ⟨⟨_, ⟨(P d (n + 2)).sub_mem p.property hR, hh⟩⟩, ⟨_, hQ⟩, ?_⟩
  exact (sub_add_cancel (p : Ambient d) (fischerCorrectionR d n g)).symm

-- lem:fischer-radial-kernel: Problem1.fischer_radial_kernel
theorem fischer_radial_kernel (d n : ℕ) (hU : FischerUnique d n) (h : HAmb d (n + 2)) (q : P d n) (hz : (h : Ambient d) + radialQ d * (q : Ambient d) = 0) : h = 0 ∧ q = 0 := by
  obtain ⟨g, hg, _⟩ := hU q
  have hΔ : laplacian d (radialQ d * (q : Ambient d)) = 0 := by
    simpa only [map_add, (show laplacian d (h : Ambient d) = 0 from h.property.2),
      map_zero, zero_add] using congrArg (laplacian d) hz
  have hsum : fischerSum d n (fun j => fischerCoefficient d n j • g j) = 0 := by
    simpa only [← hg, fischerSum, Finset.mul_sum, ← mul_assoc, ← pow_succ',
      map_sum, fischer_component_laplacian, SetLike.val_smul, mul_smul_comm] using hΔ
  have hgz : (fun j => fischerCoefficient d n j • g j) = (0 : FischerFamily d n) :=
    (hU 0).unique hsum (by simp [fischerSum])
  have hg0 : g = 0 := funext (fun j =>
    (smul_eq_zero_iff_right (fischer_coefficient_positive d n j).2).mp (congrFun hgz j))
  have hq : q = 0 := Subtype.ext (by simpa [hg0, fischerSum] using hg.symm)
  exact ⟨Subtype.ext (by simpa [hq] using hz), hq⟩

-- lem:fischer-step-unique: Problem1.fischer_step_unique
theorem fischer_step_unique (d n : ℕ) (hU : FischerUnique d n) (h h' : HAmb d (n + 2)) (q q' : P d n) (heq : (h : Ambient d) + radialQ d * (q : Ambient d) = (h' : Ambient d) + radialQ d * (q' : Ambient d)) : h = h' ∧ q = q' := by
  have hz : ((h - h' : HAmb d (n + 2)) : Ambient d) +
      radialQ d * ((q - q' : P d n) : Ambient d) = 0 := by
    simpa only [Submodule.coe_sub, mul_sub, sub_add_sub_comm, sub_eq_zero] using heq
  simpa only [sub_eq_zero] using fischer_radial_kernel d n hU (h - h') (q - q') hz

-- lem:fischer-induction-step: Problem1.fischer_induction_step
theorem fischer_induction_step (d n : ℕ) (hU : FischerUnique d n) : FischerUnique d (n + 2) := by
  intro p
  obtain ⟨h, q, hpq⟩ := fischer_step_existence d n hU p
  obtain ⟨g, hg, hgu⟩ := hU q
  have hsplit : fischerFamilySplit d n ((fischerFamilyEquiv d n).symm (h, g)) = (h, g) :=
    (fischerFamilyEquiv d n).apply_symm_apply (h, g)
  refine ⟨(fischerFamilyEquiv d n).symm (h, g), ?_, ?_⟩
  · simpa only [fischer_reindex_sum, hsplit, hg] using hpq.symm
  · intro y hy
    have hd := fischer_step_unique d n hU (fischerFamilySplit d n y).1 h
      ⟨fischerSum d n (fischerFamilySplit d n y).2, fischer_sum_mem d n _⟩ q
      (by simpa only [← fischer_reindex_sum, hy] using hpq)
    exact (fischer_family_split_bijective d n).1
      ((Prod.ext hd.1 (hgu _ (congrArg Subtype.val hd.2))).trans hsplit.symm)

-- eq:fischer-full, prop:fischer: Problem1.fischer
theorem fischer (d n : ℕ) : FischerUnique d n := by
  exact Nat.twoStepInduction (fischer_base_zero d) (fischer_base_one d)
    (fun k ih _ => fischer_induction_step d k ih) n

-- cor:fischer-submodules, eq:fischer-one-step: Problem1.fischer_submodules
theorem fischer_submodules (d n : ℕ) : P d (n + 2) = HAmb d (n + 2) ⊔ radialP d n ∧ HAmb d (n + 2) ⊓ radialP d n = ⊥ := by
  refine ⟨le_antisymm ?_ (sup_le (show HAmb d (n + 2) ≤ P d (n + 2) from inf_le_left)
    (radial_homogeneous_degree d n)), ?_⟩
  · intro p hp
    obtain ⟨h, q, hpq⟩ := fischer_step_existence d n (fischer d n) ⟨p, hp⟩
    exact Submodule.mem_sup'.mpr
      ⟨h, ⟨radialQ d * (q : Ambient d), ⟨q, q.property, rfl⟩⟩, hpq.symm⟩
  · refine (Submodule.eq_bot_iff _).mpr ?_
    rintro p ⟨hh, q, hq, rfl⟩
    exact congrArg Subtype.val (fischer_radial_kernel d n (fischer d n)
      ⟨radialQ d * q, hh⟩ ⟨-q, (P d n).neg_mem hq⟩
      (by simp only [mul_neg, add_neg_cancel])).1

-- cor:fischer-submodules, eq:fischer-one-step: Problem1.fischer_base_submodules
theorem fischer_base_submodules (d : ℕ) : P d 0 = HAmb d 0 ∧ P d 1 = HAmb d 1 := by
  exact ⟨le_antisymm (fun p hp => ⟨hp, degree_zero_harmonic d ⟨p, hp⟩⟩) inf_le_left,
    le_antisymm (fun p hp => ⟨hp, degree_one_harmonic d ⟨p, hp⟩⟩) inf_le_left⟩

-- cor:fischer-product-equiv: Problem1.fischer_pair_mem
theorem fischer_pair_mem (d n : ℕ) (v : HAmb d (n + 2) × radialP d n) : (v.1 : Ambient d) + (v.2 : Ambient d) ∈ P d (n + 2) := by
  simpa only [(fischer_submodules d n).1] using Submodule.add_mem_sup v.1.property v.2.property

-- cor:fischer-product-equiv: Problem1.fischerPairFunction
noncomputable def fischerPairFunction (d n : ℕ) (v : HAmb d (n + 2) × radialP d n) : P d (n + 2) := by
  classical
  exact (
    ⟨(v.1 : Ambient d) + (v.2 : Ambient d), fischer_pair_mem d n v⟩
  )

-- cor:fischer-product-equiv: Problem1.fischer_pair_add
theorem fischer_pair_add (d n : ℕ) (u v : HAmb d (n + 2) × radialP d n) : fischerPairFunction d n (u + v) = fischerPairFunction d n u + fischerPairFunction d n v := by
  exact Subtype.ext (add_add_add_comm _ _ _ _)

-- cor:fischer-product-equiv: Problem1.fischer_pair_smul
theorem fischer_pair_smul (d n : ℕ) (a : ℝ) (v : HAmb d (n + 2) × radialP d n) : fischerPairFunction d n (a • v) = a • fischerPairFunction d n v := by
  exact Subtype.ext (smul_add a _ _).symm

-- cor:fischer-product-equiv: Problem1.fischerPairLinear
noncomputable def fischerPairLinear (d n : ℕ) : (HAmb d (n + 2) × radialP d n) →ₗ[ℝ] P d (n + 2) := by
  classical
  exact (
    { toFun := fischerPairFunction d n, map_add' := fischer_pair_add d n, map_smul' := fischer_pair_smul d n }
  )

-- cor:fischer-product-equiv: Problem1.fischer_pair_bijective
theorem fischer_pair_bijective (d n : ℕ) : Function.Bijective (fischerPairLinear d n) := by
  refine ⟨LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_), ?_⟩
  · intro v hv
    have he : (v.1 : Ambient d) + (v.2 : Ambient d) = 0 := congrArg Subtype.val hv
    have h1 : (v.1 : Ambient d) = 0 := (Submodule.eq_bot_iff _).mp
      (fischer_submodules d n).2 _ ⟨v.1.property,
        (eq_neg_of_add_eq_zero_left he).symm ▸ (radialP d n).neg_mem v.2.property⟩
    exact Prod.ext (Subtype.ext h1) (show v.2 = 0 from
      Subtype.ext (by simpa only [h1, zero_add, Submodule.coe_zero] using he))
  · intro p
    obtain ⟨h, q, hpq⟩ := Submodule.mem_sup'.mp
      (show (p : Ambient d) ∈ HAmb d (n + 2) ⊔ radialP d n from
        (fischer_submodules d n).1 ▸ p.property)
    exact ⟨(h, q), Subtype.ext hpq⟩

-- cor:fischer-product-equiv: Problem1.fischerProductEquiv
noncomputable def fischerProductEquiv (d n : ℕ) : (HAmb d (n + 2) × radialP d n) ≃ₗ[ℝ] P d (n + 2) := by
  classical
  exact (
    LinearEquiv.ofBijective (fischerPairLinear d n) (fischer_pair_bijective d n)
  )

-- cor:fischer-product-equiv: Problem1.fischerProductEquiv_apply
theorem fischerProductEquiv_apply (d n : ℕ) (v : HAmb d (n + 2) × radialP d n) : (fischerProductEquiv d n v : Ambient d) = (v.1 : Ambient d) + (v.2 : Ambient d) := by
  rfl

-- def:coordinate-rotation-bundled: Problem1.ambientRotationDerivative
noncomputable def ambientRotationDerivative (d : ℕ) (p : SphereRotationPair d) : Ambient d → Ambient d := by
  classical
  exact (
    fun F => MvPolynomial.X p.val.1 * MvPolynomial.pderiv p.val.2 F - MvPolynomial.X p.val.2 * MvPolynomial.pderiv p.val.1 F
  )

-- def:coordinate-rotation-bundled: Problem1.sphereRotationDerivative
noncomputable def sphereRotationDerivative (d : ℕ) (p : SphereRotationPair d) : ((Sphere d → ℝ) → Sphere d → ℝ) := by
  classical
  exact (
    fun f x => deriv (fun t => f (sphereAction (planeRotation d p t) x)) 0
  )

-- lem:ambient-rotation-degree: Problem1.ambientRotation_add
theorem ambientRotation_add (d : ℕ) (p : SphereRotationPair d) (F G : Ambient d) : ambientRotationDerivative d p (F + G) = ambientRotationDerivative d p F + ambientRotationDerivative d p G := by
  simp only [ambientRotationDerivative, map_add, mul_add, add_sub_add_comm]

-- lem:ambient-rotation-degree: Problem1.ambientRotation_smul
theorem ambientRotation_smul (d : ℕ) (p : SphereRotationPair d) (a : ℝ) (F : Ambient d) : ambientRotationDerivative d p (a • F) = a • ambientRotationDerivative d p F := by
  simp only [ambientRotationDerivative, formal_derivative_smul, mul_smul_comm, smul_sub]

-- lem:ambient-rotation-degree: Problem1.ambientRotationLinear
noncomputable def ambientRotationLinear (d : ℕ) (p : SphereRotationPair d) : Ambient d →ₗ[ℝ] Ambient d := by
  classical
  exact (
    { toFun := ambientRotationDerivative d p, map_add' := ambientRotation_add d p, map_smul' := ambientRotation_smul d p }
  )

-- lem:ambient-rotation-degree: Problem1.ambientRotation_mem_ambientLE
theorem ambientRotation_mem_ambientLE (d : ℕ) (L : ℕ) (p : SphereRotationPair d) (F : Ambient d) (hF : F ∈ AmbientLE d L) : ambientRotationDerivative d p F ∈ AmbientLE d L := by
  classical
  have hmon (i j : Fin (d + 1)) (m : Fin (d + 1) →₀ ℕ) (c : ℝ)
      (hm : m.sum (fun _ e => e) ≤ L) :
      MvPolynomial.X i * MvPolynomial.pderiv j (MvPolynomial.monomial m c) ∈
        AmbientLE d L := by
    by_cases hj : m j = 0
    · simp only [MvPolynomial.pderiv_monomial, hj, Nat.cast_zero, mul_zero,
        map_zero, (AmbientLE d L).zero_mem]
    have hsum := congrArg (fun u : Fin (d + 1) →₀ ℕ => u.sum (fun _ e => e))
      (Finsupp.sub_add_single_one_cancel hj)
    simp only [Finsupp.sum_add_index' (h := fun (_ : Fin (d + 1)) (e : ℕ) => e)
        (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index (h := fun (_ : Fin (d + 1)) (e : ℕ) => e) (by rfl)] at hsum
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul,
      one_mul, AmbientLE, MvPolynomial.mem_restrictTotalDegree]
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    change (Finsupp.single i 1 + (m - Finsupp.single j 1)).sum (fun _ e => e) ≤ L
    simpa only [Finsupp.sum_add_index' (h := fun (_ : Fin (d + 1)) (e : ℕ) => e)
        (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index (h := fun (_ : Fin (d + 1)) (e : ℕ) => e) (by rfl),
      Nat.add_comm 1, hsum] using hm
  change ambientRotationLinear d p F ∈ AmbientLE d L
  rw [MvPolynomial.as_sum F, map_sum]
  exact (AmbientLE d L).sum_mem fun m hm => (AmbientLE d L).sub_mem
    (hmon p.val.1 p.val.2 m _ ((MvPolynomial.le_totalDegree hm).trans
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hF)))
    (hmon p.val.2 p.val.1 m _ ((MvPolynomial.le_totalDegree hm).trans
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hF)))

-- lem:ambient-rotation-degree: Problem1.ambientRotation_mem_homogeneous
theorem ambientRotation_mem_homogeneous (d : ℕ) (n : ℕ) (p : SphereRotationPair d) (F : Ambient d) (hF : F ∈ P d n) : ambientRotationDerivative d p F ∈ P d n := by
  cases n with
  | zero =>
    have hC : F = MvPolynomial.C (MvPolynomial.coeff 0 F) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (d + 1))).mpr hF)
    rw [hC]
    simpa only [ambientRotationDerivative, MvPolynomial.pderiv_C, mul_zero,
      sub_self] using (P d 0).zero_mem
  | succ n =>
    simpa only [ambientRotationDerivative, Nat.add_comm 1] using
      (P d (1 + n)).sub_mem
        ((MvPolynomial.isHomogeneous_X ℝ p.val.1).mul
          (show MvPolynomial.IsHomogeneous (MvPolynomial.pderiv p.val.2 F) n from
            partial_homogeneous_degree d n p.val.2 F hF))
        ((MvPolynomial.isHomogeneous_X ℝ p.val.2).mul
          (show MvPolynomial.IsHomogeneous (MvPolynomial.pderiv p.val.1 F) n from
            partial_homogeneous_degree d n p.val.1 F hF))

-- lem:rotation-curve-certificate: Problem1.rotation_curve_hasDerivAt
theorem rotation_curve_hasDerivAt (d : ℕ) (p : SphereRotationPair d) (F : Ambient d) (x : Sphere d) (t : ℝ) : HasDerivAt (fun τ => polynomialEval d F (sphereAction (planeRotation d p τ) x)) (polynomialEval d (ambientRotationDerivative d p F) (sphereAction (planeRotation d p t) x)) t := by
  convert polynomial_curve_derivative d F
    (fun u => (sphereAction (planeRotation d p u) x : Euclidean d)) _ t
    (planeRotation_coord_hasDerivAt d p x t) using 1
  simp +contextual [polynomialEval, ambientRotationDerivative, Finset.sum_ite,
    Finset.filter_eq', (ne_of_lt p.property).symm, sub_eq_add_neg, mul_comm, add_comm]

-- lem:rotation-curve-certificate: Problem1.rotation_curve_deriv
theorem rotation_curve_deriv (d : ℕ) (p : SphereRotationPair d) (F : Ambient d) (x : Sphere d) (t : ℝ) : deriv (fun τ => polynomialEval d F (sphereAction (planeRotation d p τ) x)) t = polynomialEval d (ambientRotationDerivative d p F) (sphereAction (planeRotation d p t) x) := by
  exact (rotation_curve_hasDerivAt d p F x t).deriv

-- eq:D-restriction-compatibility, lem:intrinsic-rotation-compatibility: Problem1.intrinsic_rotation_compatibility
theorem intrinsic_rotation_compatibility (d : ℕ) (p : SphereRotationPair d) (F : Ambient d) : sphereRotationDerivative d p (restriction d F) = (restriction d (ambientRotationDerivative d p F) : Sphere d → ℝ) := by
  funext x
  simpa only [sphereRotationDerivative, restriction_apply, planeRotation_zero,
    sphereAction, sphereActionN_one] using (rotation_curve_deriv d p F x 0)

-- lem:rotation-representative-independent: Problem1.rotation_representative_independent
theorem rotation_representative_independent (d : ℕ) (p : SphereRotationPair d) (F G : Ambient d) (hFG : restriction d F = restriction d G) : restriction d (ambientRotationDerivative d p F) = restriction d (ambientRotationDerivative d p G) := by
  apply DFunLike.coe_injective
  rw [← intrinsic_rotation_compatibility, ← intrinsic_rotation_compatibility, hFG]

-- lem:rotation-second-derivative: Problem1.rotation_curve_second_hasDerivAt
theorem rotation_curve_second_hasDerivAt (d : ℕ) (p : SphereRotationPair d) (F : Ambient d) (x : Sphere d) (t : ℝ) : HasDerivAt (deriv (fun τ => polynomialEval d F (sphereAction (planeRotation d p τ) x))) (polynomialEval d (ambientRotationDerivative d p (ambientRotationDerivative d p F)) (sphereAction (planeRotation d p t) x)) t := by
  convert rotation_curve_hasDerivAt d p (ambientRotationDerivative d p F) x t using 1
  exact funext (fun u => rotation_curve_deriv d p F x u)

-- lem:rotation-second-derivative: Problem1.rotation_second_derivative
theorem rotation_second_derivative (d : ℕ) (p : SphereRotationPair d) (F : Ambient d) (x : Sphere d) : sphereRotationDerivative d p (sphereRotationDerivative d p (restriction d F)) x = polynomialEval d (ambientRotationDerivative d p (ambientRotationDerivative d p F)) x ∧ polynomialEval d (ambientRotationDerivative d p (ambientRotationDerivative d p F)) x = deriv (deriv (fun t => polynomialEval d F (sphereAction (planeRotation d p t) x))) 0 := by
  constructor
  · simp only [intrinsic_rotation_compatibility, restriction_apply]
  · simpa only [planeRotation_zero, sphereAction, sphereActionN_one] using
      (rotation_curve_second_hasDerivAt d p F x 0).deriv.symm

-- lem:intrinsic-rotation-closure: Problem1.sphereRotation_continuous
theorem sphereRotation_continuous (d : ℕ) (L : ℕ) (p : SphereRotationPair d) (f : Pi d L) : Continuous (sphereRotationDerivative d p f) := by
  obtain ⟨F, hF⟩ := f.property
  change restriction d (F : Ambient d) = (f : C(Sphere d, ℝ)) at hF
  simpa only [← hF, intrinsic_rotation_compatibility] using
    (restriction d (ambientRotationDerivative d p (F : Ambient d))).continuous

-- lem:intrinsic-rotation-closure: Problem1.sphereRotationContinuous
noncomputable def sphereRotationContinuous (d : ℕ) (L : ℕ) (p : SphereRotationPair d) (f : Pi d L) : C(Sphere d, ℝ) := by
  classical
  exact (
    { toFun := sphereRotationDerivative d p f, continuous_toFun := sphereRotation_continuous d L p f }
  )

-- lem:intrinsic-rotation-closure: Problem1.sphereRotation_mem
theorem sphereRotation_mem (d : ℕ) (L : ℕ) (p : SphereRotationPair d) (f : Pi d L) : sphereRotationContinuous d L p f ∈ Pi d L := by
  obtain ⟨F, hF⟩ := f.property
  refine ⟨⟨ambientRotationDerivative d p (F : Ambient d),
    ambientRotation_mem_ambientLE d L p F F.property⟩, ?_⟩
  exact DFunLike.coe_injective ((intrinsic_rotation_compatibility d p F).symm.trans
    (congrArg (fun g : C(Sphere d, ℝ) => sphereRotationDerivative d p g) hF))

-- lem:intrinsic-rotation-linearity: Problem1.sphereRotation_add
theorem sphereRotation_add (d : ℕ) (L : ℕ) (p : SphereRotationPair d) (f g : Pi d L) : sphereRotationDerivative d p (fun x => (f : C(Sphere d, ℝ)) x + (g : C(Sphere d, ℝ)) x) = fun x => sphereRotationDerivative d p f x + sphereRotationDerivative d p g x := by
  obtain ⟨F, hF⟩ := f.property
  obtain ⟨G, hG⟩ := g.property
  simp only [boundedRestriction, LinearMap.domRestrict_apply] at hF hG
  simpa only [ambientRotation_add, map_add, ContinuousMap.coe_add,
    ← intrinsic_rotation_compatibility, hF, hG, Pi.add_def] using
    (intrinsic_rotation_compatibility d p ((F : Ambient d) + G))

-- lem:intrinsic-rotation-linearity: Problem1.sphereRotation_smul
theorem sphereRotation_smul (d : ℕ) (L : ℕ) (p : SphereRotationPair d) (a : ℝ) (f : Pi d L) : sphereRotationDerivative d p (fun x => a * (f : C(Sphere d, ℝ)) x) = fun x => a * sphereRotationDerivative d p f x := by
  obtain ⟨F, hF⟩ := f.property
  simp only [boundedRestriction, LinearMap.domRestrict_apply] at hF
  simpa only [ambientRotation_smul, map_smul, ContinuousMap.coe_smul,
    ← intrinsic_rotation_compatibility, hF, Pi.smul_def, smul_eq_mul] using
    (intrinsic_rotation_compatibility d p (a • (F : Ambient d)))

-- lem:intrinsic-rotation-linear-map: Problem1.sphereRotationCarrier
noncomputable def sphereRotationCarrier (d : ℕ) (L : ℕ) (p : SphereRotationPair d) : Pi d L → Pi d L := by
  classical
  exact (
    fun f => ⟨sphereRotationContinuous d L p f, sphereRotation_mem d L p f⟩
  )

-- lem:intrinsic-rotation-linear-map: Problem1.sphereRotationCarrier_add
theorem sphereRotationCarrier_add (d : ℕ) (L : ℕ) (p : SphereRotationPair d) (f g : Pi d L) : sphereRotationCarrier d L p (f + g) = sphereRotationCarrier d L p f + sphereRotationCarrier d L p g := by
  exact Subtype.ext (DFunLike.coe_injective (sphereRotation_add d L p f g))

-- lem:intrinsic-rotation-linear-map: Problem1.sphereRotationCarrier_smul
theorem sphereRotationCarrier_smul (d : ℕ) (L : ℕ) (p : SphereRotationPair d) (a : ℝ) (f : Pi d L) : sphereRotationCarrier d L p (a • f) = a • sphereRotationCarrier d L p f := by
  exact Subtype.ext (DFunLike.coe_injective (sphereRotation_smul d L p a f))

-- lem:intrinsic-rotation-linear-map: Problem1.sphereRotationLinear
noncomputable def sphereRotationLinear (d : ℕ) (L : ℕ) (p : SphereRotationPair d) : Pi d L →ₗ[ℝ] Pi d L := by
  classical
  exact (
    { toFun := sphereRotationCarrier d L p, map_add' := sphereRotationCarrier_add d L p, map_smul' := sphereRotationCarrier_smul d L p }
  )

-- lem:intrinsic-rotation-linear-map: Problem1.sphereRotationLinear_apply
theorem sphereRotationLinear_apply (d : ℕ) (L : ℕ) (p : SphereRotationPair d) (f : Pi d L) (x : Sphere d) : (sphereRotationLinear d L p f : C(Sphere d, ℝ)) x = sphereRotationDerivative d p f x := by
  rfl

-- def:typed-casimir, eq:typed-casimir: Problem1.casimir
noncomputable def casimir (d : ℕ) (L : ℕ) : Pi d L →ₗ[ℝ] Pi d L := by
  classical
  exact (
    - ∑ p : SphereRotationPair d, (sphereRotationLinear d L p).comp (sphereRotationLinear d L p)
  )

-- lem:rotation-degree-inclusion: Problem1.rotation_degree_inclusion
theorem rotation_degree_inclusion (d : ℕ) (L L' : ℕ) (hLL' : L ≤ L') (p : SphereRotationPair d) : (piInclusion d L L' hLL').comp (sphereRotationLinear d L p) = (sphereRotationLinear d L' p).comp (piInclusion d L L' hLL') := by
  rfl

-- lem:casimir-degree-inclusion: Problem1.casimir_degree_inclusion
theorem casimir_degree_inclusion (d : ℕ) (L L' : ℕ) (hLL' : L ≤ L') : (piInclusion d L L' hLL').comp (casimir d L) = (casimir d L').comp (piInclusion d L L' hLL') := by
  refine LinearMap.ext (fun f => ?_)
  simp only [casimir, LinearMap.comp_apply, LinearMap.neg_apply,
    LinearMap.sum_apply, map_neg, map_sum]
  rfl

-- lem:casimir-square-expansion: Problem1.casimir_square_expansion
theorem casimir_square_expansion (d : ℕ) (p : SphereRotationPair d) (F : Ambient d) : ambientRotationDerivative d p (ambientRotationDerivative d p F) = MvPolynomial.X p.val.1 ^ 2 * MvPolynomial.pderiv p.val.2 (MvPolynomial.pderiv p.val.2 F) + MvPolynomial.X p.val.2 ^ 2 * MvPolynomial.pderiv p.val.1 (MvPolynomial.pderiv p.val.1 F) - (2 : ℝ) • (MvPolynomial.X p.val.1 * MvPolynomial.X p.val.2 * MvPolynomial.pderiv p.val.1 (MvPolynomial.pderiv p.val.2 F)) - MvPolynomial.X p.val.1 * MvPolynomial.pderiv p.val.1 F - MvPolynomial.X p.val.2 * MvPolynomial.pderiv p.val.2 F := by
  simp only [ambientRotationDerivative, map_sub, formal_derivative_mul,
    formal_derivative_X, if_true, if_neg (ne_of_lt p.property),
    if_neg (ne_of_lt p.property).symm, one_mul, zero_mul, zero_add,
    mixed_partials d F p.val.2 p.val.1, two_smul ℝ, pow_two]
  ring

-- lem:euler-square: Problem1.euler_square
theorem euler_square (d : ℕ) (F : Ambient d) : eulerOperator d (eulerOperator d F) = eulerOperator d F + ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.pderiv i (MvPolynomial.pderiv j F) := by
  classical
  simp [eulerOperator, mul_add, Finset.sum_add_distrib, mul_ite, mul_assoc,
    Pi.single_apply]
  rw [Finset.sum_comm, add_comm]

-- lem:casimir-pair-sums: Problem1.casimir_pair_sums
theorem casimir_pair_sums (d : ℕ) {V : Type*} [AddCommGroup V] [Module ℝ V] (B : Fin (d + 1) → Fin (d + 1) → V) (hB : ∀ i j, B i j = B j i) : (2 : ℝ) • (∑ p : SphereRotationPair d, B p.val.1 p.val.2) = ∑ i : Fin (d + 1), ∑ j ∈ Finset.univ.erase i, B i j := by
  classical
  have hpair : (∑ p : SphereRotationPair d, B p.val.1 p.val.2) =
      ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), if i < j then B i j else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter
      (fun p : Fin (d + 1) × Fin (d + 1) => p.1 < p.2)) (by simp)
      (fun p => B p.1 p.2)]
    simp only [Finset.sum_filter, Fintype.sum_prod_type]
  rw [hpair, two_smul ℝ]
  conv_lhs => rhs; rw [Finset.sum_comm]
  simp only [← Finset.sum_add_distrib, ← Finset.filter_ne', Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rcases lt_trichotomy i j with hij | hij | hij <;>
    simp_all [lt_asymm, ne_of_lt, ne_of_gt]

-- lem:pair-incidence: Problem1.pair_incidence
theorem pair_incidence (d : ℕ) {V : Type*} [AddCommGroup V] [Module ℝ V] (A : Fin (d + 1) → V) : (∑ p : SphereRotationPair d, (A p.val.1 + A p.val.2)) = (d : ℝ) • ∑ i : Fin (d + 1), A i := by
  classical
  have h := casimir_pair_sums d (fun i j => A i + A j) (fun _ _ => add_comm _ _)
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
    ← Nat.cast_smul_eq_nsmul ℝ] at h
  rw [Finset.sum_add_distrib]
  apply smul_right_injective V (by norm_num : (2 : ℝ) ≠ 0)
  simp only [smul_add, h]
  module

-- lem:casimir-second-order-sum: Problem1.casimir_second_order_sum
theorem casimir_second_order_sum (d : ℕ) (F : Ambient d) : (∑ p : SphereRotationPair d, (MvPolynomial.X p.val.1 ^ 2 * MvPolynomial.pderiv p.val.2 (MvPolynomial.pderiv p.val.2 F) + MvPolynomial.X p.val.2 ^ 2 * MvPolynomial.pderiv p.val.1 (MvPolynomial.pderiv p.val.1 F) - (2 : ℝ) • (MvPolynomial.X p.val.1 * MvPolynomial.X p.val.2 * MvPolynomial.pderiv p.val.1 (MvPolynomial.pderiv p.val.2 F)))) = radialQ d * laplacian d F - ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.pderiv i (MvPolynomial.pderiv j F) := by
  classical
  let B (i j : Fin (d + 1)) : Ambient d :=
    MvPolynomial.X i ^ 2 * MvPolynomial.pderiv j (MvPolynomial.pderiv j F) +
    MvPolynomial.X j ^ 2 * MvPolynomial.pderiv i (MvPolynomial.pderiv i F) -
    (2 : ℝ) • (MvPolynomial.X i * MvPolynomial.X j *
      MvPolynomial.pderiv i (MvPolynomial.pderiv j F))
  have hB : ∀ i j, B i j = B j i := by
    intro i j
    simp only [B, mixed_partials d F j i, two_smul ℝ]
    ring
  have hdiag : ∀ i, B i i = 0 := by
    intro i
    simp [B, two_smul ℝ, pow_two]
  have h : (2 : ℝ) • (∑ p : SphereRotationPair d, B p.val.1 p.val.2) =
      ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), B i j := by
    simpa [hdiag] using casimir_pair_sums d B hB
  have hsum : (∑ i : Fin (d + 1), ∑ j : Fin (d + 1), B i j) =
      (2 : ℝ) • (radialQ d * laplacian d F -
        ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
          MvPolynomial.X i * MvPolynomial.X j *
            MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) := by
    simp only [B, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.smul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    simp [radialQ, laplacian, two_smul ℝ, sub_add_sub_comm]
  exact smul_right_injective (Ambient d) (by norm_num : (2 : ℝ) ≠ 0) (h.trans hsum)

-- eq:casimir-ambient, lem:casimir: Problem1.casimir_ambient
theorem casimir_ambient (d : ℕ) (F : Ambient d) : (∑ p : SphereRotationPair d, ambientRotationDerivative d p (ambientRotationDerivative d p F)) = radialQ d * laplacian d F - eulerOperator d (eulerOperator d F) - ((d : ℝ) - 1) • eulerOperator d F := by
  classical
  have hsecond := casimir_second_order_sum d F
  simp only [Finset.sum_sub_distrib] at hsecond
  simp only [casimir_square_expansion, Finset.sum_sub_distrib]
  rw [hsecond, sub_sub, ← Finset.sum_add_distrib,
    pair_incidence d (fun i => MvPolynomial.X i * MvPolynomial.pderiv i F)]
  rw [euler_square]
  simp only [eulerOperator, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply]
  module

-- lem:ambient-casimir-eigenvalue: Problem1.ambient_casimir_eigenvalue
theorem ambient_casimir_eigenvalue (d : ℕ) (n : ℕ) (H : HAmb d n) : -(∑ p : SphereRotationPair d, ambientRotationDerivative d p (ambientRotationDerivative d p (H : Ambient d))) = ((n : ℝ) * ((n : ℝ) + (d : ℝ) - 1)) • (H : Ambient d) := by
  have hL : laplacian d (H : Ambient d) = 0 := H.property.2
  have hE : eulerOperator d (H : Ambient d) = (n : ℝ) • (H : Ambient d) :=
    euler d n ⟨(H : Ambient d), H.property.1⟩
  simp only [casimir_ambient, hL, mul_zero, hE, map_smul]
  module

-- eq:casimir-eigenvalue, lem:casimir-eigenvalue: Problem1.casimir_eigenvalue
theorem casimir_eigenvalue (d : ℕ) (n : ℕ) (h : Harmonic d n) : casimir d n (harmonicPiInclusion d n n le_rfl h) = ((n : ℝ) * ((n : ℝ) + (d : ℝ) - 1)) • harmonicPiInclusion d n n le_rfl h := by
  classical
  obtain ⟨F, hF⟩ := h.property
  simp only [harmonicRestriction, LinearMap.domRestrict_apply] at hF
  refine Subtype.ext (ContinuousMap.ext (fun x => ?_))
  have ha := congrArg (fun G : Ambient d => restriction d G x)
    (ambient_casimir_eigenvalue d n F)
  simp [casimir, sphereRotationLinear_apply]
  change -(∑ p : SphereRotationPair d,
    sphereRotationDerivative d p (sphereRotationDerivative d p (h : C(Sphere d, ℝ))) x) =
    ((n : ℝ) * ((n : ℝ) + (d : ℝ) - 1)) * (h : C(Sphere d, ℝ)) x
  simpa [← hF, intrinsic_rotation_compatibility] using ha

-- cor:casimir-eigenvalue-inclusion: Problem1.casimir_eigenvalue_inclusion
theorem casimir_eigenvalue_inclusion (d : ℕ) (n L : ℕ) (hnL : n ≤ L) (h : Harmonic d n) : casimir d L (harmonicPiInclusion d n L hnL h) = ((n : ℝ) * ((n : ℝ) + (d : ℝ) - 1)) • harmonicPiInclusion d n L hnL h := by
  have he := congrArg (piInclusion d n L hnL) (casimir_eigenvalue d n h)
  have hc := DFunLike.congr_fun (casimir_degree_inclusion d n L hnL)
    (harmonicPiInclusion d n n le_rfl h)
  have hi : piInclusion d n L hnL (harmonicPiInclusion d n n le_rfl h) =
      harmonicPiInclusion d n L hnL h :=
    DFunLike.congr_fun (harmonicPiInclusion_trans d n n L le_rfl hnL) h
  simpa only [LinearMap.comp_apply, map_smul, hi] using hc.symm.trans he

-- lem:continuous-square-definite: Problem1.continuous_square_definite
theorem continuous_square_definite (d : ℕ) (hd : 2 ≤ d) (f : C(Sphere d, ℝ)) (hf : (∫ x, (f x) ^ 2 ∂sigma d) = 0) : f = 0 := by
  have hae : (fun x : Sphere d => (f x) ^ 2) =ᵐ[sigma d] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x))
      (continuous_product_integrable d hd f f).2.2).mp hf
  have heq := ((f.continuous.pow 2).ae_eq_iff_eq (μ := sigma d) continuous_const).mp hae
  exact ContinuousMap.ext (fun x => sq_eq_zero_iff.mp (congrFun heq x))

-- def:harmonic-L2-carrier: Problem1.HarmonicL2
structure HarmonicL2 (d : ℕ) (n : ℕ) where
  ambient : HAmb d n

-- lem:harmonic-wrapper-linear: Problem1.harmonicL2_eta
theorem harmonicL2_eta (d : ℕ) (n : ℕ) (u : HarmonicL2 d n) : (⟨u.ambient⟩ : HarmonicL2 d n) = u := by
  rfl

-- lem:harmonic-wrapper-linear: Problem1.harmonicL2_ambient_mk
theorem harmonicL2_ambient_mk (d : ℕ) (n : ℕ) (H : HAmb d n) : (⟨H⟩ : HarmonicL2 d n).ambient = H := by
  rfl

-- lem:harmonic-wrapper-linear: Problem1.harmonicL2Equiv
noncomputable def harmonicL2Equiv (d : ℕ) (n : ℕ) : HarmonicL2 d n ≃ HAmb d n := by
  classical
  exact (
    { toFun := HarmonicL2.ambient, invFun := fun H => ⟨H⟩, left_inv := harmonicL2_eta d n, right_inv := harmonicL2_ambient_mk d n }
  )

-- def:harmonic-L2-carrier, lem:harmonic-wrapper-linear: Problem1.harmonicL2AddCommGroup
noncomputable instance harmonicL2AddCommGroup (d : ℕ) (n : ℕ) : AddCommGroup (HarmonicL2 d n) := by
  classical
  exact (
    (harmonicL2Equiv d n).addCommGroup
  )

-- lem:harmonic-wrapper-linear: Problem1.harmonicL2Module
noncomputable instance harmonicL2Module (d : ℕ) (n : ℕ) : Module ℝ (HarmonicL2 d n) := by
  classical
  exact (
    (harmonicL2Equiv d n).module ℝ
  )

-- lem:harmonic-wrapper-linear: Problem1.harmonicL2Forget
noncomputable def harmonicL2Forget (d : ℕ) (n : ℕ) : HarmonicL2 d n ≃ₗ[ℝ] HAmb d n := by
  classical
  exact (
    (harmonicL2Equiv d n).linearEquiv ℝ
  )

-- def:harmonic-L2-carrier, lem:harmonic-wrapper-linear: Problem1.harmonicL2_componentwise
theorem harmonicL2_componentwise (d : ℕ) (n : ℕ) (u v : HarmonicL2 d n) (a : ℝ) : (0 : HarmonicL2 d n).ambient = 0 ∧ (u + v).ambient = u.ambient + v.ambient ∧ (-u).ambient = -u.ambient ∧ (a • u).ambient = a • u.ambient := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- lem:harmonic-wrapper-linear: Problem1.harmonicL2Forget_apply
theorem harmonicL2Forget_apply (d : ℕ) (n : ℕ) (u : HarmonicL2 d n) : harmonicL2Forget d n u = u.ambient := by
  rfl

-- lem:harmonic-wrapper-linear: Problem1.harmonicL2Forget_symm_apply
theorem harmonicL2Forget_symm_apply (d : ℕ) (n : ℕ) (H : HAmb d n) : (harmonicL2Forget d n).symm H = (⟨H⟩ : HarmonicL2 d n) := by
  rfl

-- lem:harmonic-wrapper-finite: Problem1.harmonicL2_finiteDimensional
noncomputable instance harmonicL2_finiteDimensional (d : ℕ) (n : ℕ) : FiniteDimensional ℝ (HarmonicL2 d n) := by
  exact Module.Finite.equiv (harmonicL2Forget d n).symm

-- lem:harmonic-wrapper-finite: Problem1.harmonicL2_finrank_ambient
theorem harmonicL2_finrank_ambient (d : ℕ) (n : ℕ) : Module.finrank ℝ (HarmonicL2 d n) = Module.finrank ℝ (HAmb d n) := by
  exact (harmonicL2Forget d n).finrank_eq

-- def:harmonic-integral-pairing: Problem1.harmonicIntegralPairing
noncomputable def harmonicIntegralPairing (d : ℕ) (n : ℕ) : HarmonicL2 d n → HarmonicL2 d n → ℝ := by
  classical
  exact (
    fun u v => ∫ x, harmonicRestriction d n (harmonicL2Forget d n u) x * harmonicRestriction d n (harmonicL2Forget d n v) x ∂sigma d
  )

-- lem:harmonic-pairing-integrable: Problem1.harmonic_pairing_integrable
theorem harmonic_pairing_integrable (d : ℕ) (n : ℕ) (hd : 2 ≤ d) (u v : HarmonicL2 d n) : MeasureTheory.Integrable (fun x => harmonicRestriction d n (harmonicL2Forget d n u) x * harmonicRestriction d n (harmonicL2Forget d n v) x) (sigma d) := by
  exact (continuous_product_integrable d hd
    (harmonicRestriction d n (harmonicL2Forget d n u))
    (harmonicRestriction d n (harmonicL2Forget d n v))).2.1

-- lem:harmonic-pairing-symm: Problem1.harmonic_pairing_symm
theorem harmonic_pairing_symm (d : ℕ) (n : ℕ) (hd : 2 ≤ d) (u v : HarmonicL2 d n) : harmonicIntegralPairing d n u v = harmonicIntegralPairing d n v u := by
  have _ := hd
  simp only [harmonicIntegralPairing, mul_comm]

-- lem:harmonic-pairing-add: Problem1.harmonic_pairing_add
theorem harmonic_pairing_add (d : ℕ) (n : ℕ) (hd : 2 ≤ d) (u v w : HarmonicL2 d n) : harmonicIntegralPairing d n (u + v) w = harmonicIntegralPairing d n u w + harmonicIntegralPairing d n v w := by
  simpa only [harmonicIntegralPairing, map_add, ContinuousMap.add_apply, add_mul] using
    (MeasureTheory.integral_add (harmonic_pairing_integrable d n hd u w)
      (harmonic_pairing_integrable d n hd v w))

-- lem:harmonic-pairing-smul: Problem1.harmonic_pairing_smul
theorem harmonic_pairing_smul (d : ℕ) (n : ℕ) (hd : 2 ≤ d) (a : ℝ) (u v : HarmonicL2 d n) : harmonicIntegralPairing d n (a • u) v = a * harmonicIntegralPairing d n u v := by
  have _ := hd
  simpa only [harmonicIntegralPairing, map_smul, ContinuousMap.smul_apply,
    smul_eq_mul, mul_assoc] using
    (MeasureTheory.integral_const_mul a (fun x =>
      harmonicRestriction d n (harmonicL2Forget d n u) x *
      harmonicRestriction d n (harmonicL2Forget d n v) x) (μ := sigma d))

-- lem:harmonic-pairing-nonneg: Problem1.harmonic_pairing_nonneg
theorem harmonic_pairing_nonneg (d : ℕ) (n : ℕ) (hd : 2 ≤ d) (u : HarmonicL2 d n) : 0 ≤ harmonicIntegralPairing d n u u := by
  have _ := hd
  exact MeasureTheory.integral_nonneg (fun x =>
    mul_self_nonneg (harmonicRestriction d n (harmonicL2Forget d n u) x))

-- lem:harmonic-pairing-definite: Problem1.harmonic_pairing_definite
theorem harmonic_pairing_definite (d : ℕ) (n : ℕ) (hd : 2 ≤ d) (u : HarmonicL2 d n) (hu : harmonicIntegralPairing d n u u = 0) : u = 0 := by
  have hf := continuous_square_definite d hd
    (harmonicRestriction d n (harmonicL2Forget d n u))
    (by simpa only [harmonicIntegralPairing, pow_two] using hu)
  exact (harmonicL2Forget d n).injective ((harmonic_restriction_injective d n)
    (by simpa only [map_zero] using hf))

-- lem:harmonic-L2-core-fields: Problem1.harmonic_pairing_add_right
theorem harmonic_pairing_add_right (d : ℕ) (n : ℕ) (hd : 2 ≤ d) (u v w : HarmonicL2 d n) : harmonicIntegralPairing d n u (v + w) = harmonicIntegralPairing d n u v + harmonicIntegralPairing d n u w := by
  exact (harmonic_pairing_symm d n hd u (v + w)).trans
    ((harmonic_pairing_add d n hd v w u).trans
      (congrArg₂ (· + ·) (harmonic_pairing_symm d n hd v u)
        (harmonic_pairing_symm d n hd w u)))

-- lem:harmonic-L2-core-fields: Problem1.harmonic_pairing_smul_right
theorem harmonic_pairing_smul_right (d : ℕ) (n : ℕ) (hd : 2 ≤ d) (a : ℝ) (u v : HarmonicL2 d n) : harmonicIntegralPairing d n u (a • v) = a * harmonicIntegralPairing d n u v := by
  exact (harmonic_pairing_symm d n hd u (a • v)).trans
    ((harmonic_pairing_smul d n hd a v u).trans
      (congrArg (a * ·) (harmonic_pairing_symm d n hd v u)))

-- lem:harmonic-L2-core-fields: Problem1.harmonic_pairing_core_conj
theorem harmonic_pairing_core_conj (d : ℕ) (n : ℕ) (hd : 2 ≤ d) (u v : HarmonicL2 d n) : star (harmonicIntegralPairing d n v u) = harmonicIntegralPairing d n u v := by
  exact harmonic_pairing_symm d n hd v u

-- lem:harmonic-L2-core-fields: Problem1.harmonic_pairing_core_re_nonneg
theorem harmonic_pairing_core_re_nonneg (d : ℕ) (n : ℕ) (hd : 2 ≤ d) (u : HarmonicL2 d n) : 0 ≤ RCLike.re (harmonicIntegralPairing d n u u) := by
  exact harmonic_pairing_nonneg d n hd u

-- lem:harmonic-L2-core-fields: Problem1.harmonic_pairing_core_smul
theorem harmonic_pairing_core_smul (d : ℕ) (n : ℕ) (hd : 2 ≤ d) (u v : HarmonicL2 d n) (a : ℝ) : harmonicIntegralPairing d n (a • u) v = star a * harmonicIntegralPairing d n u v := by
  exact harmonic_pairing_smul d n hd a u v

-- lem:harmonic-L2-core-fields: Problem1.harmonicL2Core
@[implicit_reducible] noncomputable def harmonicL2Core (d : ℕ) (n : ℕ) (hd : 2 ≤ d) : InnerProductSpace.Core ℝ (HarmonicL2 d n) := by
  classical
  exact (
    { inner := harmonicIntegralPairing d n, conj_inner_symm := harmonic_pairing_core_conj d n hd, re_inner_nonneg := harmonic_pairing_core_re_nonneg d n hd, add_left := harmonic_pairing_add d n hd, smul_left := harmonic_pairing_core_smul d n hd, definite := harmonic_pairing_definite d n hd }
  )

-- def:harmonic-L2-instances: Problem1.harmonicL2NormedAddCommGroup
noncomputable instance harmonicL2NormedAddCommGroup (d : ℕ) (n : ℕ) [Fact (2 ≤ d)] : NormedAddCommGroup (HarmonicL2 d n) := by
  classical
  exact (
    letI : InnerProductSpace.Core ℝ (HarmonicL2 d n) := harmonicL2Core d n (Fact.out : 2 ≤ d); InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  )

-- def:harmonic-L2-instances: Problem1.harmonicL2NormedSpace
noncomputable instance harmonicL2NormedSpace (d : ℕ) (n : ℕ) [Fact (2 ≤ d)] : NormedSpace ℝ (HarmonicL2 d n) := by
  classical
  exact (
    letI : InnerProductSpace.Core ℝ (HarmonicL2 d n) := harmonicL2Core d n (Fact.out : 2 ≤ d); InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ)
  )

-- def:harmonic-L2-instances: Problem1.harmonicL2InnerProductSpace
noncomputable instance harmonicL2InnerProductSpace (d : ℕ) (n : ℕ) [Fact (2 ≤ d)] : InnerProductSpace ℝ (HarmonicL2 d n) := by
  classical
  exact (
    InnerProductSpace.ofCore (harmonicL2Core d n (Fact.out : 2 ≤ d)).toCore
  )

-- def:harmonic-L2-instances: Problem1.harmonicL2_inner_eq_pairing
theorem harmonicL2_inner_eq_pairing (d : ℕ) (n : ℕ) [Fact (2 ≤ d)] (u v : HarmonicL2 d n) : inner ℝ u v = harmonicIntegralPairing d n u v := by
  rfl

-- def:harmonic-L2-instances: Problem1.harmonicL2_norm_eq_sqrt_pairing
theorem harmonicL2_norm_eq_sqrt_pairing (d : ℕ) (n : ℕ) [Fact (2 ≤ d)] (u : HarmonicL2 d n) : ‖u‖ = Real.sqrt (harmonicIntegralPairing d n u u) := by
  rfl

-- lem:harmonic-eval-linear: Problem1.harmonicEvalLinear
noncomputable def harmonicEvalLinear (d : ℕ) (n : ℕ) : HarmonicL2 d n →ₗ[ℝ] Harmonic d n := by
  classical
  exact (
    (harmonicRestriction d n).rangeRestrict.comp (harmonicL2Forget d n).toLinearMap
  )

-- lem:harmonic-eval-linear: Problem1.harmonicEvalLinear_surjective
theorem harmonicEvalLinear_surjective (d : ℕ) (n : ℕ) : Function.Surjective (harmonicEvalLinear d n) := by
  exact (LinearMap.surjective_rangeRestrict (harmonicRestriction d n)).comp
    (harmonicL2Forget d n).surjective

-- lem:harmonic-eval-injective: Problem1.harmonicEvalLinear_injective
theorem harmonicEvalLinear_injective (d : ℕ) (n : ℕ) : Function.Injective (harmonicEvalLinear d n) := by
  exact fun u v huv => (harmonicL2Forget d n).injective
    ((harmonic_restriction_injective d n) (congrArg Subtype.val huv))

-- lem:harmonic-eval-bijective: Problem1.harmonicEvalLinear_bijective
theorem harmonicEvalLinear_bijective (d : ℕ) (n : ℕ) : Function.Bijective (harmonicEvalLinear d n) := by
  exact ⟨harmonicEvalLinear_injective d n, harmonicEvalLinear_surjective d n⟩

-- def:harmonic-evaluation-equiv: Problem1.harmonicEvalEquiv
noncomputable def harmonicEvalEquiv (d : ℕ) (n : ℕ) : HarmonicL2 d n ≃ₗ[ℝ] Harmonic d n := by
  classical
  exact (
    LinearEquiv.ofBijective (harmonicEvalLinear d n) (harmonicEvalLinear_bijective d n)
  )

-- lem:harmonic-eval-laws: Problem1.harmonicEvalEquiv_apply
theorem harmonicEvalEquiv_apply (d : ℕ) (n : ℕ) (u : HarmonicL2 d n) (x : Sphere d) : (harmonicEvalEquiv d n u : C(Sphere d, ℝ)) x = polynomialEval d (harmonicL2Forget d n u : Ambient d) x := by
  rfl

-- lem:harmonic-eval-laws: Problem1.harmonicEvalEquiv_symm_apply_apply
theorem harmonicEvalEquiv_symm_apply_apply (d : ℕ) (n : ℕ) (u : HarmonicL2 d n) : (harmonicEvalEquiv d n).symm (harmonicEvalEquiv d n u) = u := by
  exact (harmonicEvalEquiv d n).symm_apply_apply u

-- lem:harmonic-eval-laws: Problem1.harmonicEvalEquiv_apply_symm_apply
theorem harmonicEvalEquiv_apply_symm_apply (d : ℕ) (n : ℕ) (h : Harmonic d n) : harmonicEvalEquiv d n ((harmonicEvalEquiv d n).symm h) = h := by
  exact (harmonicEvalEquiv d n).apply_symm_apply h

-- eq:harmonic-L2-pairing, lem:harmonic-L2-pairing: Problem1.harmonicL2_inner_apply
theorem harmonicL2_inner_apply (d : ℕ) (n : ℕ) [Fact (2 ≤ d)] (u v : HarmonicL2 d n) : inner ℝ u v = ∫ x, (harmonicEvalEquiv d n u : C(Sphere d, ℝ)) x * (harmonicEvalEquiv d n v : C(Sphere d, ℝ)) x ∂sigma d := by
  exact harmonicL2_inner_eq_pairing d n u v

-- lem:harmonic-L2-finrank: Problem1.harmonicL2_finrank
theorem harmonicL2_finrank (d : ℕ) (n : ℕ) : Module.finrank ℝ (HarmonicL2 d n) = Module.finrank ℝ (HAmb d n) ∧ Module.finrank ℝ (HAmb d n) = Module.finrank ℝ (Harmonic d n) ∧ Module.finrank ℝ (HarmonicL2 d n) = Module.finrank ℝ (Harmonic d n) := by
  exact ⟨harmonicL2_finrank_ambient d n, (harmonic_finrank d n).symm,
    (harmonicEvalEquiv d n).finrank_eq⟩

-- lem:harmonic-L2-interface: Problem1.harmonicL2_completeSpace
noncomputable instance harmonicL2_completeSpace (d : ℕ) (n : ℕ) [Fact (2 ≤ d)] : CompleteSpace (HarmonicL2 d n) := by
  exact FiniteDimensional.complete ℝ (HarmonicL2 d n)

-- lem:harmonic-L2-interface: Problem1.harmonicL2_interface
theorem harmonicL2_interface (d : ℕ) (n : ℕ) [Fact (2 ≤ d)] : CompleteSpace (HarmonicL2 d n) ∧ FiniteDimensional ℝ (HarmonicL2 d n) ∧ (∀ u v : HarmonicL2 d n, inner ℝ u v = ∫ x, (harmonicEvalEquiv d n u : C(Sphere d, ℝ)) x * (harmonicEvalEquiv d n v : C(Sphere d, ℝ)) x ∂sigma d) ∧ (Module.finrank ℝ (HarmonicL2 d n) = Module.finrank ℝ (HAmb d n) ∧ Module.finrank ℝ (HAmb d n) = Module.finrank ℝ (Harmonic d n) ∧ Module.finrank ℝ (HarmonicL2 d n) = Module.finrank ℝ (Harmonic d n)) := by
  exact ⟨harmonicL2_completeSpace d n, harmonicL2_finiteDimensional d n,
    harmonicL2_inner_apply d n, harmonicL2_finrank d n⟩

end
end Problem1
