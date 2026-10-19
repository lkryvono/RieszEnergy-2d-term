import Riesz.PastProjects.Problem1.EnergyLower
import Riesz.Energy

/-!
# Sphere results reused from Problem 1

The source modules under `Riesz/PastProjects/Problem1` retain the original
statements and proofs. Their provenance and source hashes are recorded in
`provenance.json`. This module identifies their sphere, kernel, and continuous
energy with the exact definitions in `Showcase.lean`.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped Classical

namespace Riesz.Geometry

/-- The two sphere subtypes have the same ambient vectors. -/
def problem1SphereEquiv (d : ℕ) : Sphere d ≃ Problem1.Sphere d :=
  Equiv.subtypeEquivRight (fun x => by
    simp [Problem1.Sphere, Problem1.UnitSphereN, Problem1.EuclideanN])

theorem problem1SphereEquiv_dist (d : ℕ) (x y : Sphere d) :
    dist (problem1SphereEquiv d x) (problem1SphereEquiv d y) = chord d x y := by
  exact dist_eq_norm x.val y.val

def problem1SphereIsometryEquiv (d : ℕ) : Sphere d ≃ᵢ Problem1.Sphere d where
  toEquiv := problem1SphereEquiv d
  isometry_toFun := Isometry.of_dist_eq (fun x y =>
    (problem1SphereEquiv_dist d x y).trans (dist_eq_norm x.val y.val).symm)

/-- The invariant probability law constructed from orthogonal Haar measure.
Its geometric identification with normalized chart area is a separate task. -/
def sphericalMeasure (d : ℕ) : Measure (Sphere d) :=
  (Problem1.sigma d).map (problem1SphereIsometryEquiv d).symm

instance sphericalMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (sphericalMeasure d) :=
  (Problem1.sigma d).isProbabilityMeasure_map
    (problem1SphereIsometryEquiv d).symm.continuous.measurable.aemeasurable

theorem sphericalMeasure_singleton (d : ℕ) (hd : 2 ≤ d) (x : Sphere d) :
    sphericalMeasure d {x} = 0 := by
  rw [sphericalMeasure, Measure.map_apply
    (problem1SphereIsometryEquiv d).symm.continuous.measurable (measurableSet_singleton x)]
  rw [show (⇑(problem1SphereIsometryEquiv d).symm) ⁻¹' {x} =
    {problem1SphereIsometryEquiv d x} from
    Set.ext (fun y => (problem1SphereIsometryEquiv d).symm_apply_eq (x := x) (y := y))]
  exact Problem1.sphere_atomless d hd _

theorem sphericalMeasure_nullSingletonClass (d : ℕ) (hd : 2 ≤ d) :
    NullSingletonClass (sphericalMeasure d) := ⟨sphericalMeasure_singleton d hd⟩

theorem problem1Kernel_eq (d : ℕ) (s : ℝ) (hs : s ≠ 0) (x y : Sphere d) :
    Problem1.kernel d s (problem1SphereEquiv d x) (problem1SphereEquiv d y) =
      K_s s (chord d x y) := by
  by_cases hxy : x = y
  · simp [hxy, Problem1.kernel_diag, K_s, chord,
      Real.zero_rpow (neg_ne_zero.mpr hs)]
  · simp [Problem1.kernel, (problem1SphereEquiv d).injective.ne hxy, hs,
      problem1SphereEquiv_dist, K_s, div_eq_mul_inv, mul_comm]

theorem problem1FiniteEnergy_eq (d N : ℕ) (s : ℝ) (hs : s ≠ 0)
    (x : SphereConfiguration d N) :
    Problem1.finiteEnergy s (fun i => problem1SphereEquiv d (x.val i)) =
      Riesz.Energy.kernelEnergy d s N x := by
  simp only [Problem1.finiteEnergy, Riesz.Energy.kernelEnergy,
    problem1Kernel_eq d s hs]

theorem problem1ContinuousEnergy_eq (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hsd : s < (d : ℝ)) (hs : s ≠ 0) :
    Problem1.continuousEnergy d s = V_K d s := by
  rw [Problem1.continuous_energy_power_formula d hd s hsd hs,
    (Problem1.coordinate_normalizer_gamma d hd).1, ProbabilityTheory.beta, V_K, V_s]
  have hgd : Real.Gamma ((d : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos
      (div_pos (Nat.cast_pos.mpr (by omega)) (by norm_num))).ne'
  rw [show (d : ℝ) - 1 - s = (d : ℝ) - s - 1 by ring,
    show ((d : ℝ) - s) / 2 + (d : ℝ) / 2 = (d : ℝ) - s / 2 by ring]
  field_simp [hgd]
  simp only [Real.rpow_eq_pow, mul_comm]

theorem sphericalMeasure_kernel_integrable (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hsd : s < (d : ℝ)) (hs : s ≠ 0) (x : Sphere d) :
    Integrable (fun y => K_s s (chord d x y)) (sphericalMeasure d) := by
  apply (problem1SphereIsometryEquiv d).symm.toHomeomorph.measurableEmbedding.integrable_map_iff.mpr
  change Integrable (fun y => K_s s (chord d x ((problem1SphereEquiv d).symm y)))
    (Problem1.sigma d)
  simp_rw [← problem1Kernel_eq d s hs, Equiv.apply_symm_apply]
  exact Problem1.kernel_section_integrable d hd s hsd (problem1SphereEquiv d x)

theorem sphericalMeasure_kernel_integral (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hsd : s < (d : ℝ)) (hs : s ≠ 0) (x : Sphere d) :
    (∫ y, K_s s (chord d x y) ∂sphericalMeasure d) = V_K d s := by
  change (∫ y, K_s s (chord d x y) ∂Measure.map
    (problem1SphereIsometryEquiv d).symm.toHomeomorph (Problem1.sigma d)) = V_K d s
  rw [(problem1SphereIsometryEquiv d).symm.toHomeomorph.measurableEmbedding.integral_map]
  change (∫ y, K_s s (chord d x ((problem1SphereEquiv d).symm y))
    ∂Problem1.sigma d) = V_K d s
  simp_rw [← problem1Kernel_eq d s hs, Equiv.apply_symm_apply]
  rw [Problem1.continuous_energy_center d hd s hsd, problem1ContinuousEnergy_eq d hd s hsd hs]

theorem sphericalMeasure_radial_integral (d : ℕ) (F : ℝ → ℝ) (x : Sphere d) :
    (∫ y, F (chord d x y) ∂sphericalMeasure d) =
      ∫ y, F (dist (problem1SphereEquiv d x) y) ∂Problem1.sigma d := by
  change (∫ y, F (chord d x y) ∂Measure.map
    (problem1SphereIsometryEquiv d).symm.toHomeomorph (Problem1.sigma d)) = _
  rw [(problem1SphereIsometryEquiv d).symm.toHomeomorph.measurableEmbedding.integral_map]
  change (∫ y, F (chord d x ((problem1SphereEquiv d).symm y)) ∂Problem1.sigma d) = _
  simp_rw [← problem1SphereEquiv_dist, Equiv.apply_symm_apply]

theorem sphericalMeasure_gaussian_integral (d : ℕ) (hd : 2 ≤ d) (t : ℝ)
    (x : Sphere d) :
    (∫ y, Real.exp (-t * (chord d x y) ^ 2) ∂sphericalMeasure d) =
      Problem1.gaussianAverage d t := by
  rw [sphericalMeasure_radial_integral d (fun r => Real.exp (-t * r ^ 2)) x]
  exact (Problem1.gaussian_center d hd t (problem1SphereEquiv d x)).2

theorem problem1GaussianAverageConstant_eq (d : ℕ) (hd : 2 ≤ d) :
    Problem1.gaussianAverageConstant d = Real.pi ^ ((d : ℝ) / 2) / omega d := by
  rw [Problem1.gaussianAverageConstant, (Problem1.coordinate_normalizer_gamma d hd).1,
    omega]
  have hpi : Real.pi ^ (((d : ℝ) + 1) / 2) =
      Real.pi ^ ((d : ℝ) / 2) * Real.sqrt Real.pi := by
    rw [show ((d : ℝ) + 1) / 2 = (d : ℝ) / 2 + 1 / 2 by ring,
      Real.rpow_add Real.pi_pos, ← Real.sqrt_eq_rpow]
  have hgd : Real.Gamma ((d : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos
      (div_pos (Nat.cast_pos.mpr (by omega)) (by norm_num))).ne'
  field_simp [hpi, hgd]
  simpa only [mul_comm] using hpi

theorem sphericalMeasure_gaussian_bound (d : ℕ) (hd : 2 ≤ d) (t : ℝ)
    (ht : 0 < t) (x : Sphere d) :
    (∫ y, Real.exp (-t * (chord d x y) ^ 2) ∂sphericalMeasure d) ≤
      Real.pi ^ ((d : ℝ) / 2) / omega d * t ^ (-(d : ℝ) / 2) := by
  simpa only [sphericalMeasure_gaussian_integral d hd t x,
    ← problem1GaussianAverageConstant_eq d hd, Real.rpow_eq_pow] using
    ((Problem1.gaussian_average d hd).2.1 t ht).2

theorem positive_sphere_kernelEnergy_lower (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (N : ℕ) (x : SphereConfiguration d N) :
    V_K d s * (N : ℝ) ^ 2 - Problem1.part5_energy_constants_positive d s *
      (N : ℝ) ^ (1 + s / (d : ℝ)) ≤ Riesz.Energy.kernelEnergy d s N x := by
  simpa only [problem1ContinuousEnergy_eq d hd s hsd hs.ne',
    problem1FiniteEnergy_eq d N s hs.ne', Real.rpow_eq_pow] using
    Problem1.part5_positive_energy_config d hd s hs hsd N
      (fun i => problem1SphereEquiv d (x.val i))
      ((problem1SphereEquiv d).injective.comp x.property)

theorem sphereConfiguration_nonempty (d : ℕ) (hd : 2 ≤ d) (N : ℕ) :
    Nonempty (SphereConfiguration d N) := by
  obtain ⟨x, hx⟩ := Problem1.exists_injective_configuration d hd N
  exact ⟨⟨fun i => (problem1SphereEquiv d).symm (x i),
    (problem1SphereEquiv d).symm.injective.comp hx⟩⟩

theorem positive_sphere_optimalEnergy_lower (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (N : ℕ) :
    V_K d s * (N : ℝ) ^ 2 - Problem1.part5_energy_constants_positive d s *
      (N : ℝ) ^ (1 + s / (d : ℝ)) ≤ E_K d s N := by
  refine le_csInf ?_ ?_
  · exact (sphereConfiguration_nonempty d hd N).elim
      (fun x => ⟨Riesz.Energy.kernelEnergy d s N x, x, rfl⟩)
  · rintro _ ⟨x, rfl⟩
    exact positive_sphere_kernelEnergy_lower d hd s hs hsd N x

/-- The universal lower bound in the paper, for the exact showcase infimum. -/
theorem universal_positive_sphere_lower_bound (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      -K * (N : ℝ) ^ (1 + s / (d : ℝ)) ≤
        E_K d s N - V_K d s * (N : ℝ) ^ 2 := by
  refine ⟨Problem1.part5_energy_constants_positive d s,
    (Problem1.part5_energy_constant_signs d hd).1 s hs hsd, ?_⟩
  intro N
  linarith [positive_sphere_optimalEnergy_lower d hd s hs hsd N]

theorem negative_sphere_kernelEnergy_lower (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : -2 < s) (hs0 : s < 0) (hsd : s < (d : ℝ)) (N : ℕ)
    (x : SphereConfiguration d N) :
    V_K d s * (N : ℝ) ^ 2 + Problem1.part5_energy_constants_negative d s *
      (N : ℝ) ^ (1 + s / (d : ℝ)) ≤ Riesz.Energy.kernelEnergy d s N x := by
  simpa only [problem1ContinuousEnergy_eq d hd s hsd hs0.ne,
    problem1FiniteEnergy_eq d N s hs0.ne, Real.rpow_eq_pow] using
    Problem1.part5_negative_energy_config d hd s hs hs0 N
      (fun i => problem1SphereEquiv d (x.val i))
      ((problem1SphereEquiv d).injective.comp x.property)

theorem negative_sphere_optimalEnergy_lower (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : -2 < s) (hs0 : s < 0) (hsd : s < (d : ℝ)) (N : ℕ) :
    V_K d s * (N : ℝ) ^ 2 + Problem1.part5_energy_constants_negative d s *
      (N : ℝ) ^ (1 + s / (d : ℝ)) ≤ E_K d s N := by
  exact le_csInf ((sphereConfiguration_nonempty d hd N).elim
    (fun x => ⟨Riesz.Energy.kernelEnergy d s N x, x, rfl⟩))
    (fun _ ⟨x, hx⟩ => hx ▸ negative_sphere_kernelEnergy_lower d hd s hs hs0 hsd N x)

theorem universal_negative_sphere_lower_bound (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : -2 < s) (hs0 : s < 0) (hsd : s < (d : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      K * (N : ℝ) ^ (1 + s / (d : ℝ)) ≤
        E_K d s N - V_K d s * (N : ℝ) ^ 2 := by
  refine ⟨Problem1.part5_energy_constants_negative d s,
    (Problem1.part5_energy_constant_signs d hd).2.1 s hs hs0, fun N => ?_⟩
  linarith [negative_sphere_optimalEnergy_lower d hd s hs hs0 hsd N]

/-- The rescaled coordinate integrand used in the sharp Gaussian limit. -/
def sphericalGaussianScaledIntegrand (d : ℕ) (t z : ℝ) : ℝ :=
  Real.exp (-z) * z ^ ((d : ℝ) / 2 - 1) *
    (1 - z / (4 * t)) ^ ((d : ℝ) / 2 - 1)

theorem gaussian_coordinate_scaled (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (ht : 0 < t) :
    t ^ ((d : ℝ) / 2) * Problem1.gaussianAverage d t =
      Problem1.coordinateNormConst d / 2 *
        ∫ z in Set.Icc (0 : ℝ) (4 * t), sphericalGaussianScaledIntegrand d t z := by
  rw [(Problem1.gaussian_coordinate d hd t ht).2]
  have hpoint (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 2) :
      sphericalGaussianScaledIntegrand d t (2 * t * v) =
        t ^ ((d : ℝ) / 2 - 1) *
          (Real.exp (-2 * t * v) * (v * (2 - v)) ^ ((d : ℝ) / 2 - 1)) := by
    simp only [sphericalGaussianScaledIntegrand, neg_mul]
    have hbase : 1 - 2 * t * v / (4 * t) = (2 - v) / 2 := by
      field_simp [ht.ne']
      ring
    rw [hbase, mul_assoc, ← Real.mul_rpow
      (mul_nonneg (mul_pos (by norm_num : (0 : ℝ) < 2) ht).le hv.1)
      (div_nonneg (sub_nonneg.mpr hv.2) (by norm_num : (0 : ℝ) ≤ 2))]
    rw [show 2 * t * v * ((2 - v) / 2) = t * (v * (2 - v)) by ring,
      Real.mul_rpow ht.le (mul_nonneg hv.1 (sub_nonneg.mpr hv.2))]
    ring
  have hsub : (∫ v in Set.Icc (0 : ℝ) 2,
      sphericalGaussianScaledIntegrand d t (2 * t * v)) =
      (2 * t)⁻¹ * ∫ z in Set.Icc (0 : ℝ) (4 * t),
        sphericalGaussianScaledIntegrand d t z := by
    simpa only [mul_zero, show 2 * t * 2 = 4 * t by ring,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 4 * t),
      integral_Icc_eq_integral_Ioc, smul_eq_mul] using
        intervalIntegral.integral_comp_mul_left (a := 0) (b := 2) (c := 2 * t)
          (sphericalGaussianScaledIntegrand d t) (mul_ne_zero (by norm_num) ht.ne')
  rw [setIntegral_congr_fun measurableSet_Icc hpoint, integral_const_mul] at hsub
  have hpow : t ^ ((d : ℝ) / 2) = t * t ^ ((d : ℝ) / 2 - 1) := by
    simpa only [show (1 : ℝ) + ((d : ℝ) / 2 - 1) = (d : ℝ) / 2 by ring,
      Real.rpow_one] using Real.rpow_add ht 1 ((d : ℝ) / 2 - 1)
  have hsub' := congrArg (fun z : ℝ => (2 * t) * z) hsub
  simp only [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ht.ne'),
    one_mul] at hsub'
  simp only [Real.rpow_eq_pow, hpow, ← hsub']
  ring

/-- Extension by zero of the rescaled Gaussian integrand. -/
def sphericalGaussianTruncatedIntegrand (d : ℕ) (t z : ℝ) : ℝ :=
  (Set.Iic (4 * t)).indicator (sphericalGaussianScaledIntegrand d t) z

theorem tendsto_integral_sphericalGaussianTruncatedIntegrand (d : ℕ) (hd : 2 ≤ d) :
    Filter.Tendsto
      (fun t : ℝ => ∫ z in Set.Ioi (0 : ℝ), sphericalGaussianTruncatedIntegrand d t z)
      Filter.atTop (nhds (Real.Gamma ((d : ℝ) / 2))) := by
  have hp : 0 ≤ (d : ℝ) / 2 - 1 := by
    linarith [show (2 : ℝ) ≤ d by exact_mod_cast hd]
  rw [Real.Gamma_eq_integral
    (div_pos (Nat.cast_pos.mpr (by omega : 0 < d)) (by norm_num : (0 : ℝ) < 2))]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z : ℝ => Real.exp (-z) * z ^ ((d : ℝ) / 2 - 1))
  case h_lim =>
    refine Filter.Eventually.of_forall (fun z => ?_)
    have hdiv : Filter.Tendsto (fun t : ℝ => z / (4 * t)) Filter.atTop (nhds 0) :=
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
        Filter.tendsto_id).const_div_atTop z
    have hpow : Filter.Tendsto (fun t : ℝ => (1 - z / (4 * t)) ^ ((d : ℝ) / 2 - 1))
        Filter.atTop (nhds 1) := by
      simpa only [sub_zero, Real.one_rpow] using
        (tendsto_const_nhds.sub hdiv).rpow_const
          (p := (d : ℝ) / 2 - 1) (Or.inl (by norm_num : (1 : ℝ) - 0 ≠ 0))
    have hscaled : Filter.Tendsto (fun t : ℝ => sphericalGaussianScaledIntegrand d t z)
        Filter.atTop (nhds (Real.exp (-z) * z ^ ((d : ℝ) / 2 - 1))) := by
      simpa only [sphericalGaussianScaledIntegrand, mul_one] using
        hpow.const_mul (Real.exp (-z) * z ^ ((d : ℝ) / 2 - 1))
    apply hscaled.congr'
    filter_upwards [Filter.eventually_ge_atTop (z / 4)] with t ht
    simp only [sphericalGaussianTruncatedIntegrand,
      Set.indicator_of_mem (show z ∈ Set.Iic (4 * t) from by
        simpa only [Set.mem_Iic, mul_comm] using
          (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp ht)]
  case bound_integrable =>
    exact Real.GammaIntegral_convergent
      (div_pos (Nat.cast_pos.mpr (by omega : 0 < d)) (by norm_num : (0 : ℝ) < 2))
  case hF_meas =>
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hcont : Continuous (sphericalGaussianScaledIntegrand d t) :=
      (continuous_neg.rexp.mul (Real.continuous_rpow_const hp)).mul
        ((Real.continuous_rpow_const hp).comp
          (continuous_const.sub (continuous_id.div_const (4 * t))))
    exact hcont.aestronglyMeasurable.indicator measurableSet_Iic
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  refine (ae_restrict_mem measurableSet_Ioi).mono (fun z hz => ?_)
  by_cases hzt : z ≤ 4 * t
  · have hbase0 : 0 ≤ 1 - z / (4 * t) :=
      sub_nonneg.mpr ((div_le_one (mul_pos (by norm_num : (0 : ℝ) < 4) ht)).mpr hzt)
    have hbase1 : 1 - z / (4 * t) ≤ 1 :=
      sub_le_self 1 (div_nonneg (le_of_lt hz) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ht.le))
    have hG0 : 0 ≤ Real.exp (-z) * z ^ ((d : ℝ) / 2 - 1) :=
      mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (le_of_lt hz) _)
    rw [sphericalGaussianTruncatedIntegrand,
      Set.indicator_of_mem (show z ∈ Set.Iic (4 * t) from hzt),
      sphericalGaussianScaledIntegrand, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hG0 (Real.rpow_nonneg hbase0 _))]
    exact mul_le_of_le_one_right hG0 (Real.rpow_le_one hbase0 hbase1 hp)
  · simpa only [sphericalGaussianTruncatedIntegrand,
      Set.indicator_of_notMem (show z ∉ Set.Iic (4 * t) from hzt), norm_zero] using
        mul_nonneg (Real.exp_nonneg (-z)) (Real.rpow_nonneg (le_of_lt hz) ((d : ℝ) / 2 - 1))

theorem integral_sphericalGaussianTruncatedIntegrand (d : ℕ) (t : ℝ) :
    (∫ z in Set.Ioi (0 : ℝ), sphericalGaussianTruncatedIntegrand d t z) =
      ∫ z in Set.Icc (0 : ℝ) (4 * t), sphericalGaussianScaledIntegrand d t z := by
  simp only [sphericalGaussianTruncatedIntegrand, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Set.Iic_inter_Ioi,
    integral_Icc_eq_integral_Ioc]

/-- The sharp Gaussian coefficient for the exact normalization of the showcase. -/
theorem gaussianAverage_asymptotic (d : ℕ) (hd : 2 ≤ d) :
    Filter.Tendsto (fun t : ℝ => t ^ ((d : ℝ) / 2) * Problem1.gaussianAverage d t)
      Filter.atTop (nhds (Real.pi ^ ((d : ℝ) / 2) / omega d)) := by
  rw [← problem1GaussianAverageConstant_eq d hd]
  have hlim : Filter.Tendsto (fun t : ℝ => Problem1.coordinateNormConst d / 2 *
      ∫ z in Set.Ioi (0 : ℝ), sphericalGaussianTruncatedIntegrand d t z)
      Filter.atTop (nhds (Problem1.gaussianAverageConstant d)) := by
    simpa only [Problem1.gaussianAverageConstant, div_mul_eq_mul_div] using
      (tendsto_integral_sphericalGaussianTruncatedIntegrand d hd).const_mul
        (Problem1.coordinateNormConst d / 2)
  apply hlim.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  rw [integral_sphericalGaussianTruncatedIntegrand, gaussian_coordinate_scaled d hd t ht]

theorem sphericalMeasure_gaussian_asymptotic (d : ℕ) (hd : 2 ≤ d) (x : Sphere d) :
    Filter.Tendsto
      (fun t : ℝ => t ^ ((d : ℝ) / 2) *
        ∫ y, Real.exp (-t * (chord d x y) ^ 2) ∂sphericalMeasure d)
      Filter.atTop (nhds (Real.pi ^ ((d : ℝ) / 2) / omega d)) := by
  simpa only [sphericalMeasure_gaussian_integral d hd] using gaussianAverage_asymptotic d hd

theorem sphericalArea_pos (d : ℕ) : 0 < omega d := by
  unfold omega
  exact div_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity))

theorem gaussianAverage_radius_asymptotic (d : ℕ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 < u) :
    Filter.Tendsto (fun R : ℝ => omega d * R ^ d * Problem1.gaussianAverage d (u * R ^ 2))
      Filter.atTop (nhds (B d u)) := by
  have harg : Filter.Tendsto (fun R : ℝ => u * R ^ 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hu (Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hlim := ((gaussianAverage_asymptotic d hd).comp harg).const_mul
    (omega d / u ^ ((d : ℝ) / 2))
  have hconstant : omega d / u ^ ((d : ℝ) / 2) *
      (Real.pi ^ ((d : ℝ) / 2) / omega d) = B d u := by
    rw [B, Real.div_rpow Real.pi_pos.le hu.le]
    field_simp [(sphericalArea_pos d).ne']
  rw [hconstant] at hlim
  apply hlim.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
  simp only [Function.comp_apply, Real.mul_rpow hu.le (sq_nonneg R)]
  have hpowR : (R ^ (2 : ℕ)) ^ ((d : ℝ) / 2) = R ^ d := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le, Nat.cast_ofNat,
      show (2 : ℝ) * ((d : ℝ) / 2) = (d : ℝ) by ring, Real.rpow_natCast]
  rw [hpowR]
  field_simp [(Real.rpow_pos_of_pos hu ((d : ℝ) / 2)).ne']

/-- The radius of the enlarged sphere whose surface area is `N`. -/
def sphericalRadius (d N : ℕ) : ℝ := ((N : ℝ) / omega d) ^ (1 / (d : ℝ))

theorem sphericalRadius_pos (d N : ℕ) (hN : 0 < N) : 0 < sphericalRadius d N := by
  exact Real.rpow_pos_of_pos (div_pos (Nat.cast_pos.mpr hN) (sphericalArea_pos d)) _

theorem sphericalRadius_pow_dimension (d N : ℕ) (hd : 0 < d) :
    (sphericalRadius d N) ^ d = (N : ℝ) / omega d := by
  rw [sphericalRadius, ← Real.rpow_natCast, ← Real.rpow_mul
    (div_nonneg (Nat.cast_nonneg N) (sphericalArea_pos d).le)]
  rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr hd.ne'), Real.rpow_one]

theorem sphericalRadius_tendsto_atTop (d : ℕ) (hd : 0 < d) :
    Filter.Tendsto (sphericalRadius d) Filter.atTop Filter.atTop := by
  exact (tendsto_rpow_atTop (div_pos zero_lt_one (Nat.cast_pos.mpr hd))).comp
    ((tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop).atTop_div_const
        (sphericalArea_pos d))

/-- `B_N(u)` in the paper's enlarged-sphere normalization. -/
def sphericalGaussianBackground (d N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) * Problem1.gaussianAverage d (u * (sphericalRadius d N) ^ 2)

theorem tendsto_sphericalGaussianBackground (d : ℕ) (hd : 2 ≤ d) (u : ℝ) (hu : 0 < u) :
    Filter.Tendsto (fun N : ℕ => sphericalGaussianBackground d N u)
      Filter.atTop (nhds (B d u)) := by
  have hlim := (gaussianAverage_radius_asymptotic d hd u hu).comp
    (sphericalRadius_tendsto_atTop d (by omega : 0 < d))
  apply hlim.congr'
  refine Filter.Eventually.of_forall (fun N => ?_)
  simp only [Function.comp_apply, sphericalGaussianBackground,
    sphericalRadius_pow_dimension d N (by omega : 0 < d)]
  field_simp [(sphericalArea_pos d).ne']

theorem sphericalGaussianBackground_le (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (u : ℝ) (hu : 0 < u) : sphericalGaussianBackground d N u ≤ B d u := by
  have ht : 0 < u * (sphericalRadius d N) ^ 2 :=
    mul_pos hu (sq_pos_of_pos (sphericalRadius_pos d N hN))
  have hupper : Problem1.gaussianAverage d (u * (sphericalRadius d N) ^ 2) ≤
      (Real.pi ^ ((d : ℝ) / 2) / omega d) *
        (u * (sphericalRadius d N) ^ 2) ^ (-((d : ℝ) / 2)) := by
    simpa only [problem1GaussianAverageConstant_eq d hd, Real.rpow_eq_pow,
      show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring] using
        ((Problem1.gaussian_average d hd).2.1 _ ht).2
  refine (mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg N)).trans_eq ?_
  rw [Real.rpow_neg ht.le, Real.mul_rpow hu.le (sq_nonneg _),
    ← Real.rpow_natCast (sphericalRadius d N) 2,
    ← Real.rpow_mul (sphericalRadius_pos d N hN).le, Nat.cast_ofNat,
    show (2 : ℝ) * ((d : ℝ) / 2) = (d : ℝ) by ring, Real.rpow_natCast,
    sphericalRadius_pow_dimension d N (by omega : 0 < d), B,
    Real.div_rpow Real.pi_pos.le hu.le]
  field_simp [(sphericalArea_pos d).ne', (Nat.cast_pos.mpr hN : (0 : ℝ) < N).ne']

/-- The ordered distinct-index Gaussian profile of an enlarged-sphere tuple.
The tuple may have repeated sites; distinct indices are retained. -/
def sphericalGaussianPairProfile (d N : ℕ) (x : Fin N → Sphere d) (u : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
    if i = j then 0 else Real.exp (-(u * (sphericalRadius d N) ^ 2) * (chord d (x i) (x j)) ^ 2)

def sphericalGaussianRemainder (d N : ℕ) (x : Fin N → Sphere d) (u : ℝ) : ℝ :=
  sphericalGaussianPairProfile d N x u - max (sphericalGaussianBackground d N u - 1) 0

theorem sphericalGaussianPairProfile_nonneg (d N : ℕ) (x : Fin N → Sphere d) (u : ℝ) :
    0 ≤ sphericalGaussianPairProfile d N x u := by
  unfold sphericalGaussianPairProfile
  positivity

theorem sphericalGaussianPairProfile_ge_background (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (x : Fin N → Sphere d) (u : ℝ) (hu : 0 ≤ u) :
    sphericalGaussianBackground d N u - 1 ≤ sphericalGaussianPairProfile d N x u := by
  have hbase := (Problem1.part5_gaussian_discrepancy_lower d hd N
    (fun i => problem1SphereEquiv d (x i)) (u * (sphericalRadius d N) ^ 2)
    (mul_nonneg hu (sq_nonneg _))).2
  simp only [problem1SphereEquiv_dist] at hbase
  rw [sphericalGaussianBackground, sphericalGaussianPairProfile,
    ← div_eq_inv_mul, le_div_iff₀ (Nat.cast_pos.mpr hN)]
  nlinarith only [hbase]

theorem sphericalGaussianRemainder_nonneg (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (x : Fin N → Sphere d) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ sphericalGaussianRemainder d N x u := by
  exact sub_nonneg.mpr (max_le
    (sphericalGaussianPairProfile_ge_background d N hd hN x u hu)
    (sphericalGaussianPairProfile_nonneg d N x u))

/-- The three pointwise Gaussian assertions in the spherical remainder lemma.
The energy representation and convergence of its scalar reference term are separate. -/
theorem sphericalGaussian_remainder_inputs (d : ℕ) (hd : 2 ≤ d) :
    (∀ (N : ℕ), 0 < N → ∀ (x : Fin N → Sphere d) (u : ℝ), 0 ≤ u →
      0 ≤ sphericalGaussianRemainder d N x u) ∧
    (∀ (N : ℕ), 0 < N → ∀ (u : ℝ), 0 < u → sphericalGaussianBackground d N u ≤ B d u) ∧
    (∀ (u : ℝ), 0 < u → Filter.Tendsto (fun N : ℕ => sphericalGaussianBackground d N u)
      Filter.atTop (nhds (B d u))) := by
  exact ⟨fun N hN x u hu => sphericalGaussianRemainder_nonneg d N hd hN x u hu,
    fun N hN u hu => sphericalGaussianBackground_le d N hd hN u hu,
    fun u hu => tendsto_sphericalGaussianBackground d hd u hu⟩

end Riesz.Geometry
