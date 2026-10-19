import Riesz.Negative.IndependentCells
import Riesz.Analysis.DiscrepancyDifference
import Riesz.Geometry.SphereFromProblem1

/-!
Exact signed-energy comparison for actual physical spherical tuples.
The original signed discrepancy equals the centered ordered spherical kernel
energy after radius scaling. Every finite integral is justified explicitly.
-/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Geometry
open scoped ENNReal Classical

namespace Riesz.Negative

/-- Physical area on the radius-R sphere, with its actual geometric density. -/
def negativeSphericalBackground (d : ℕ) (R : ℝ) : FiniteMeasure (Rd (d+1)) :=
  ⟨(ENNReal.ofReal (R^d * omega d) • sphericalMeasure d).map
      (fun y : Sphere d => R • y.val), by
    letI : IsFiniteMeasure (ENNReal.ofReal (R^d * omega d) • sphericalMeasure d) :=
      (sphericalMeasure d).smul_finite ENNReal.ofReal_ne_top
    exact Measure.isFiniteMeasure_map _ _⟩

def negativeSphericalTupleDiscrepancy (d N : ℕ) (R : ℝ)
    (x : Fin N → Rd (d+1)) : SignedMeasure (Rd (d+1)) :=
  letI := tupleCounting_isFiniteMeasure (d+1) N x
  (tupleCounting (d+1) N x).toSignedMeasure -
    (negativeSphericalBackground d R : Measure (Rd (d+1))).toSignedMeasure

private theorem negativeSpherical_kernel_homogeneous (d : ℕ)
    (q R : ℝ) (hR : 0 < R) (x y : Sphere d) :
    K_s (-q) ‖R • x.val - R • y.val‖ = R^q * K_s (-q) (chord d x y) := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  simp only [K_s, neg_neg, chord, Real.mul_rpow hR.le (norm_nonneg _),
    mul_div_assoc]

private theorem negativeSphericalBackground_form (d N : ℕ) (R : ℝ)
    (hRN : R^d * omega d = (N : ℝ)) :
    (negativeSphericalBackground d R : Measure (Rd (d+1))) =
      (ENNReal.ofReal (N : ℝ) • sphericalMeasure d).map
        (fun y : Sphere d => R • y.val) := by
  simp only [negativeSphericalBackground, hRN]
  rfl

theorem negativeSphericalBackground_mass (d N : ℕ) (R : ℝ)
    (hRN : R^d * omega d = (N : ℝ)) :
    (negativeSphericalBackground d R : Measure (Rd (d+1))) Set.univ = N := by
  rw [negativeSphericalBackground_form d N R hRN,
    Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp

private theorem negativeSpherical_section (d N : ℕ) (hd : 2 ≤ d)
    (q R : ℝ) (hq : 0 < q) (hR : 0 < R)
    (hRN : R^d * omega d = (N : ℝ)) (x : Sphere d) :
    (∫ z, K_s (-q) ‖R • x.val - z‖
      ∂(negativeSphericalBackground d R : Measure (Rd (d+1)))) =
        (N : ℝ) * (R^q * V_K d (-q)) := by
  rw [negativeSphericalBackground_form d N R hRN,
    integral_map_of_stronglyMeasurable (by fun_prop)]
  · rw [integral_smul_measure]
    simp_rw [negativeSpherical_kernel_homogeneous d q R hR x]
    rw [integral_const_mul, sphericalMeasure_kernel_integral d hd (-q)
      (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) (neg_ne_zero.mpr hq.ne')]
    simp only [ENNReal.toReal_ofReal (Nat.cast_nonneg N), smul_eq_mul]
  · have hm : Measurable (fun z : Rd (d+1) => ‖R • x.val-z‖^q / (-q)) :=
      ((measurable_const.sub measurable_id).norm.pow_const q).div_const (-q)
    simpa only [K_s, neg_neg] using hm.stronglyMeasurable

private theorem negativeSpherical_pair_integrable (d : ℕ) (q R : ℝ)
    (hq : 0 < q) (μ ν : Measure (Rd (d+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ {z | ‖z‖ = R}ᶜ = 0) (hν : ν {z | ‖z‖ = R}ᶜ = 0) :
    Integrable (fun p : Rd (d+1) × Rd (d+1) => K_s (-q) ‖p.1-p.2‖) (μ.prod ν) := by
  simpa only [K_s, neg_neg] using
    (Riesz.Analysis.integrable_rpow_distance q (2*R) hq.le μ ν
    (Riesz.Analysis.ae_distance_le_of_concentrated μ ν {z | ‖z‖ = R} (2*R)
      hμ hν (fun x hx y hy => by
        have h := norm_sub_le x y
        change ‖x‖ = R at hx
        change ‖y‖ = R at hy
        simpa only [hx, hy, two_mul] using h))).div_const (-q)

/-- Exact physical signed Dq for a genuinely distinct spherical tuple.
All three positive-measure kernel integrals are proved integrable before the
signed quadratic form is expanded. No Gaussian or asymptotic identity is used. -/
theorem negativeSphericalTuple_energy_eq (d N : ℕ) (hd : 2 ≤ d)
    (q R : ℝ) (hq : 0 < q) (hq2 : q < 2) (hR : 0 < R)
    (hRN : R^d * omega d = (N : ℝ)) (x : SphereConfiguration d N) :
    Riesz.Analysis.signedDiscrepancyEnergy q
      (negativeSphericalTupleDiscrepancy d N R (fun i => R • (x.val i).val)) =
        R^q * (Riesz.Energy.kernelEnergy d (-q) N x - V_K d (-q) * (N : ℝ)^2) := by
  let u : Fin N → Rd (d+1) := fun i => R • (x.val i).val
  let μ := tupleCounting (d+1) N u
  let ν : Measure (Rd (d+1)) := negativeSphericalBackground d R
  let S : Set (Rd (d+1)) := {z | ‖z‖ = R}
  letI : IsFiniteMeasure μ := tupleCounting_isFiniteMeasure (d+1) N u
  have hS : MeasurableSet S := measurableSet_eq_fun continuous_norm.measurable measurable_const
  have hu (i : Fin N) : u i ∈ S := by
    simp only [u, S, Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR, (x.val i).property, mul_one]
  have hμ : μ Sᶜ = 0 := (tupleCounting_compl_eq_zero_iff (d+1) N u S hS).mpr hu
  have hν : ν Sᶜ = 0 := by
    change (negativeSphericalBackground d R : Measure (Rd (d+1))) Sᶜ = 0
    rw [negativeSphericalBackground_form d N R hRN,
      Measure.map_apply (by fun_prop) hS.compl]
    have hz : (fun y : Sphere d => R • y.val) ⁻¹' Sᶜ = ∅ := by
      ext y
      simp [S, norm_smul, Real.norm_eq_abs, abs_of_pos hR, y.property]
    rw [hz, measure_empty]
  have hmass : μ.real Set.univ = ν.real Set.univ :=
    congrArg ENNReal.toReal ((tupleCounting_univ (d+1) N u).trans
      (negativeSphericalBackground_mass d N R hRN).symm)
  have hdiam (z : Rd (d+1)) (hz : z ∈ S) (w : Rd (d+1)) (hw : w ∈ S) :
      ‖z-w‖ ≤ 2*R := by
    have h := norm_sub_le z w
    change ‖z‖ = R at hz
    change ‖w‖ = R at hw
    simpa only [hz, hw, two_mul] using h
  have hμμ := negativeSpherical_pair_integrable d q R hq μ μ hμ hμ
  have hμν := negativeSpherical_pair_integrable d q R hq μ ν hμ hν
  have hνν := negativeSpherical_pair_integrable d q R hq ν ν hν hν
  have hA : (∫ p : Rd (d+1) × Rd (d+1), K_s (-q) ‖p.1-p.2‖ ∂μ.prod μ) =
      R^q * Riesz.Energy.kernelEnergy d (-q) N x := by
    rw [integral_prod _ hμμ, integral_tupleCounting]
    have hij (i j : Fin N) : K_s (-q) ‖u i-u j‖ =
        R^q * (if i = j then 0 else K_s (-q) (chord d (x.val i) (x.val j))) := by
      dsimp only [u]
      rw [negativeSpherical_kernel_homogeneous d q R hR]
      by_cases h : i = j
      · simp [h, chord, K_s, Real.zero_rpow hq.ne']
      · simp only [h, if_false]
    simp only [μ, integral_tupleCounting, hij]
    simp only [Riesz.Energy.kernelEnergy, Finset.mul_sum]
  have hB : (∫ p : Rd (d+1) × Rd (d+1), K_s (-q) ‖p.1-p.2‖ ∂μ.prod ν) =
      (N : ℝ)^2 * (R^q * V_K d (-q)) := by
    rw [integral_prod _ hμν, integral_tupleCounting]
    simp_rw [show ∀ i : Fin N, (∫ y, K_s (-q) ‖u i-y‖ ∂ν) =
        (N : ℝ) * (R^q * V_K d (-q)) from
      fun i => negativeSpherical_section d N hd q R hq hR hRN (x.val i)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hC : (∫ p : Rd (d+1) × Rd (d+1), K_s (-q) ‖p.1-p.2‖ ∂ν.prod ν) =
      (N : ℝ)^2 * (R^q * V_K d (-q)) := by
    have hm : StronglyMeasurable (fun p : Rd (d+1) × Rd (d+1) =>
        K_s (-q) ‖p.1-p.2‖) := by
      have hm' : Measurable (fun p : Rd (d+1) × Rd (d+1) => ‖p.1-p.2‖^q / (-q)) :=
        ((measurable_fst.sub measurable_snd).norm.pow_const q).div_const (-q)
      simpa only [K_s, neg_neg] using hm'.stronglyMeasurable
    calc
      _ = ∫ z, (∫ y, K_s (-q) ‖z-y‖ ∂ν) ∂ν := integral_prod _ hνν
      _ = ∫ z, (∫ y, K_s (-q) ‖z-y‖ ∂ν)
          ∂(ENNReal.ofReal (N : ℝ) • sphericalMeasure d).map
            (fun y : Sphere d => R • y.val) :=
        congrArg (fun ρ : Measure (Rd (d+1)) =>
          ∫ z, (∫ y, K_s (-q) ‖z-y‖ ∂ν) ∂ρ)
            (negativeSphericalBackground_form d N R hRN)
      _ = ∫ z : Sphere d, (∫ y, K_s (-q) ‖R • z.val-y‖ ∂ν)
          ∂ENNReal.ofReal (N : ℝ) • sphericalMeasure d :=
        integral_map_of_stronglyMeasurable (by fun_prop) hm.integral_prod_right'
      _ = _ := by
        simp_rw [show ∀ z : Sphere d, (∫ y, K_s (-q) ‖R • z.val-y‖ ∂ν) =
            (N : ℝ) * (R^q * V_K d (-q)) from
          fun z => negativeSpherical_section d N hd q R hq hR hRN z]
        rw [integral_smul_measure]
        simp only [ENNReal.toReal_ofReal (Nat.cast_nonneg N), integral_const,
          probReal_univ, smul_eq_mul]
        ring
  change Riesz.Analysis.signedDiscrepancyEnergy q (μ.toSignedMeasure-ν.toSignedMeasure) = _
  rw [Riesz.Analysis.signedDiscrepancyEnergy_sub_toSignedMeasure
    q (2*R) hq hq2 μ ν hmass S hS hμ hν hdiam,
    Riesz.Analysis.differenceKernelQuadratic, hA, hB, hC]
  ring

/-- Pointwise normalization of an actual radius-R tuple; no random inverse map
or measurable choice of tuple labels is needed. -/
def negativeNormalizeSphereConfiguration (d N : ℕ) (R : ℝ) (hR : 0 < R)
    (x : Fin N → Rd (d+1)) (hinj : Function.Injective x)
    (hnorm : ∀ i, ‖x i‖ = R) : SphereConfiguration d N :=
  ⟨fun i => ⟨R⁻¹ • x i, by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR),
      hnorm i, inv_mul_cancel₀ hR.ne']⟩, by
    intro i j hij
    apply hinj
    have h := congrArg (fun z : Sphere d => R • z.val) hij
    simpa only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul] using h⟩

theorem negativeNormalizeSphereConfiguration_recover (d N : ℕ) (R : ℝ) (hR : 0 < R)
    (x : Fin N → Rd (d+1)) (hinj : Function.Injective x) (hnorm : ∀ i, ‖x i‖ = R) :
    (fun i => R • ((negativeNormalizeSphereConfiguration d N R hR x hinj hnorm).val i).val) = x := by
  funext i
  change R • (R⁻¹ • x i) = x i
  simp only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

theorem negativePhysicalSphereTuple_energy_eq (d N : ℕ) (hd : 2 ≤ d)
    (q R : ℝ) (hq : 0 < q) (hq2 : q < 2) (hR : 0 < R)
    (hRN : R^d * omega d = (N : ℝ)) (x : Fin N → Rd (d+1))
    (hinj : Function.Injective x) (hnorm : ∀ i, ‖x i‖ = R) :
    Riesz.Analysis.signedDiscrepancyEnergy q (negativeSphericalTupleDiscrepancy d N R x) =
      R^q * (Riesz.Energy.kernelEnergy d (-q) N
        (negativeNormalizeSphereConfiguration d N R hR x hinj hnorm) -
          V_K d (-q) * (N : ℝ)^2) := by
  have h := negativeSphericalTuple_energy_eq d N hd q R hq hq2 hR hRN
    (negativeNormalizeSphereConfiguration d N R hR x hinj hnorm)
  rwa [negativeNormalizeSphereConfiguration_recover d N R hR x hinj hnorm] at h

/-- The actual physical tuple is a pointwise competitor for the exact infimum. -/
theorem negativePhysicalSphereTuple_optimal_le (d N : ℕ) (hd : 2 ≤ d)
    (q R : ℝ) (hq : 0 < q) (hq2 : q < 2) (hR : 0 < R)
    (hRN : R^d * omega d = (N : ℝ)) (x : Fin N → Rd (d+1))
    (hinj : Function.Injective x) (hnorm : ∀ i, ‖x i‖ = R) :
    R^q * (E_K d (-q) N - V_K d (-q) * (N : ℝ)^2) ≤
      Riesz.Analysis.signedDiscrepancyEnergy q (negativeSphericalTupleDiscrepancy d N R x) := by
  let y := negativeNormalizeSphereConfiguration d N R hR x hinj hnorm
  have hqd : -q < (d : ℝ) := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hbelow : BddBelow (Set.range (Riesz.Energy.kernelEnergy d (-q) N)) := by
    refine ⟨V_K d (-q) * (N : ℝ)^2 + Problem1.part5_energy_constants_negative d (-q) *
      (N : ℝ)^(1 + (-q)/(d : ℝ)), ?_⟩
    rintro r ⟨z, rfl⟩
    exact negative_sphere_kernelEnergy_lower d hd (-q) (neg_lt_neg hq2)
      (neg_lt_zero.mpr hq) hqd N z
  have hopt : E_K d (-q) N ≤ Riesz.Energy.kernelEnergy d (-q) N y :=
    csInf_le hbelow (Set.mem_range_self y)
  rw [negativePhysicalSphereTuple_energy_eq d N hd q R hq hq2 hR hRN x hinj hnorm]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hopt _)
    (Real.rpow_nonneg hR.le q)

end Riesz.Negative
