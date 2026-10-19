import Riesz.Analysis.NegativeGaussian
import Mathlib.MeasureTheory.VectorMeasure.Integral

/-!
Quadratic Young bounds for compact zero-mass signed discrepancies.
These combine independent sampling with multiscale atomic rounding without
requiring a general theorem about conditional signed-measure increments.
-/

noncomputable section

open MeasureTheory RieszShowcase

namespace Riesz.Analysis

theorem signed_variation_le_totalVariation {X : Type*} [MeasurableSpace X]
    (η : SignedMeasure X) : η.variation ≤ η.totalVariation := by
  calc
    η.variation = η.toJordanDecomposition.toSignedMeasure.variation :=
      (congrArg VectorMeasure.variation (SignedMeasure.toSignedMeasure_toJordanDecomposition η)).symm
    _ ≤ η.totalVariation := by
      simpa only [JordanDecomposition.toSignedMeasure, SignedMeasure.totalVariation,
        Measure.variation_toSignedMeasure] using
        (VectorMeasure.variation_sub_le (μ := η.toJordanDecomposition.posPart.toSignedMeasure)
          (ν := η.toJordanDecomposition.negPart.toSignedMeasure))

instance signed_variation_isFiniteMeasure {X : Type*} [MeasurableSpace X]
    (η : SignedMeasure X) : IsFiniteMeasure η.variation := by
  letI : IsFiniteMeasure η.totalVariation :=
    inferInstanceAs (IsFiniteMeasure
      (η.toJordanDecomposition.posPart + η.toJordanDecomposition.negPart))
  exact isFiniteMeasure_of_le η.totalVariation (signed_variation_le_totalVariation η)

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

theorem integrable_gaussian_signed (t : ℝ) (ht : 0 ≤ t) (η : SignedMeasure V) (z : V) :
    η.Integrable (fun x => Real.exp (-t * ‖x - z‖ ^ 2)) := by
  simpa only [norm_sub_rev] using integrable_gaussian_finite_measure t ht z η.variation

def signedGaussianPotential (t : ℝ) (η : SignedMeasure V) (z : V) : ℝ :=
  (∫ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂η.toJordanDecomposition.posPart) -
    (∫ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂η.toJordanDecomposition.negPart)

theorem signedGaussianPotential_eq_integral (t : ℝ) (ht : 0 ≤ t)
    (η : SignedMeasure V) (z : V) :
    signedGaussianPotential t η z = ∫ᵛ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂<•η := by
  symm
  calc
    _ = ∫ᵛ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2)
        ∂<•η.toJordanDecomposition.toSignedMeasure :=
      congrArg (fun θ : SignedMeasure V =>
        ∫ᵛ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂<•θ)
        (SignedMeasure.toSignedMeasure_toJordanDecomposition η).symm
    _ = signedGaussianPotential t η z := by
      have hp : η.toJordanDecomposition.posPart.toSignedMeasure.Integrable
          (fun x : V => Real.exp (-2 * t * ‖x - z‖ ^ 2)) := by
        simpa only [neg_mul] using integrable_gaussian_signed (2 * t)
          (mul_nonneg (by norm_num) ht) η.toJordanDecomposition.posPart.toSignedMeasure z
      have hn : η.toJordanDecomposition.negPart.toSignedMeasure.Integrable
          (fun x : V => Real.exp (-2 * t * ‖x - z‖ ^ 2)) := by
        simpa only [neg_mul] using integrable_gaussian_signed (2 * t)
          (mul_nonneg (by norm_num) ht) η.toJordanDecomposition.negPart.toSignedMeasure z
      simpa only [JordanDecomposition.toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
        signedGaussianPotential] using
        (VectorMeasure.integral_sub_vectorMeasure (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip) hp hn)

theorem signedGaussianPotential_add (t : ℝ) (ht : 0 ≤ t)
    (η ζ : SignedMeasure V) (z : V) :
    signedGaussianPotential t (η + ζ) z =
      signedGaussianPotential t η z + signedGaussianPotential t ζ z := by
  rw [signedGaussianPotential_eq_integral t ht (η + ζ),
    signedGaussianPotential_eq_integral t ht η, signedGaussianPotential_eq_integral t ht ζ]
  simpa only [neg_mul] using VectorMeasure.integral_add_vectorMeasure
    (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (integrable_gaussian_signed (2 * t) (mul_nonneg (by norm_num) ht) η z)
    (integrable_gaussian_signed (2 * t) (mul_nonneg (by norm_num) ht) ζ z)

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem signed_gaussian_quadratic_eq_square (t : ℝ) (ht : 0 < t) (η : SignedMeasure V) :
    signedKernelQuadratic (fun x y : V => Real.exp (-t * ‖x - y‖ ^ 2)) η =
      (4 * t / Real.pi) ^ ((Module.finrank ℝ V : ℝ) / 2) *
        ∫ z : V, (signedGaussianPotential t η z) ^ 2 := by
  rw [signedKernelQuadratic_eq_difference _
    (fun x y => congrArg (fun r : ℝ => Real.exp (-t * r ^ 2)) (norm_sub_rev x y))]
  exact gaussian_quadratic_eq_integral_square t ht
    η.toJordanDecomposition.posPart η.toJordanDecomposition.negPart

theorem integrable_signedGaussianPotential_square (t : ℝ) (ht : 0 < t)
    (η : SignedMeasure V) : Integrable (fun z : V => (signedGaussianPotential t η z) ^ 2) := by
  let f : V → ℝ := fun z =>
    ∫ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂η.toJordanDecomposition.posPart
  let g : V → ℝ := fun z =>
    ∫ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂η.toJordanDecomposition.negPart
  have hff : Integrable (fun z => f z * f z) :=
    integrable_gaussian_smoothing_product t ht
      η.toJordanDecomposition.posPart η.toJordanDecomposition.posPart
  have hfg : Integrable (fun z => f z * g z) :=
    integrable_gaussian_smoothing_product t ht
      η.toJordanDecomposition.posPart η.toJordanDecomposition.negPart
  have hgg : Integrable (fun z => g z * g z) :=
    integrable_gaussian_smoothing_product t ht
      η.toJordanDecomposition.negPart η.toJordanDecomposition.negPart
  convert! (hff.sub (hfg.const_mul 2)).add hgg using 1
  ext z
  change (f z - g z) ^ 2 = f z * f z - 2 * (f z * g z) + g z * g z
  ring

theorem real_quadratic_young (a b τ : ℝ) (hτ : 0 < τ) :
    (a + b) ^ 2 ≤ (1 + τ) * a ^ 2 + (1 + τ⁻¹) * b ^ 2 := by
  apply (mul_le_mul_iff_right₀ hτ).mp
  field_simp
  nlinarith [sq_nonneg (τ * a - b)]

theorem signed_gaussian_quadratic_young (t τ : ℝ) (ht : 0 < t) (hτ : 0 < τ)
    (η ζ : SignedMeasure V) :
    signedKernelQuadratic (fun x y : V => Real.exp (-t * ‖x - y‖ ^ 2)) (η + ζ) ≤
      (1 + τ) * signedKernelQuadratic (fun x y : V => Real.exp (-t * ‖x - y‖ ^ 2)) η +
        (1 + τ⁻¹) * signedKernelQuadratic (fun x y : V => Real.exp (-t * ‖x - y‖ ^ 2)) ζ := by
  simp_rw [signed_gaussian_quadratic_eq_square t ht]
  have hbound := integral_mono (integrable_signedGaussianPotential_square t ht (η + ζ))
    (((integrable_signedGaussianPotential_square t ht η).const_mul (1 + τ)).add
      ((integrable_signedGaussianPotential_square t ht ζ).const_mul (1 + τ⁻¹)))
    (fun z => (signedGaussianPotential_add t ht.le η ζ z).symm ▸
      real_quadratic_young (signedGaussianPotential t η z) (signedGaussianPotential t ζ z) τ hτ)
  simp only [Pi.add_apply] at hbound
  rw [integral_add ((integrable_signedGaussianPotential_square t ht η).const_mul (1 + τ))
    ((integrable_signedGaussianPotential_square t ht ζ).const_mul (1 + τ⁻¹)),
    integral_const_mul, integral_const_mul] at hbound
  simpa only [mul_add, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hbound
      (Real.rpow_nonneg (by positivity : 0 ≤ 4 * t / Real.pi) ((Module.finrank ℝ V : ℝ) / 2))

theorem totalVariation_null_of_subsets {X : Type*} [MeasurableSpace X]
    (η : SignedMeasure X) (A : Set X) (hA : MeasurableSet A)
    (hη : ∀ B : Set X, B ⊆ A → η B = 0) : η.totalVariation A = 0 := by
  obtain ⟨i, hi, hip, hin, hpos, hneg⟩ := η.toJordanDecomposition_spec
  rw [SignedMeasure.totalVariation, Measure.add_apply, hpos, hneg,
    SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hA,
    SignedMeasure.toMeasureOfLEZero_apply _ _ _ hA]
  simp [hη (i ∩ A) Set.inter_subset_right, hη (iᶜ ∩ A) Set.inter_subset_right]

theorem totalVariation_add_concentrated {X : Type*} [MeasurableSpace X]
    (η ζ : SignedMeasure X) (S : Set X)
    (hS : MeasurableSet S) (hη : η.totalVariation Sᶜ = 0) (hζ : ζ.totalVariation Sᶜ = 0) :
    (η + ζ).totalVariation Sᶜ = 0 := by
  apply totalVariation_null_of_subsets (η + ζ) Sᶜ hS.compl
  intro B hB
  simp only [_root_.add_apply, η.null_of_totalVariation_zero (measure_mono_null hB hη),
    ζ.null_of_totalVariation_zero (measure_mono_null hB hζ), add_zero]

variable [SecondCountableTopology V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem integrable_signed_gaussian_profile (s L : ℝ) (hs_lower : -2 < s) (hs_upper : s < 0)
    (η : SignedMeasure V) (hmass : η Set.univ = 0) (S : Set V)
    (hsupport : η.totalVariation Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L) :
    IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1) *
      signedKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2))) η) (Set.Ioi 0) := by
  have hparts : η.toJordanDecomposition.posPart Sᶜ = 0 ∧
      η.toJordanDecomposition.negPart Sᶜ = 0 := by
    simpa only [SignedMeasure.totalVariation, Measure.add_apply, add_eq_zero] using hsupport
  have hA := integrable_negative_gaussian_profile s L hs_lower hs_upper
    η.toJordanDecomposition.posPart η.toJordanDecomposition.posPart
    (ae_distance_le_of_concentrated _ _ S L hparts.1 hparts.1 hdiam)
  have hB := integrable_negative_gaussian_profile s L hs_lower hs_upper
    η.toJordanDecomposition.posPart η.toJordanDecomposition.negPart
    (ae_distance_le_of_concentrated _ _ S L hparts.1 hparts.2 hdiam)
  have hC := integrable_negative_gaussian_profile s L hs_lower hs_upper
    η.toJordanDecomposition.negPart η.toJordanDecomposition.negPart
    (ae_distance_le_of_concentrated _ _ S L hparts.2 hparts.2 hdiam)
  refine ((hA.sub (hB.const_mul 2)).add hC).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [signed_gaussian_quadratic_eq]
  rw [← gaussian_sub_one_quadratic_eq t (Set.mem_Ioi.mp ht).le
    η.toJordanDecomposition.posPart η.toJordanDecomposition.negPart
    (jordan_masses_eq_of_zero η hmass)]
  dsimp only [differenceKernelQuadratic]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem signedDiscrepancyEnergy_young (q τ : ℝ) (hq : 0 < q) (hq_two : q < 2) (hτ : 0 < τ)
    (η ζ : SignedMeasure V) (hηmass : η Set.univ = 0) (hζmass : ζ Set.univ = 0)
    (S : Set V) (hcompact : IsCompact S)
    (hηsupport : η.totalVariation Sᶜ = 0) (hζsupport : ζ.totalVariation Sᶜ = 0) :
    signedDiscrepancyEnergy q (η + ζ) ≤
      (1 + τ) * signedDiscrepancyEnergy q η + (1 + τ⁻¹) * signedDiscrepancyEnergy q ζ := by
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp hcompact.isBounded
  have hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L := fun x hx y hy => by
    simpa only [dist_eq_norm] using hL hx hy
  have hsumsupport := totalVariation_add_concentrated η ζ S hcompact.measurableSet hηsupport hζsupport
  have hsummass : (η + ζ) Set.univ = 0 := by simp only [_root_.add_apply, hηmass, hζmass, add_zero]
  have hiη := integrable_signed_gaussian_profile (-q) L (neg_lt_neg hq_two) (neg_lt_zero.mpr hq)
    η hηmass S hηsupport hdiam
  have hiζ := integrable_signed_gaussian_profile (-q) L (neg_lt_neg hq_two) (neg_lt_zero.mpr hq)
    ζ hζmass S hζsupport hdiam
  have hisum := integrable_signed_gaussian_profile (-q) L (neg_lt_neg hq_two) (neg_lt_zero.mpr hq)
    (η + ζ) hsummass S hsumsupport hdiam
  rw [(signedDiscrepancyEnergy_gaussian_compact q hq hq_two (η + ζ) hsummass S hcompact hsumsupport).1,
    (signedDiscrepancyEnergy_gaussian_compact q hq hq_two η hηmass S hcompact hηsupport).1,
    (signedDiscrepancyEnergy_gaussian_compact q hq hq_two ζ hζmass S hcompact hζsupport).1]
  have hpoint :
      (fun t : ℝ => t ^ (-q / 2 - 1) *
        signedKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2))) (η + ζ)) ≤ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t : ℝ => (1 + τ) * (t ^ (-q / 2 - 1) *
        signedKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2))) η) +
        (1 + τ⁻¹) * (t ^ (-q / 2 - 1) *
        signedKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2))) ζ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [mul_add, mul_left_comm, mul_assoc, neg_mul] using
      mul_le_mul_of_nonneg_left (signed_gaussian_quadratic_young t τ ht hτ η ζ)
        (Real.rpow_nonneg ht.le (-q / 2 - 1))
  have hbound := integral_mono_ae hisum
    ((hiη.const_mul (1 + τ)).add (hiζ.const_mul (1 + τ⁻¹))) hpoint
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hiη.const_mul (1 + τ)) (hiζ.const_mul (1 + τ⁻¹)),
    integral_const_mul, integral_const_mul] at hbound
  simpa only [mul_add, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hbound (gamma_s_pos (-q) (neg_lt_neg hq_two)).le

theorem signedDiscrepancyEnergy_add_le (q : ℝ) (hq : 0 < q) (hq_two : q < 2)
    (η ζ : SignedMeasure V) (hηmass : η Set.univ = 0) (hζmass : ζ Set.univ = 0)
    (S : Set V) (hcompact : IsCompact S)
    (hηsupport : η.totalVariation Sᶜ = 0) (hζsupport : ζ.totalVariation Sᶜ = 0) :
    signedDiscrepancyEnergy q (η + ζ) ≤
      2 * signedDiscrepancyEnergy q η + 2 * signedDiscrepancyEnergy q ζ := by
  simpa only [inv_one, show (1 : ℝ) + 1 = 2 by norm_num] using
    signedDiscrepancyEnergy_young q 1 hq hq_two (by norm_num)
    η ζ hηmass hζmass S hcompact hηsupport hζsupport

end Riesz.Analysis
