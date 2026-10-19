import Riesz.Analysis.DiscrepancyYoung

/-!
The discrepancy of two finite positive measures, without a mutual-singularity
assumption. This permits measurable positive-measure kernels to represent
random signed discrepancy energies even when input and output share atoms.
-/

noncomputable section

open MeasureTheory RieszShowcase

namespace Riesz.Analysis

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

theorem signedGaussianPotential_sub_toSignedMeasure (t : ℝ) (ht : 0 ≤ t)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (z : V) :
    signedGaussianPotential t (μ.toSignedMeasure - ν.toSignedMeasure) z =
      (∫ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂μ) -
        (∫ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂ν) := by
  rw [signedGaussianPotential_eq_integral t ht]
  simpa only [VectorMeasure.integral_toSignedMeasure, neg_mul] using
    VectorMeasure.integral_sub_vectorMeasure
      (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
      (integrable_gaussian_signed (2 * t) (mul_nonneg (by norm_num) ht) μ.toSignedMeasure z)
      (integrable_gaussian_signed (2 * t) (mul_nonneg (by norm_num) ht) ν.toSignedMeasure z)

omit [NormedAddCommGroup V] [BorelSpace V] in
theorem toSignedMeasure_sub_mass_zero (μ ν : Measure V)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real Set.univ = ν.real Set.univ) :
    (μ.toSignedMeasure - ν.toSignedMeasure) Set.univ = 0 := by
  simp only [_root_.sub_apply, Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    hmass, sub_self]

omit [NormedAddCommGroup V] [BorelSpace V] in
theorem toSignedMeasure_sub_concentrated (μ ν : Measure V)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (S : Set V) (hS : MeasurableSet S)
    (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0) :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Sᶜ = 0 := by
  apply totalVariation_null_of_subsets _ Sᶜ hS.compl
  intro A hA
  simp [_root_.sub_apply, Measure.toSignedMeasure_apply, measureReal_def,
    measure_mono_null hA hμ, measure_mono_null hA hν]

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem signed_gaussian_quadratic_sub_toSignedMeasure (t : ℝ) (ht : 0 < t)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    signedKernelQuadratic (fun x y : V => Real.exp (-t * ‖x - y‖ ^ 2))
      (μ.toSignedMeasure - ν.toSignedMeasure) =
        differenceKernelQuadratic (fun x y : V => Real.exp (-t * ‖x - y‖ ^ 2)) μ ν := by
  rw [signed_gaussian_quadratic_eq_square t ht, differenceKernelQuadratic,
    gaussian_quadratic_eq_integral_square t ht]
  simp only [signedGaussianPotential_sub_toSignedMeasure t ht.le]

variable [SecondCountableTopology V]

/-- Equal-mass finite measures may share atoms: their signed discrepancy still
equals the three positive-measure integrals, with no Jordan-part computation. -/
theorem signedDiscrepancyEnergy_sub_toSignedMeasure (q L : ℝ)
    (hq : 0 < q) (hq_two : q < 2) (μ ν : Measure V)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real Set.univ = ν.real Set.univ)
    (S : Set V) (hS : MeasurableSet S) (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L) :
    signedDiscrepancyEnergy q (μ.toSignedMeasure - ν.toSignedMeasure) =
      differenceKernelQuadratic (fun x y : V => K_s (-q) ‖x - y‖) μ ν := by
  rw [signedDiscrepancyEnergy_eq_kernel,
    negative_signed_quadratic_eq (-q) L (neg_lt_neg hq_two) (neg_lt_zero.mpr hq) _
      (toSignedMeasure_sub_mass_zero μ ν hmass) S
      (toSignedMeasure_sub_concentrated μ ν S hS hμ hν) hdiam,
    negative_riesz_quadratic_eq (-q) L (neg_lt_neg hq_two) (neg_lt_zero.mpr hq) μ ν hmass
      (ae_distance_le_of_concentrated μ μ S L hμ hμ hdiam)
      (ae_distance_le_of_concentrated μ ν S L hμ hν hdiam)
      (ae_distance_le_of_concentrated ν ν S L hν hν hdiam)]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [← neg_mul, signed_gaussian_quadratic_sub_toSignedMeasure t ht]

end Riesz.Analysis
