import Riesz.Stationary.GridCovariance

/-! The grid covariance is the expected finite-cell signed Gaussian discrepancy.
This identifies the actual showcase profile before integrating in the scale parameter. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Stationary

def tupleGaussianSum (d n : ℕ) (t : ℝ) (x : Fin n → Rd d) : ℝ :=
  ∑ ij : Fin n × Fin n, Real.exp (-t * ‖x ij.1 - x ij.2‖ ^ 2)

theorem tupleGaussian_toReal (d n : ℕ) (t : ℝ) (x : Fin n → Rd d) :
    (tuplePairSum d n (gaussianPairKernel d t) x).toReal = tupleGaussianSum d n t x := by
  unfold tuplePairSum gaussianPairKernel tupleGaussianSum
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, norm_sub_rev, neg_mul]

theorem tupleGaussianSum_integrable (d n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (Qcell : Measure (Fin n → Rd d)) [IsFiniteMeasure Qcell] :
    Integrable (tupleGaussianSum d n t) Qcell := by
  have hfinite : (∫⁻ x, tuplePairSum d n (gaussianPairKernel d t) x ∂Qcell) ≠ ∞ :=
    ((lintegral_mono (fun x => tuplePairSum_gaussian_le d n t ht x)).trans_lt
      (lintegral_const_lt_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n)))).ne
  simpa only [tupleGaussian_toReal] using integrable_toReal_of_lintegral_ne_top
    (measurable_tuplePairSum d n _ (measurable_gaussianPairKernel d t)).aemeasurable hfinite

theorem tupleGaussian_lintegral_toReal (d n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (Qcell : Measure (Fin n → Rd d)) :
    (∫⁻ x, tuplePairSum d n (gaussianPairKernel d t) x ∂Qcell).toReal =
      ∫ x, tupleGaussianSum d n t x ∂Qcell := by
  simpa only [tupleGaussian_toReal] using
    (integral_toReal (measurable_tuplePairSum d n _ (measurable_gaussianPairKernel d t)).aemeasurable
      (ae_of_all Qcell (fun x => (tuplePairSum_gaussian_le d n t ht x).trans_lt
        (ENNReal.pow_lt_top (ENNReal.natCast_lt_top n))))).symm

theorem gaussianPair_lintegral_toReal (d : ℕ) (t : ℝ) (μ ν : Measure (Rd d)) :
    (∫⁻ p, gaussianPairKernel d t p ∂μ.prod ν).toReal =
      ∫ p : Rd d × Rd d, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂μ.prod ν := by
  have hmeas : AEStronglyMeasurable
      (fun p : Rd d × Rd d => Real.exp (-t * ‖p.1 - p.2‖ ^ 2)) (μ.prod ν) :=
    (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_fst.sub continuous_snd).norm.pow 2))).aestronglyMeasurable
  simpa only [gaussianPairKernel, norm_sub_rev, neg_mul] using
    (integral_eq_lintegral_of_nonneg_ae
      (ae_of_all (μ.prod ν) (fun _ => (Real.exp_pos _).le)) hmeas).symm

theorem tupleGaussian_background_cross_integrable (d n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (Qcell : Measure (Fin n → Rd d)) [IsFiniteMeasure Qcell]
    (ν : Measure (Rd d)) [IsFiniteMeasure ν] :
    Integrable (fun x => ∑ i, ∫ b, Real.exp (-t * ‖x i - b‖ ^ 2) ∂ν) Qcell := by
  exact Riesz.Negative.tupleMeanMeasure_integrable_sum d n Qcell
    (fun a => ∫ b, Real.exp (-t * ‖a - b‖ ^ 2) ∂ν)
    (Riesz.Analysis.integrable_gaussian_prod_measure t ht
      (Riesz.Negative.tupleMeanMeasure d n Qcell) ν).integral_prod_left

theorem tupleGaussian_background_cross_mean (d m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) :
    (∫ x, ∑ i, ∫ b, Real.exp (-t * ‖x i - b‖ ^ 2)
      ∂volume.restrict (cube d (m : ℝ)) ∂Qcell) =
      ∫ p : Rd d × Rd d, Real.exp (-t * ‖p.1 - p.2‖ ^ 2)
        ∂(volume.restrict (cube d (m : ℝ))).prod (volume.restrict (cube d (m : ℝ))) := by
  letI : IsProbabilityMeasure Qcell := hQ.1
  rw [← Riesz.Negative.tupleBalanced_tupleMeanMeasure d m Qcell hQ]
  have hk := Riesz.Analysis.integrable_gaussian_prod_measure t ht
    (Riesz.Negative.tupleMeanMeasure d (m ^ d) Qcell) (Riesz.Negative.tupleMeanMeasure d (m ^ d) Qcell)
  exact (Riesz.Negative.tupleMeanMeasure_integral_sum d (m ^ d) Qcell
    (fun a => ∫ b, Real.exp (-t * ‖a - b‖ ^ 2) ∂Riesz.Negative.tupleMeanMeasure d (m ^ d) Qcell)
      hk.integral_prod_left).trans (integral_prod _ hk).symm

theorem tupleGaussian_signedDiscrepancy_eq (d m : ℕ) (hd : 0 < d) (t : ℝ) (ht : 0 ≤ t)
    (x : Fin (m ^ d) → Rd d) :
    Riesz.Analysis.signedKernelQuadratic
      (fun a b : Rd d => Real.exp (-t * ‖a - b‖ ^ 2)) (Riesz.Negative.tupleDiscrepancy d m x) =
      tupleGaussianSum d (m ^ d) t x -
        2 * (∑ i, ∫ b, Real.exp (-t * ‖x i - b‖ ^ 2) ∂volume.restrict (cube d (m : ℝ))) +
        ∫ p : Rd d × Rd d, Real.exp (-t * ‖p.1 - p.2‖ ^ 2)
          ∂(volume.restrict (cube d (m : ℝ))).prod (volume.restrict (cube d (m : ℝ))) := by
  letI := Riesz.Negative.tupleCounting_isFiniteMeasure d (m ^ d) x
  letI := Riesz.Negative.cube_background_isFiniteMeasure d m
  obtain ⟨hpos, hneg⟩ := Riesz.Negative.tupleDiscrepancy_jordan_parts d m hd x
  rw [Riesz.Analysis.signedKernelQuadratic_eq_difference _
      (fun a b => congrArg (fun r : ℝ => Real.exp (-t * r ^ 2)) (norm_sub_rev a b)),
    hpos, hneg, Riesz.Analysis.differenceKernelQuadratic]
  rw [integral_prod _ (Riesz.Analysis.integrable_gaussian_prod_measure t ht
      (Riesz.Negative.tupleCounting d (m ^ d) x) (Riesz.Negative.tupleCounting d (m ^ d) x)),
    integral_prod _ (Riesz.Analysis.integrable_gaussian_prod_measure t ht
      (Riesz.Negative.tupleCounting d (m ^ d) x) (volume.restrict (cube d (m : ℝ)))),
    Riesz.Negative.iterated_integral_tupleCounting, Riesz.Negative.integral_tupleCounting]
  rfl

theorem tupleGaussian_signedDiscrepancy_integrable (d m : ℕ) (hd : 0 < d)
    (t : ℝ) (ht : 0 ≤ t) (Qcell : Measure (Fin (m ^ d) → Rd d)) [IsFiniteMeasure Qcell] :
    Integrable (fun x => Riesz.Analysis.signedKernelQuadratic
      (fun a b : Rd d => Real.exp (-t * ‖a - b‖ ^ 2)) (Riesz.Negative.tupleDiscrepancy d m x)) Qcell := by
  letI := Riesz.Negative.cube_background_isFiniteMeasure d m
  exact (((tupleGaussianSum_integrable d (m ^ d) t ht Qcell).sub
    ((tupleGaussian_background_cross_integrable d (m ^ d) t ht Qcell
      (volume.restrict (cube d (m : ℝ)))).const_mul 2)).add
    (integrable_const (∫ p : Rd d × Rd d, Real.exp (-t * ‖p.1 - p.2‖ ^ 2)
      ∂(volume.restrict (cube d (m : ℝ))).prod (volume.restrict (cube d (m : ℝ)))))).congr
    (ae_of_all Qcell (fun x => (tupleGaussian_signedDiscrepancy_eq d m hd t ht x).symm))

theorem tupleGaussian_expected_signedDiscrepancy (d m : ℕ) (hd : 0 < d)
    (t : ℝ) (ht : 0 ≤ t) (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) :
    (∫ x, Riesz.Analysis.signedKernelQuadratic
      (fun a b : Rd d => Real.exp (-t * ‖a - b‖ ^ 2)) (Riesz.Negative.tupleDiscrepancy d m x) ∂Qcell) =
      (∫⁻ x, tuplePairSum d (m ^ d) (gaussianPairKernel d t) x ∂Qcell).toReal -
        (∫⁻ p, gaussianPairKernel d t p
          ∂(volume.restrict (cube d (m : ℝ))).prod (volume.restrict (cube d (m : ℝ)))).toReal := by
  letI : IsProbabilityMeasure Qcell := hQ.1
  letI := Riesz.Negative.cube_background_isFiniteMeasure d m
  rw [tupleGaussian_lintegral_toReal d (m ^ d) t ht Qcell,
    gaussianPair_lintegral_toReal d t]
  simp_rw [tupleGaussian_signedDiscrepancy_eq d m hd t ht]
  have hA := tupleGaussianSum_integrable d (m ^ d) t ht Qcell
  have hC := tupleGaussian_background_cross_integrable d (m ^ d) t ht Qcell
    (volume.restrict (cube d (m : ℝ)))
  have hAC : Integrable (fun x => tupleGaussianSum d (m ^ d) t x -
      2 * (∑ i, ∫ b, Real.exp (-t * ‖x i - b‖ ^ 2)
        ∂volume.restrict (cube d (m : ℝ)))) Qcell := hA.sub (hC.const_mul 2)
  have hD : Integrable (fun _x : Fin (m ^ d) → Rd d =>
      ∫ p : Rd d × Rd d, Real.exp (-t * ‖p.1 - p.2‖ ^ 2)
        ∂(volume.restrict (cube d (m : ℝ))).prod (volume.restrict (cube d (m : ℝ)))) Qcell :=
    integrable_const _
  rw [integral_add hAC hD, integral_sub hA (hC.const_mul 2), integral_const_mul, integral_const]
  rw [tupleGaussian_background_cross_mean d m t ht Qcell hQ]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  ring

/-- The exact covariance identity from the paper, for the concrete admissible grid law. -/
theorem Q_randomShiftGridLaw_signedGaussian_covariance (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) (t : ℝ) (ht : 0 < t) :
    (Q d (randomShiftGridLaw d m Qcell) t).toReal + 1 - B d t =
      ((m : ℝ) ^ d)⁻¹ * ∫ x, Riesz.Analysis.signedKernelQuadratic
        (fun a b : Rd d => Real.exp (-t * ‖a - b‖ ^ 2))
          (Riesz.Negative.tupleDiscrepancy d m x) ∂Qcell := by
  rw [Q_randomShiftGridLaw_real_covariance d m hm Qcell hQ t ht,
    ← tupleGaussian_expected_signedDiscrepancy d m hd t ht.le Qcell hQ]

theorem Q_randomShiftGridLaw_covariance_nonneg (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) (t : ℝ) (ht : 0 < t) :
    0 ≤ (Q d (randomShiftGridLaw d m Qcell) t).toReal + 1 - B d t := by
  rw [Q_randomShiftGridLaw_signedGaussian_covariance d m hd hm Qcell hQ t ht]
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg m) d))
    (integral_nonneg (fun x => Riesz.Analysis.gaussian_signed_quadratic_nonneg t ht
      (Riesz.Negative.tupleDiscrepancy d m x)))

end Riesz.Stationary
