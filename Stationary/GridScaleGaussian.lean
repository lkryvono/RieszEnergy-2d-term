import Riesz.Stationary.GridDiscrepancyGaussian
import Riesz.Stationary.Infimum

/-! Scale integration of the actual finite-cell signed Gaussian profile. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Stationary

theorem differenceWeightedGaussian_integrable (d : ℕ) (s L : ℝ)
    (hs_lower : -2 < s) (hs_upper : s < 0)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real Set.univ = ν.real Set.univ)
    (hμμ : ∀ᵐ p : Rd d × Rd d ∂μ.prod μ, ‖p.1 - p.2‖ ≤ L)
    (hμν : ∀ᵐ p : Rd d × Rd d ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L)
    (hνν : ∀ᵐ p : Rd d × Rd d ∂ν.prod ν, ‖p.1 - p.2‖ ≤ L) :
    IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1) *
      Riesz.Analysis.differenceKernelQuadratic
        (fun a b : Rd d => Real.exp (-(t * ‖a - b‖ ^ 2))) μ ν) (Set.Ioi 0) := by
  have hA := Riesz.Analysis.integrable_negative_gaussian_profile s L hs_lower hs_upper μ μ hμμ
  have hB := Riesz.Analysis.integrable_negative_gaussian_profile s L hs_lower hs_upper μ ν hμν
  have hC := Riesz.Analysis.integrable_negative_gaussian_profile s L hs_lower hs_upper ν ν hνν
  refine ((hA.sub (hB.const_mul 2)).add hC).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [← Riesz.Analysis.gaussian_sub_one_quadratic_eq t ht.le μ ν hmass]
  simp only [Riesz.Analysis.differenceKernelQuadratic, Pi.add_apply, Pi.sub_apply,
    mul_add, mul_sub, mul_left_comm]

theorem signedWeightedGaussian_integrable (d : ℕ) (s : ℝ)
    (hs_lower : -2 < s) (hs_upper : s < 0)
    (η : SignedMeasure (Rd d)) (hmass : η Set.univ = 0) (S : Set (Rd d))
    (hcompact : IsCompact S) (hsupport : η.totalVariation Sᶜ = 0) :
    IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1) *
      Riesz.Analysis.signedKernelQuadratic
        (fun a b : Rd d => Real.exp (-(t * ‖a - b‖ ^ 2))) η) (Set.Ioi 0) := by
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp hcompact.isBounded
  have hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L := fun x hx y hy => by
    simpa only [dist_eq_norm] using hL hx hy
  have hparts : η.toJordanDecomposition.posPart Sᶜ = 0 ∧
      η.toJordanDecomposition.negPart Sᶜ = 0 := by
    simpa only [SignedMeasure.totalVariation, Measure.add_apply, add_eq_zero] using hsupport
  simp_rw [Riesz.Analysis.signed_gaussian_quadratic_eq]
  exact differenceWeightedGaussian_integrable d s L hs_lower hs_upper
    η.toJordanDecomposition.posPart η.toJordanDecomposition.negPart
    (Riesz.Analysis.jordan_masses_eq_of_zero η hmass)
    (Riesz.Analysis.ae_distance_le_of_concentrated _ _ S L hparts.1 hparts.1 hdiam)
    (Riesz.Analysis.ae_distance_le_of_concentrated _ _ S L hparts.1 hparts.2 hdiam)
    (Riesz.Analysis.ae_distance_le_of_concentrated _ _ S L hparts.2 hparts.2 hdiam)

def tupleWeightedGaussian (d m : ℕ) (q : ℝ)
    (p : ℝ × (Fin (m ^ d) → Rd d)) : ℝ :=
  p.1 ^ (-q / 2 - 1) * Riesz.Analysis.signedKernelQuadratic
    (fun a b : Rd d => Real.exp (-p.1 * ‖a - b‖ ^ 2))
      (Riesz.Negative.tupleDiscrepancy d m p.2)

theorem gaussian_background_joint_stronglyMeasurable (d : ℕ)
    (ν : Measure (Rd d)) [SFinite ν] :
    StronglyMeasurable (fun p : ℝ × Rd d =>
      ∫ b, Real.exp (-p.1 * ‖p.2 - b‖ ^ 2) ∂ν) := by
  have h : Continuous (fun p : (ℝ × Rd d) × Rd d =>
      Real.exp (-p.1.1 * ‖p.1.2 - p.2‖ ^ 2)) := by fun_prop
  exact h.stronglyMeasurable.integral_prod_right'

theorem gaussian_pair_scale_stronglyMeasurable (d : ℕ)
    (μ ν : Measure (Rd d)) [SFinite μ] [SFinite ν] :
    StronglyMeasurable (fun t : ℝ =>
      ∫ p : Rd d × Rd d, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂μ.prod ν) := by
  exact (show Continuous (fun p : ℝ × (Rd d × Rd d) =>
    Real.exp (-p.1 * ‖p.2.1 - p.2.2‖ ^ 2)) from by fun_prop).stronglyMeasurable.integral_prod_right'

def tupleGaussianExpression (d m : ℕ) (p : ℝ × (Fin (m ^ d) → Rd d)) : ℝ :=
  tupleGaussianSum d (m ^ d) p.1 p.2 -
    2 * (∑ i, ∫ b, Real.exp (-p.1 * ‖p.2 i - b‖ ^ 2)
      ∂volume.restrict (cube d (m : ℝ))) +
    ∫ ab : Rd d × Rd d, Real.exp (-p.1 * ‖ab.1 - ab.2‖ ^ 2)
      ∂(volume.restrict (cube d (m : ℝ))).prod (volume.restrict (cube d (m : ℝ)))

theorem tupleGaussianExpression_stronglyMeasurable (d m : ℕ) :
    StronglyMeasurable (tupleGaussianExpression d m) := by
  letI := Riesz.Negative.cube_background_isFiniteMeasure d m
  have hA : Continuous (fun p : ℝ × (Fin (m ^ d) → Rd d) =>
      tupleGaussianSum d (m ^ d) p.1 p.2) := by
    unfold tupleGaussianSum
    fun_prop
  have hC : StronglyMeasurable (fun p : ℝ × (Fin (m ^ d) → Rd d) =>
      ∑ i, ∫ b, Real.exp (-p.1 * ‖p.2 i - b‖ ^ 2)
        ∂volume.restrict (cube d (m : ℝ))) :=
    Finset.stronglyMeasurable_fun_sum _ (fun i _ =>
      (gaussian_background_joint_stronglyMeasurable d _).comp_measurable
        (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  exact (hA.stronglyMeasurable.sub (hC.const_mul 2)).add
    ((gaussian_pair_scale_stronglyMeasurable d _ _).comp_measurable measurable_fst)

theorem tupleWeightedGaussian_aestronglyMeasurable (d m : ℕ) (hd : 0 < d) (q : ℝ)
    (Qcell : Measure (Fin (m ^ d) → Rd d)) [IsFiniteMeasure Qcell] :
    AEStronglyMeasurable (tupleWeightedGaussian d m q)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod Qcell) := by
  have h : StronglyMeasurable (fun p : ℝ × (Fin (m ^ d) → Rd d) =>
      p.1 ^ (-q / 2 - 1) * tupleGaussianExpression d m p) :=
    (measurable_fst.pow_const _).stronglyMeasurable.mul
      (tupleGaussianExpression_stronglyMeasurable d m)
  refine h.aestronglyMeasurable.congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)] with p hp
  exact congrArg (fun r : ℝ => p.1 ^ (-q / 2 - 1) * r)
    (tupleGaussian_signedDiscrepancy_eq d m hd p.1 hp.le p.2).symm

theorem tupleWeightedGaussian_integrable_scale (d m : ℕ) (hd : 0 < d)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2) (x : Fin (m ^ d) → Rd d)
    (hx : ∀ i, x i ∈ cube d (m : ℝ)) :
    IntegrableOn (fun t : ℝ => tupleWeightedGaussian d m q (t, x)) (Set.Ioi 0) := by
  obtain ⟨S, hcompact, hsupport⟩ := Riesz.Negative.tupleDiscrepancy_compact_support d m hd x hx
  simpa only [tupleWeightedGaussian, neg_mul] using signedWeightedGaussian_integrable d (-q)
    (neg_lt_neg hq_two) (neg_lt_zero.mpr hq)
    (Riesz.Negative.tupleDiscrepancy d m x) (Riesz.Negative.tupleDiscrepancy_mass_zero d m x)
    S hcompact hsupport

theorem tupleWeightedGaussian_nonneg (d m : ℕ) (q t : ℝ) (ht : 0 < t)
    (x : Fin (m ^ d) → Rd d) : 0 ≤ tupleWeightedGaussian d m q (t, x) := by
  exact mul_nonneg (Real.rpow_nonneg ht.le _)
    (Riesz.Analysis.gaussian_signed_quadratic_nonneg t ht (Riesz.Negative.tupleDiscrepancy d m x))

theorem tupleWeightedGaussian_norm_integral (d m : ℕ) (hd : 0 < d)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2) (x : Fin (m ^ d) → Rd d)
    (hx : ∀ i, x i ∈ cube d (m : ℝ)) :
    (∫ t : ℝ in Set.Ioi 0, ‖tupleWeightedGaussian d m q (t, x)‖) =
      (gamma_s (-q))⁻¹ * Riesz.Analysis.signedDiscrepancyEnergy q
        (Riesz.Negative.tupleDiscrepancy d m x) := by
  have hE : Riesz.Analysis.signedDiscrepancyEnergy q (Riesz.Negative.tupleDiscrepancy d m x) =
      gamma_s (-q) * (∫ t : ℝ in Set.Ioi 0, tupleWeightedGaussian d m q (t, x)) := by
    simpa only [tupleWeightedGaussian, neg_mul] using
      (Riesz.Negative.tuple_signedDiscrepancyEnergy_gaussian d m q hd hq hq_two x hx).1
  rw [hE, ← mul_assoc, inv_mul_cancel₀
    (Riesz.Analysis.gamma_s_pos (-q) (neg_lt_neg hq_two)).ne', one_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
    Real.norm_of_nonneg (tupleWeightedGaussian_nonneg d m q t ht x)

/-- The scale and finite-cell expectation may be exchanged: absolute convergence
follows from the signed finite-volume energy, rather than an assumed grid energy. -/
theorem tupleBalanced_weightedGaussian_integrable (d m : ℕ) (hd : 0 < d)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) :
    Integrable (tupleWeightedGaussian d m q)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod Qcell) := by
  letI : IsProbabilityMeasure Qcell := hQ.1
  apply (integrable_prod_iff' (tupleWeightedGaussian_aestronglyMeasurable d m hd q Qcell)).mpr
  refine ⟨hQ.2.1.mono (fun x hx =>
    tupleWeightedGaussian_integrable_scale d m hd q hq hq_two x hx.2), ?_⟩
  exact ((Riesz.Negative.tupleBalanced_signedDiscrepancyEnergy_integrable
    d m q hd hq hq_two Qcell hQ).const_mul ((gamma_s (-q))⁻¹)).congr
    (hQ.2.1.mono (fun x hx =>
      (tupleWeightedGaussian_norm_integral d m hd q hq hq_two x hx.2).symm))

theorem tupleWeightedGaussian_energy_integral (d m : ℕ) (hd : 0 < d)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2) (x : Fin (m ^ d) → Rd d)
    (hx : ∀ i, x i ∈ cube d (m : ℝ)) :
    (∫ t : ℝ in Set.Ioi 0, tupleWeightedGaussian d m q (t, x)) =
      (gamma_s (-q))⁻¹ * Riesz.Analysis.signedDiscrepancyEnergy q
        (Riesz.Negative.tupleDiscrepancy d m x) := by
  rw [← tupleWeightedGaussian_norm_integral d m hd q hq hq_two x hx]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
    (Real.norm_of_nonneg (tupleWeightedGaussian_nonneg d m q t ht x)).symm

/-- The integrated covariance has exactly the expected finite-cell discrepancy
energy, with the paper's Gamma and volume normalizations. -/
theorem tupleWeightedGaussian_covariance (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (q t : ℝ) (ht : 0 < t) (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) :
    t ^ (-q / 2 - 1) * ((Q d (randomShiftGridLaw d m Qcell) t).toReal + 1 - B d t) =
      ((m : ℝ) ^ d)⁻¹ * ∫ x, tupleWeightedGaussian d m q (t, x) ∂Qcell := by
  simp only [Q_randomShiftGridLaw_signedGaussian_covariance d m hd hm Qcell hQ t ht,
    tupleWeightedGaussian, integral_const_mul]
  exact mul_left_comm _ _ _

theorem Q_randomShiftGridLaw_integrated_signedGaussian (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) :
    gamma_s (-q) * (∫ t : ℝ in Set.Ioi 0, t ^ (-q / 2 - 1) *
      ((Q d (randomShiftGridLaw d m Qcell) t).toReal + 1 - B d t)) =
      ((m : ℝ) ^ d)⁻¹ * ∫ x, Riesz.Analysis.signedDiscrepancyEnergy q
        (Riesz.Negative.tupleDiscrepancy d m x) ∂Qcell := by
  letI : IsProbabilityMeasure Qcell := hQ.1
  rw [integral_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono
    (fun t ht => tupleWeightedGaussian_covariance d m hd hm q t ht Qcell hQ)), integral_const_mul]
  rw [← integral_prod _ (tupleBalanced_weightedGaussian_integrable d m hd q hq hq_two Qcell hQ),
    integral_prod_symm _ (tupleBalanced_weightedGaussian_integrable d m hd q hq hq_two Qcell hQ)]
  rw [integral_congr_ae (hQ.2.1.mono
    (fun x hx => tupleWeightedGaussian_energy_integral d m hd q hq hq_two x hx.2)), integral_const_mul]
  rw [mul_left_comm (gamma_s (-q)) ((m : ℝ) ^ d)⁻¹, ← mul_assoc (gamma_s (-q)),
    mul_inv_cancel₀ (Riesz.Analysis.gamma_s_pos (-q) (neg_lt_neg hq_two)).ne', one_mul]

theorem Q_randomShiftGridLaw_weighted_covariance_integrable (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) :
    IntegrableOn (fun t : ℝ => t ^ (-q / 2 - 1) *
      ((Q d (randomShiftGridLaw d m Qcell) t).toReal + 1 - B d t)) (Set.Ioi 0) := by
  letI : IsProbabilityMeasure Qcell := hQ.1
  exact ((tupleBalanced_weightedGaussian_integrable d m hd q hq hq_two Qcell hQ).integral_prod_left.const_mul
    (((m : ℝ) ^ d)⁻¹)).congr ((ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => (tupleWeightedGaussian_covariance d m hd hm q t ht Qcell hQ).symm))

theorem Q_randomShiftGridLaw_weighted_covariance_lintegral (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-q / 2 - 1)) *
      ENNReal.ofReal ((Q d (randomShiftGridLaw d m Qcell) t).toReal + 1 - B d t)) =
      ENNReal.ofReal (∫ t : ℝ in Set.Ioi 0, t ^ (-q / 2 - 1) *
        ((Q d (randomShiftGridLaw d m Qcell) t).toReal + 1 - B d t)) := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t => t ^ (-q / 2 - 1) *
        ((Q d (randomShiftGridLaw d m Qcell) t).toReal + 1 - B d t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
      mul_nonneg (Real.rpow_nonneg ht.le _)
        (Q_randomShiftGridLaw_covariance_nonneg d m hd hm Qcell hQ t ht)
  rw [ofReal_integral_eq_lintegral_ofReal
    (Q_randomShiftGridLaw_weighted_covariance_integrable d m hd hm q hq hq_two Qcell hQ) hnonneg]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
    (ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)).symm

theorem gaussianRemainder_le_covariance_of_Q_ne_top (d : ℕ) (P : ConfigurationLaw d) (t : ℝ)
    (hQ : Q d P t ≠ ∞) :
    gaussianRemainder d P t ≤ ENNReal.ofReal ((Q d P t).toReal + 1 - B d t) := by
  unfold gaussianRemainder
  conv_lhs => rw [← ENNReal.ofReal_toReal hQ]
  rw [← ENNReal.ofReal_sub _ (le_max_right (B d t - 1) 0)]
  exact ENNReal.ofReal_le_ofReal (by linarith [le_max_left (B d t - 1) 0])

theorem W_randomShiftGridLaw_neg_ne_top (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) :
    W d (-q) (randomShiftGridLaw d m Qcell) ≠ ⊤ := by
  unfold W
  refine EReal.add_ne_top (EReal.coe_ne_top _) (EReal.coe_ennreal_eq_top_iff.not.mpr ?_)
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  have hupper :
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-q / 2 - 1)) *
        gaussianRemainder d (randomShiftGridLaw d m Qcell) t) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-q / 2 - 1)) *
        ENNReal.ofReal ((Q d (randomShiftGridLaw d m Qcell) t).toReal + 1 - B d t) :=
    lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht =>
      mul_le_mul_right (gaussianRemainder_le_covariance_of_Q_ne_top d _ t
        (Q_randomShiftGridLaw_ne_top d m hm Qcell hQ t ht)) _))
  rw [Q_randomShiftGridLaw_weighted_covariance_lintegral d m hd hm q hq hq_two Qcell hQ] at hupper
  exact (hupper.trans_lt ENNReal.ofReal_lt_top).ne

/-- The negative-exponent Euclidean problem has a concrete finite competitor. -/
theorem exists_admissible_finite_energy_neg (d : ℕ) (hd : 0 < d)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2) :
    ∃ P : ConfigurationLaw d, Admissible d P ∧ W d (-q) P ≠ ⊤ := by
  obtain ⟨Pcell, hPcell⟩ := Riesz.Negative.exists_balanced_law d 1 hd Nat.zero_lt_one
  obtain ⟨Qcell, hQcell, _, hgrid⟩ := exists_admissible_grid_law_of_balanced
    d 1 Nat.zero_lt_one Pcell hPcell
  exact ⟨_, hgrid, W_randomShiftGridLaw_neg_ne_top d 1 hd Nat.zero_lt_one q hq hq_two Qcell hQcell⟩

theorem infimumFinite_neg (d : ℕ) (hd : 0 < d)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2) :
    eExtended d (-q) = (e d (-q) : EReal) := by
  obtain ⟨P, hP, hW⟩ := exists_admissible_finite_energy_neg d hd q hq hq_two
  exact infimumFinite_of_competitor d (-q) P hP hW

theorem e_pos_neg (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hq_two : q < 2) :
    0 < e d (-q) := by
  exact e_pos_of_neg_of_finite d (-q) hd (neg_lt_neg hq_two)
    ((neg_lt_zero.mpr hq).trans_le (Nat.cast_nonneg d)) (neg_lt_zero.mpr hq)
    (infimumFinite_neg d (Nat.lt_of_lt_of_le (by decide) hd) q hq hq_two)

/-- Finiteness and both constant signs in the main theorem's negative branch. -/
theorem negative_constant_finiteness_and_sign (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs_lower : -2 < s) (hs_neg : s < 0) :
    eExtended d s = (e d s : EReal) ∧ 0 < e d s ∧ C d s < 0 := by
  have hq_two : -s < 2 := by linarith
  have hfinite : eExtended d s = (e d s : EReal) := by
    simpa only [neg_neg] using infimumFinite_neg d (Nat.lt_of_lt_of_le (by decide) hd)
      (-s) (neg_pos.mpr hs_neg) hq_two
  have hpos : 0 < e d s := by
    simpa only [neg_neg] using e_pos_neg d hd (-s) (neg_pos.mpr hs_neg) hq_two
  exact ⟨hfinite, hpos, mul_neg_of_neg_of_pos hs_neg hpos⟩

end Riesz.Stationary
