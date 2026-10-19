import Riesz.Analysis.DiscrepancyYoung
import Riesz.Stationary.NegativeHeatSpectrum

/-! Angular Fourier energy for finite compact neutral signed inputs. -/

noncomputable section

open MeasureTheory Filter RieszShowcase
open scoped ENNReal ComplexConjugate RealInnerProductSpace

namespace Riesz.Stationary

private abbrev finiteAngularPhase (d : ℕ) (k x : Rd d) : ℂ :=
  Complex.exp ((inner ℝ k x : ℂ) * Complex.I)

private theorem integrable_finiteAngularPhase
    (d : ℕ) (μ : Measure (Rd d)) [IsFiniteMeasure μ] (k : Rd d) :
    Integrable (finiteAngularPhase d k) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (show AEStronglyMeasurable (finiteAngularPhase d k) μ from
      (show Continuous (finiteAngularPhase d k) from by fun_prop).aestronglyMeasurable) ?_
  exact Eventually.of_forall (fun x => by
    simp only [finiteAngularPhase, Complex.norm_exp_ofReal_mul_I, le_refl])

private theorem integral_finiteAngularPhase_eq_charFun
    (d : ℕ) (μ : Measure (Rd d)) (k : Rd d) :
    (∫ x, finiteAngularPhase d k x ∂μ) = charFun μ k := by
  rw [charFun_apply]
  exact integral_congr_ae (Eventually.of_forall (fun x => by
    simp only [finiteAngularPhase, real_inner_comm k x]))

theorem angularPhase_integral_prod_finite
    (d : ℕ) (μ ν : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (k : Rd d) :
    (∫ p : Rd d × Rd d,
      Complex.exp ((inner ℝ k (p.2 - p.1) : ℂ) * Complex.I) ∂μ.prod ν) =
      conj (charFun μ k) * charFun ν k := by
  have hp (p : Rd d × Rd d) : finiteAngularPhase d k (p.2 - p.1) =
      conj (finiteAngularPhase d k p.1) * finiteAngularPhase d k p.2 :=
    angularPhase_pair d k p.1 p.2
  rw [integral_congr_ae (Eventually.of_forall hp),
    integral_prod_mul (fun x => conj (finiteAngularPhase d k x))
      (finiteAngularPhase d k), integral_conj,
    integral_finiteAngularPhase_eq_charFun d μ k,
    integral_finiteAngularPhase_eq_charFun d ν k]

theorem gaussian_pair_charFun_finite
    (d : ℕ) (u : ℝ) (hu : 0 < u)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun k : Rd d => (originalHeatGaussian d u k : ℂ) *
      (conj (charFun μ k) * charFun ν k)) volume ∧
    ((∫ p : Rd d × Rd d, Real.exp (-u * ‖p.1 - p.2‖ ^ 2)
        ∂μ.prod ν : ℝ) : ℂ) =
      ∫ k : Rd d, (originalHeatGaussian d u k : ℂ) *
        (conj (charFun μ k) * charFun ν k) := by
  let F : Rd d → (Rd d × Rd d) → ℂ := fun k p =>
    (originalHeatGaussian d u k : ℂ) * finiteAngularPhase d k (p.2 - p.1)
  have hF : Integrable (Function.uncurry F) (volume.prod (μ.prod ν)) := by
    refine ((integrable_originalHeatGaussian d u hu).comp_fst (μ.prod ν)).mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.comp
        ((continuous_originalHeatGaussian d u).comp continuous_fst)).mul
        (show Continuous (fun q : Rd d × (Rd d × Rd d) =>
          finiteAngularPhase d q.1 (q.2.2 - q.2.1)) from by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall (fun q => by
        simp only [Function.uncurry, F, finiteAngularPhase, norm_mul,
          Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (originalHeatGaussian_nonneg d u hu q.1),
          le_refl])
  have hk (k : Rd d) : (∫ p : Rd d × Rd d, F k p ∂μ.prod ν) =
      (originalHeatGaussian d u k : ℂ) *
        (conj (charFun μ k) * charFun ν k) := by
    rw [integral_const_mul, angularPhase_integral_prod_finite]
  have hp (p : Rd d × Rd d) : (∫ k : Rd d, F k p) =
      (Real.exp (-u * ‖p.1 - p.2‖ ^ 2) : ℂ) := by
    rw [integral_originalHeatGaussian_mul_angularExp d u hu, norm_sub_rev]
  refine ⟨hF.integral_prod_left.congr (Eventually.of_forall hk), ?_⟩
  exact integral_complex_ofReal.symm.trans
    ((integral_congr_ae (Eventually.of_forall hp)).symm.trans
      ((integral_integral_swap (μ := volume) (ν := μ.prod ν) (f := F) hF).symm.trans
        (integral_congr_ae (Eventually.of_forall hk))))

def signedAngularAmplitude (d : ℕ) (η : SignedMeasure (Rd d)) (k : Rd d) : ℂ :=
  ∫ᵛ x, Complex.exp ((inner ℝ k x : ℂ) * Complex.I) ∂<•η

private theorem integrable_angularPhase_signed
    (d : ℕ) (η : SignedMeasure (Rd d)) (k : Rd d) :
    η.Integrable (finiteAngularPhase d k) :=
  integrable_finiteAngularPhase d η.variation k

theorem signedAngularAmplitude_eq_jordan
    (d : ℕ) (η : SignedMeasure (Rd d)) (k : Rd d) :
    signedAngularAmplitude d η k =
      charFun η.toJordanDecomposition.posPart k -
        charFun η.toJordanDecomposition.negPart k := by
  calc
    _ = ∫ᵛ x, finiteAngularPhase d k x ∂<•η.toJordanDecomposition.toSignedMeasure :=
      congrArg (fun ζ : SignedMeasure (Rd d) =>
        ∫ᵛ x, finiteAngularPhase d k x ∂<•ζ)
        (SignedMeasure.toSignedMeasure_toJordanDecomposition η).symm
    _ = (∫ x, finiteAngularPhase d k x ∂η.toJordanDecomposition.posPart) -
        (∫ x, finiteAngularPhase d k x ∂η.toJordanDecomposition.negPart) := by
      simpa only [JordanDecomposition.toSignedMeasure, VectorMeasure.integral_toSignedMeasure]
        using (VectorMeasure.integral_sub_vectorMeasure
          (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip)
          (μ := η.toJordanDecomposition.posPart.toSignedMeasure)
          (ν := η.toJordanDecomposition.negPart.toSignedMeasure)
          (f := finiteAngularPhase d k)
          (integrable_angularPhase_signed d η.toJordanDecomposition.posPart.toSignedMeasure k)
          (integrable_angularPhase_signed d η.toJordanDecomposition.negPart.toSignedMeasure k))
    _ = _ := by rw [integral_finiteAngularPhase_eq_charFun,
      integral_finiteAngularPhase_eq_charFun]

theorem measurable_signedAngularAmplitude (d : ℕ) (η : SignedMeasure (Rd d)) :
    Measurable (signedAngularAmplitude d η) := by
  have heq : signedAngularAmplitude d η = fun k : Rd d =>
      charFun η.toJordanDecomposition.posPart k -
        charFun η.toJordanDecomposition.negPart k :=
    funext (signedAngularAmplitude_eq_jordan d η)
  exact heq.symm ▸ (measurable_charFun.sub measurable_charFun)

theorem signedAngularAmplitude_add
    (d : ℕ) (η ζ : SignedMeasure (Rd d)) (k : Rd d) :
    signedAngularAmplitude d (η + ζ) k =
      signedAngularAmplitude d η k + signedAngularAmplitude d ζ k := by
  exact VectorMeasure.integral_add_vectorMeasure
    (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip)
    (integrable_angularPhase_signed d η k) (integrable_angularPhase_signed d ζ k)

theorem signedAngularAmplitude_sub
    (d : ℕ) (η ζ : SignedMeasure (Rd d)) (k : Rd d) :
    signedAngularAmplitude d (η - ζ) k =
      signedAngularAmplitude d η k - signedAngularAmplitude d ζ k := by
  exact VectorMeasure.integral_sub_vectorMeasure
    (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip)
    (integrable_angularPhase_signed d η k) (integrable_angularPhase_signed d ζ k)

theorem signedAngularAmplitude_smul
    (d : ℕ) (c : ℝ) (η : SignedMeasure (Rd d)) (k : Rd d) :
    signedAngularAmplitude d (c • η) k = c • signedAngularAmplitude d η k := by
  exact VectorMeasure.integral_smul_vectorMeasure
    (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip) (finiteAngularPhase d k) c

theorem signedAngularAmplitude_toSignedMeasure
    (d : ℕ) (μ : Measure (Rd d)) [IsFiniteMeasure μ] (k : Rd d) :
    signedAngularAmplitude d μ.toSignedMeasure k = charFun μ k := by
  rw [signedAngularAmplitude, VectorMeasure.integral_toSignedMeasure,
    integral_finiteAngularPhase_eq_charFun]

theorem signedAngularAmplitude_zero_of_mass_zero
    (d : ℕ) (η : SignedMeasure (Rd d)) (hmass : η Set.univ = 0) :
    signedAngularAmplitude d η 0 = 0 := by
  rw [signedAngularAmplitude_eq_jordan, charFun_zero, charFun_zero,
    Riesz.Analysis.jordan_masses_eq_of_zero η hmass, sub_self]

theorem signedGaussian_angular_fourier
    (d : ℕ) (η : SignedMeasure (Rd d)) (u : ℝ) (hu : 0 < u) :
    Integrable (fun k : Rd d => originalHeatGaussian d u k *
      Complex.normSq (signedAngularAmplitude d η k)) volume ∧
    Riesz.Analysis.signedKernelQuadratic
        (fun x y : Rd d => Real.exp (-u * ‖x-y‖ ^ 2)) η =
      ∫ k : Rd d, originalHeatGaussian d u k *
        Complex.normSq (signedAngularAmplitude d η k) := by
  let μ := η.toJordanDecomposition.posPart
  let ν := η.toJordanDecomposition.negPart
  let C := fun (α β : Measure (Rd d)) (k : Rd d) =>
    (originalHeatGaussian d u k : ℂ) * (conj (charFun α k) * charFun β k)
  have hPP := gaussian_pair_charFun_finite d u hu μ μ
  have hPN := gaussian_pair_charFun_finite d u hu μ ν
  have hNP := gaussian_pair_charFun_finite d u hu ν μ
  have hNN := gaussian_pair_charFun_finite d u hu ν ν
  have hp (k : Rd d) :
      C μ μ k - C μ ν k - C ν μ k + C ν ν k =
        (originalHeatGaussian d u k : ℂ) *
          (Complex.normSq (signedAngularAmplitude d η k) : ℂ) := by
    simp only [C, μ, ν, signedAngularAmplitude_eq_jordan,
      Complex.normSq_eq_conj_mul_self, map_sub]
    ring
  have hC : Integrable (fun k : Rd d => (originalHeatGaussian d u k : ℂ) *
      (Complex.normSq (signedAngularAmplitude d η k) : ℂ)) volume :=
    (((hPP.1.sub hPN.1).sub hNP.1).add hNN.1).congr (Eventually.of_forall hp)
  have hReal : Integrable (fun k : Rd d => originalHeatGaussian d u k *
      Complex.normSq (signedAngularAmplitude d η k)) volume := by
    exact hC.re.congr (Eventually.of_forall (fun k => by
      change (((originalHeatGaussian d u k : ℂ) *
        (Complex.normSq (signedAngularAmplitude d η k) : ℂ)).re) = _
      simp))
  have hsum : (∫ k : Rd d, C μ μ k - C μ ν k - C ν μ k + C ν ν k) =
      (∫ k : Rd d, C μ μ k) - (∫ k : Rd d, C μ ν k) -
        (∫ k : Rd d, C ν μ k) + (∫ k : Rd d, C ν ν k) := by
    rw [integral_add (f := fun k => C μ μ k - C μ ν k - C ν μ k)
        (g := C ν ν) ((hPP.1.sub hPN.1).sub hNP.1) hNN.1,
      integral_sub (f := fun k => C μ μ k - C μ ν k) (g := C ν μ)
        (hPP.1.sub hPN.1) hNP.1,
      integral_sub (f := C μ μ) (g := C μ ν) hPP.1 hPN.1]
  have hcast : (Riesz.Analysis.signedKernelQuadratic
      (fun x y : Rd d => Real.exp (-u * ‖x-y‖ ^ 2)) η : ℂ) =
      (∫ k : Rd d, C μ μ k) - (∫ k : Rd d, C μ ν k) -
        (∫ k : Rd d, C ν μ k) + (∫ k : Rd d, C ν ν k) := by
    simp only [Riesz.Analysis.signedKernelQuadratic, Complex.ofReal_sub,
      Complex.ofReal_add]
    rw [hPP.2, hPN.2, hNP.2, hNN.2]
  have hComplex : (Riesz.Analysis.signedKernelQuadratic
      (fun x y : Rd d => Real.exp (-u * ‖x-y‖ ^ 2)) η : ℂ) =
      ∫ k : Rd d, (originalHeatGaussian d u k : ℂ) *
        (Complex.normSq (signedAngularAmplitude d η k) : ℂ) :=
    hcast.trans (hsum.symm.trans (integral_congr_ae (Eventually.of_forall hp)))
  refine ⟨hReal, ?_⟩
  apply Complex.ofReal_injective
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal] using hComplex

theorem compactSigned_angular_mellin_energy
    (d : ℕ) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (η : SignedMeasure (Rd d)) (hmass : η Set.univ = 0)
    (S : Set (Rd d)) (hS : IsCompact S) (hsupp : η.totalVariation Sᶜ = 0) :
    let J : ℝ≥0∞ := ∫⁻ k : Rd d, fullAngularMellinKernel d (-q) k *
      ENNReal.ofReal (Complex.normSq (signedAngularAmplitude d η k))
    ENNReal.ofReal (Riesz.Analysis.signedDiscrepancyEnergy q η) =
        ENNReal.ofReal (gamma_s (-q)) * J ∧
      J ≠ ∞ ∧
      Riesz.Analysis.signedDiscrepancyEnergy q η = gamma_s (-q) * J.toReal := by
  let τ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let R : Rd d → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Complex.normSq (signedAngularAmplitude d η k))
  let Φ : ℝ → ℝ := fun u => Riesz.Analysis.signedKernelQuadratic
    (fun x y : Rd d => Real.exp (-u * ‖x-y‖ ^ 2)) η
  let w : ℝ → ℝ := fun u => u ^ ((-q) / 2 - 1)
  let J : ℝ≥0∞ := ∫⁻ k : Rd d, fullAngularMellinKernel d (-q) k * R k
  have hgamma : 0 < gamma_s (-q) :=
    Riesz.Analysis.gamma_s_pos (-q) (neg_lt_neg hqTwo)
  have hR : Measurable R :=
    (Complex.continuous_normSq.measurable.comp
      (measurable_signedAngularAmplitude d η)).ennreal_ofReal
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp hS.isBounded
  have hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ L := fun x hx y hy => by
    simpa only [dist_eq_norm] using hL hx hy
  have hprof : Integrable (fun u => w u * Φ u) τ := by
    simpa only [IntegrableOn, τ, w, Φ, neg_mul] using
      Riesz.Analysis.integrable_signed_gaussian_profile (-q) L
        (neg_lt_neg hqTwo) (neg_lt_zero.mpr hq) η hmass S hsupp hdiam
  obtain ⟨hEnergy', hEnergyNonneg⟩ :=
    Riesz.Analysis.signedDiscrepancyEnergy_gaussian_compact q hq hqTwo η hmass S hS hsupp
  have hEnergy : Riesz.Analysis.signedDiscrepancyEnergy q η =
      gamma_s (-q) * ∫ u, w u * Φ u ∂τ := by
    simpa only [τ, w, Φ, neg_mul] using hEnergy'
  have hprofNonneg : 0 ≤ᵐ[τ] (fun u => w u * Φ u) :=
    (ae_restrict_mem measurableSet_Ioi).mono (fun u hu =>
      mul_nonneg (Real.rpow_nonneg hu.le _) (by
        simpa only [Φ, neg_mul] using
          Riesz.Analysis.gaussian_signed_quadratic_nonneg u hu η))
  have hu (u : ℝ) (hu : 0 < u) : ENNReal.ofReal (w u * Φ u) =
      ∫⁻ k : Rd d, angularHeadBaseNN d (-q) (u,k) * R k := by
    obtain ⟨hGaussian, hPhi⟩ := signedGaussian_angular_fourier d η u hu
    have hPhiNN : ENNReal.ofReal (Φ u) =
        ∫⁻ k : Rd d, ENNReal.ofReal (originalHeatGaussian d u k) * R k := by
      dsimp only [Φ]
      rw [hPhi, ofReal_integral_eq_lintegral_ofReal hGaussian
        (Eventually.of_forall (fun k => mul_nonneg
          (originalHeatGaussian_nonneg d u hu k) (Complex.normSq_nonneg _)))]
      exact lintegral_congr_ae (Eventually.of_forall (fun k =>
        ENNReal.ofReal_mul (originalHeatGaussian_nonneg d u hu k)))
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _), hPhiNN,
      ← lintegral_const_mul' (ENNReal.ofReal (w u))
        (fun k : Rd d => ENNReal.ofReal (originalHeatGaussian d u k) * R k)
        ENNReal.ofReal_ne_top]
    exact lintegral_congr_ae (Eventually.of_forall (fun k => by
      simp only [angularHeadBaseNN, w, mul_assoc]))
  have hJoint : Measurable (fun p : ℝ × Rd d =>
      angularHeadBaseNN d (-q) p * R p.2) :=
    (measurable_angularHeadBaseNN d (-q)).mul (hR.comp measurable_snd)
  have hswap : (∫⁻ u, ∫⁻ k : Rd d, angularHeadBaseNN d (-q) (u,k) * R k
        ∂volume ∂τ) =
      ∫⁻ k : Rd d, ∫⁻ u, angularHeadBaseNN d (-q) (u,k) * R k ∂τ :=
    lintegral_lintegral_swap (μ := τ) (ν := (volume : Measure (Rd d)))
      (f := fun u k => angularHeadBaseNN d (-q) (u,k) * R k) hJoint.aemeasurable
  have hinner (k : Rd d) :
      (∫⁻ u, angularHeadBaseNN d (-q) (u,k) * R k ∂τ) =
        fullAngularMellinKernel d (-q) k * R k :=
    lintegral_mul_const' (R k)
      (fun u : ℝ => angularHeadBaseNN d (-q) (u,k)) ENNReal.ofReal_ne_top
  have hNN : ENNReal.ofReal (Riesz.Analysis.signedDiscrepancyEnergy q η) =
      ENNReal.ofReal (gamma_s (-q)) * J := by
    rw [hEnergy, ENNReal.ofReal_mul hgamma.le,
      ofReal_integral_eq_lintegral_ofReal hprof hprofNonneg]
    exact congrArg (ENNReal.ofReal (gamma_s (-q)) * ·)
      ((lintegral_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono
        (fun u hu' => hu u hu'))).trans
          (hswap.trans (lintegral_congr_ae (Eventually.of_forall hinner))))
  have hJfin : J ≠ ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_right
      (hNN.symm.trans_ne ENNReal.ofReal_ne_top)
      (ENNReal.ofReal_ne_zero_iff.mpr hgamma)).ne
  have hReal := congrArg ENNReal.toReal hNN
  refine ⟨hNN, hJfin, ?_⟩
  simpa only [ENNReal.toReal_ofReal hEnergyNonneg, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hgamma.le] using hReal

theorem compactSigned_radial_fourier_energy
    (d : ℕ) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (η : SignedMeasure (Rd d)) (hmass : η Set.univ = 0)
    (S : Set (Rd d)) (hS : IsCompact S) (hsupp : η.totalVariation Sᶜ = 0) :
    let C : ℝ := angularMellinPrefactor d *
      (4 : ℝ) ^ angularMellinOrder d (-q) * Real.Gamma (angularMellinOrder d (-q))
    Integrable (fun k : Rd d => ‖k‖ ^ (-((d : ℝ)+q)) *
      Complex.normSq (signedAngularAmplitude d η k)) volume ∧
    Riesz.Analysis.signedDiscrepancyEnergy q η = gamma_s (-q) * C *
      ∫ k : Rd d, ‖k‖ ^ (-((d : ℝ)+q)) *
        Complex.normSq (signedAngularAmplitude d η k) := by
  let C : ℝ := angularMellinPrefactor d *
    (4 : ℝ) ^ angularMellinOrder d (-q) * Real.Gamma (angularMellinOrder d (-q))
  let f : Rd d → ℝ := fun k => ‖k‖ ^ (-((d : ℝ)+q)) *
    Complex.normSq (signedAngularAmplitude d η k)
  have hsd : -q < (d : ℝ) :=
    (neg_lt_zero.mpr hq).trans_le (Nat.cast_nonneg d)
  have horder : 0 < angularMellinOrder d (-q) :=
    div_pos (sub_pos.mpr hsd) (by norm_num)
  have hC : 0 < C := mul_pos
    (mul_pos (angularMellinPrefactor_pos d) (Real.rpow_pos_of_pos (by norm_num) _))
    (Real.Gamma_pos_of_pos horder)
  have hfm : Measurable f := (measurable_id.norm.pow_const _).mul
    (Complex.continuous_normSq.measurable.comp (measurable_signedAngularAmplitude d η))
  have hfnn (k : Rd d) : 0 ≤ f k :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg k) _) (Complex.normSq_nonneg _)
  obtain ⟨_, hJfin, hEnergy⟩ := compactSigned_angular_mellin_energy
    d q hq hqTwo η hmass S hS hsupp
  have hpoint (k : Rd d) : fullAngularMellinKernel d (-q) k *
        ENNReal.ofReal (Complex.normSq (signedAngularAmplitude d η k)) =
      ENNReal.ofReal C * ENNReal.ofReal (f k) := by
    by_cases hk : k = 0
    · simp only [hk, f, signedAngularAmplitude_zero_of_mass_zero d η hmass,
        Complex.normSq_zero, mul_zero, ENNReal.ofReal_zero]
    · rw [fullAngularMellinKernel_eq_radial d (-q) hsd hk]
      change ENNReal.ofReal (C * ‖k‖ ^ (-((d : ℝ)-(-q)))) *
        ENNReal.ofReal (Complex.normSq (signedAngularAmplitude d η k)) = _
      simp only [sub_neg_eq_add, ENNReal.ofReal_mul hC.le, f,
        ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg k) _), mul_assoc]
  have hJrad : (∫⁻ k : Rd d, fullAngularMellinKernel d (-q) k *
      ENNReal.ofReal (Complex.normSq (signedAngularAmplitude d η k))) =
      ENNReal.ofReal C * ∫⁻ k : Rd d, ENNReal.ofReal (f k) :=
    (lintegral_congr_ae (Eventually.of_forall hpoint)).trans
      (lintegral_const_mul' (ENNReal.ofReal C)
        (fun k : Rd d => ENNReal.ofReal (f k)) ENNReal.ofReal_ne_top)
  have hIfin : (∫⁻ k : Rd d, ENNReal.ofReal (f k)) ≠ ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_right (hJrad.symm.trans_ne hJfin)
      (ENNReal.ofReal_ne_zero_iff.mpr hC)).ne
  have hfInt : Integrable f volume :=
    (lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable
      (Eventually.of_forall hfnn)).mp hIfin
  have hOfIntegral := ofReal_integral_eq_lintegral_ofReal hfInt
    (Eventually.of_forall hfnn)
  rw [hJrad, ← hOfIntegral, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC.le,
    ENNReal.toReal_ofReal (integral_nonneg hfnn)] at hEnergy
  exact ⟨hfInt, by simpa only [C, f, mul_assoc] using hEnergy⟩

theorem signedAngularAmplitude_three_finite
    (d : ℕ) (μ ν κ : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure κ]
    (c : ℝ) (k : Rd d) :
    signedAngularAmplitude d (μ.toSignedMeasure - ν.toSignedMeasure -
      c • κ.toSignedMeasure) k =
      charFun μ k - charFun ν k - c • charFun κ k := by
  rw [signedAngularAmplitude_sub, signedAngularAmplitude_sub,
    signedAngularAmplitude_smul, signedAngularAmplitude_toSignedMeasure,
    signedAngularAmplitude_toSignedMeasure, signedAngularAmplitude_toSignedMeasure]

end Riesz.Stationary
