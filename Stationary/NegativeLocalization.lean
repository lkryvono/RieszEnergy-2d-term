import Riesz.Stationary.NeutralizedFourierBounds
import Riesz.Stationary.NegativeCompactTestVariance
import Riesz.Stationary.CompactSignedFourier
import Riesz.Configuration.Compactness
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-! Localization identities, finite-energy bounds and limits for the original stationary law. -/

noncomputable section
open MeasureTheory Filter RieszShowcase Riesz.Configuration
open scoped ENNReal Topology ComplexConjugate CompactlySupported RealInnerProductSpace ContDiff

namespace Riesz.Stationary

theorem measurable_neutralizedFourierF
    (d : ℕ) (q : ℝ) (χ h : C_c(Rd d, ℝ)) :
    Measurable (neutralizedFourierF d q χ h) := by
  have hZ : Measurable (fun p : Rd d × Rd d =>
      neutralizedAngularAmplitude d χ h p.1 p.2) :=
    ((measurable_compactAngularAmplitude d χ).comp
      (measurable_snd.sub measurable_fst)).sub
      (((measurable_compactAngularAmplitude d χ).comp measurable_fst.neg).mul
        ((measurable_compactAngularAmplitude d h).comp measurable_snd))
  have hm : Measurable (fun p : Rd d × Rd d =>
      neutralizedFourierProfile d q χ h p.1 p.2) :=
    (measurable_snd.norm.pow_const _).mul
      (Complex.continuous_normSq.measurable.comp hZ)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

private def negativeR1RadialC (d : ℕ) (q : ℝ) : ℝ :=
  angularMellinPrefactor d * (4 : ℝ)^angularMellinOrder d (-q) *
    Real.Gamma (angularMellinOrder d (-q))

private def negativeR1Kappa (d : ℕ) (q : ℝ) : ℝ :=
  gamma_s (-q) * (2*Real.pi)^d * negativeR1RadialC d q

private theorem negativeR1RadialC_pos (d : ℕ) (q : ℝ) (hq : 0 < q) :
    0 < negativeR1RadialC d q := by
  have ho : 0 < angularMellinOrder d (-q) := div_pos
    (sub_pos.mpr ((neg_lt_zero.mpr hq).trans_le (Nat.cast_nonneg d))) (by norm_num)
  exact mul_pos (mul_pos (angularMellinPrefactor_pos d)
    (Real.rpow_pos_of_pos (by norm_num) _)) (Real.Gamma_pos_of_pos ho)

private theorem negativeR1Kappa_pos
    (d : ℕ) (q : ℝ) (hq : 0 < q) (hs : -2 < -q) :
    0 < negativeR1Kappa d q :=
  mul_pos (mul_pos (Riesz.Analysis.gamma_s_pos (-q) hs)
    (pow_pos (by positivity) d)) (negativeR1RadialC_pos d q hq)

private theorem negativeR1Kernel_radial_ae
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hs : -2 < -q)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤) :
    negativeAngularEnergyKernel d (-q) =ᵐ[
      originalAngularSpectrumGeneral d (-q) hs P hP hW]
      (fun k => ENNReal.ofReal (negativeR1Kappa d q) *
        ENNReal.ofReal (‖k‖^(-((d : ℝ)+q)))) := by
  have hC := (negativeR1RadialC_pos d q hq).le
  have hγ := (Riesz.Analysis.gamma_s_pos (-q) hs).le
  have hA : 0 ≤ (2*Real.pi)^d := (pow_pos (by positivity) d).le
  filter_upwards [ae_ne_zero_originalAngularSpectrumGeneral
    d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW] with k hk
  rw [negativeAngularEnergyKernel,
    fullAngularMellinKernel_eq_radial d (-q)
      ((neg_lt_zero.mpr hq).trans_le (Nat.cast_nonneg d)) hk]
  simp only [sub_neg_eq_add]
  change (ENNReal.ofReal (gamma_s (-q)) * ENNReal.ofReal ((2*Real.pi)^d)) *
        ENNReal.ofReal (negativeR1RadialC d q * ‖k‖^(-((d : ℝ)+q))) =
    ENNReal.ofReal ((gamma_s (-q)*(2*Real.pi)^d)*negativeR1RadialC d q) *
      ENNReal.ofReal (‖k‖^(-((d : ℝ)+q)))
  rw [ENNReal.ofReal_mul hC,
    ENNReal.ofReal_mul (mul_nonneg hγ hA), ENNReal.ofReal_mul hγ]
  ac_rfl

private theorem negativeR1Weighted_ae_ne_zero
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hs : -2 < -q)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤) :
    ∀ᵐ k ∂(negativeAngularWeightedMeasure
      d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW : Measure (Rd d)), k ≠ 0 := by
  exact (withDensity_absolutelyContinuous
      (originalAngularSpectrumGeneral d (-q) hs P hP hW)
      (negativeAngularEnergyKernel d (-q))).ae_le
    (ae_ne_zero_originalAngularSpectrumGeneral
      d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW)

private theorem negativeR1Weighted_radial_lintegral
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hs : -2 < -q)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (L : ℝ) (hL : 0 < L) (f : Rd d → ℝ) (hf : Measurable f) :
    (∫⁻ k, ENNReal.ofReal (‖L • k‖^((d : ℝ)+q)*f k)
      ∂(negativeAngularWeightedMeasure
        d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW : Measure (Rd d))) =
      (ENNReal.ofReal (negativeR1Kappa d q)*ENNReal.ofReal (L^((d : ℝ)+q))) *
        (∫⁻ k, ENNReal.ofReal (f k)
          ∂originalAngularSpectrumGeneral d (-q) hs P hP hW) := by
  let p : ℝ := (d : ℝ)+q
  let ρ := originalAngularSpectrumGeneral d (-q) hs P hP hW
  have hm : Measurable (fun k : Rd d => ENNReal.ofReal (‖L • k‖^p*f k)) :=
    (((measurable_const_smul L).norm.pow_const p).mul hf).ennreal_ofReal
  change (∫⁻ k, ENNReal.ofReal (‖L • k‖^p*f k)
    ∂ρ.withDensity (negativeAngularEnergyKernel d (-q))) = _
  rw [lintegral_withDensity_eq_lintegral_mul ρ
    (measurable_negativeAngularEnergyKernel d (-q)) hm]
  refine (lintegral_congr_ae ?_).trans
    (lintegral_const_mul'
      (ENNReal.ofReal (negativeR1Kappa d q)*ENNReal.ofReal (L^p))
      (fun k : Rd d => ENNReal.ofReal (f k))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
  filter_upwards [negativeR1Kernel_radial_ae d hd q hq hs P hP hW,
    ae_ne_zero_originalAngularSpectrumGeneral
      d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW] with k hJ hk
  change negativeAngularEnergyKernel d (-q) k =
    ENNReal.ofReal (negativeR1Kappa d q) * ENNReal.ofReal (‖k‖^(-p)) at hJ
  have hr : 0 < ‖k‖ := norm_pos_iff.mpr hk
  have hnorm : ‖L • k‖ = L*‖k‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  have hcancel : ENNReal.ofReal (‖k‖^(-p))*ENNReal.ofReal (‖k‖^p) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _),
      ← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one]
  change negativeAngularEnergyKernel d (-q) k *
    ENNReal.ofReal (‖L • k‖^p*f k) = _
  rw [hJ, hnorm, Real.mul_rpow hL.le hr.le,
    ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hL.le _)
      (Real.rpow_nonneg hr.le _)),
    ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
  calc
    _ = (ENNReal.ofReal (negativeR1Kappa d q)*ENNReal.ofReal (L^p))*
        ((ENNReal.ofReal (‖k‖^(-p))*ENNReal.ofReal (‖k‖^p))*ENNReal.ofReal (f k)) := by
      ac_rfl
    _ = _ := by rw [hcancel, one_mul]

theorem negativeWeighted_neutralizedF_integrable_and_tendsto
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hs : -2 < -q)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (χ h : C_c(Rd d, ℝ)) (hχsm : ContDiff ℝ ∞ χ) (hhsm : ContDiff ℝ ∞ h)
    (hh : (∫ x : Rd d, h x) = 1)
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n) (hLinf : Tendsto L atTop atTop) :
    let ν : Measure (Rd d) := negativeAngularWeightedMeasure
      d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
    let R : ℕ → Rd d → ℝ := fun n k =>
      ‖-(L n • k)‖^((d : ℝ)+q)*neutralizedFourierF d q χ h (-(L n • k))
    (∀ n, Integrable (R n) ν ∧ (∫⁻ k, ENNReal.ofReal (R n k) ∂ν) ≠ ⊤) ∧
    Tendsto (fun n => ∫ k, R n k ∂ν) atTop
      (𝓝 (((2*Real.pi)^d*(∫ x : Rd d, (χ x)^2))*(W d (-q) P).toReal)) := by
  dsimp only
  let ν : Measure (Rd d) := negativeAngularWeightedMeasure
    d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
  let R : ℕ → Rd d → ℝ := fun n k =>
    ‖-(L n • k)‖^((d : ℝ)+q)*neutralizedFourierF d q χ h (-(L n • k))
  letI : IsFiniteMeasure ν := inferInstance
  have hd' : 1 ≤ d := le_trans (by norm_num) hd
  have hqTwo : q < 2 := by linarith
  obtain ⟨C, hC, hbound, hsharp⟩ := neutralizedFourierF_scaled_bound_and_sharp_limit
    d hd' q hq hqTwo χ h hχsm hhsm hh
  have hRm (n : ℕ) : Measurable (R n) :=
    (((measurable_const_smul (L n)).neg.norm.pow_const _).mul
      ((measurable_neutralizedFourierF d q χ h).comp
        (measurable_const_smul (L n)).neg))
  have hR0 (n : ℕ) (k : Rd d) : 0 ≤ R n k := mul_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _)
    (neutralizedFourierProfile_integrable d hd' q hq hqTwo χ h hh (-(L n • k))).2.2.2
  have hRInt (n : ℕ) : Integrable (R n) ν :=
    (integrable_const C).mono' (hRm n).aestronglyMeasurable
      (Eventually.of_forall (fun k => by
        rw [Real.norm_of_nonneg (hR0 n k)]
        exact hbound (-(L n • k))))
  refine ⟨fun n => ⟨hRInt n,
    (lintegral_ofReal_ne_top_iff_integrable (hRm n).aestronglyMeasurable
      (Eventually.of_forall (hR0 n))).2 (hRInt n)⟩, ?_⟩
  have hpoint : ∀ᵐ k ∂ν, Tendsto (fun n => R n k) atTop
      (𝓝 ((2*Real.pi)^d*(∫ x : Rd d, (χ x)^2))) := by
    filter_upwards [negativeR1Weighted_ae_ne_zero d hd q hq hs P hP hW] with k hk
    have hnorm : Tendsto (fun n => ‖-(L n • k)‖) atTop atTop :=
      Filter.Tendsto.congr' (Eventually.of_forall (fun n => by
        simp only [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (hL n)]))
        (hLinf.atTop_mul_const (norm_pos_iff.mpr hk))
    exact hsharp (fun n => -(L n • k)) hnorm
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := ν) (F := R)
    (f := fun _ : Rd d => (2*Real.pi)^d*(∫ x : Rd d, (χ x)^2))
    (fun _ : Rd d => C) (fun n => (hRm n).aestronglyMeasurable)
    (integrable_const C) (fun n => Eventually.of_forall (fun k => by
      rw [Real.norm_of_nonneg (hR0 n k)]
      exact hbound (-(L n • k)))) hpoint
  simpa only [ν, integral_const, smul_eq_mul,
    real_mass_negativeAngularWeightedMeasure d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW,
    mul_comm] using hlim

private theorem negativeR1_scaled_density_control
    (d : ℕ) (q : ℝ) (hq : 0 < q) (hs : -2 < -q)
    (χ : C_c(Rd d, ℝ)) (hχsm : ContDiff ℝ ∞ χ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ y : Rd d, ‖y‖^((d : ℝ)+q)*Complex.normSq (compactAngularAmplitude d χ y) ≤ C) ∧
      ∀ y : ℕ → Rd d, Tendsto (fun n => ‖y n‖) atTop atTop →
        Tendsto (fun n => ‖y n‖^((d : ℝ)+q)*
          Complex.normSq (compactAngularAmplitude d χ (y n))) atTop (𝓝 0) := by
  let p : ℝ := (d : ℝ)+q
  let m : ℝ := ((2*d+2 : ℕ) : ℝ)
  have hp : 0 ≤ p := add_nonneg (Nat.cast_nonneg d) hq.le
  have hpm : p < m := by
    dsimp only [p, m]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) d]
  obtain ⟨C, hC, hdecay⟩ := compactSmoothWindow_angular_density_decay d χ hχsm
  have hbound (y : Rd d) : ‖y‖^p*Complex.normSq (compactAngularAmplitude d χ y) ≤
      C*(1+‖y‖)^(p-m) := by
    calc
      _ ≤ ‖y‖^p*(C*(1+‖y‖)^(-m)) :=
        mul_le_mul_of_nonneg_left (hdecay y) (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ (1+‖y‖)^p*(C*(1+‖y‖)^(-m)) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (norm_nonneg _) (by linarith) hp)
          (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))
      _ = C*(1+‖y‖)^(p-m) := by
        conv_rhs => rw [show p-m = p+(-m) by ring, Real.rpow_add (by positivity)]
        ring
  refine ⟨C, hC, fun y => ?_, fun y hy => ?_⟩
  · have hpow : (1+‖y‖)^(p-m) ≤ 1 := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
        (show 1 ≤ 1+‖y‖ by linarith [norm_nonneg y]) (sub_nonpos.mpr hpm.le)
    exact (hbound y).trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow hC.le)
  · have hlarge : Tendsto (fun n => 1+‖y n‖) atTop atTop :=
      tendsto_atTop_mono (fun n => by linarith) hy
    have hzero : Tendsto (fun n => C*(1+‖y n‖)^(p-m)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, show p-m = -(m-p) by ring, mul_zero] using
        ((tendsto_rpow_neg_atTop (sub_pos.mpr hpm)).comp hlarge).const_mul C
    exact squeeze_zero (fun n => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Complex.normSq_nonneg _)) (fun n => hbound (y n)) hzero

theorem negativeWeighted_scaled_density_integrable_and_tendsto
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hs : -2 < -q)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχsm : ContDiff ℝ ∞ χ)
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n) (hLinf : Tendsto L atTop atTop) :
    let ν : Measure (Rd d) := negativeAngularWeightedMeasure
      d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
    let R : ℕ → Rd d → ℝ := fun n k =>
      ‖L n • k‖^((d : ℝ)+q)*Complex.normSq (compactAngularAmplitude d χ (L n • k))
    (∀ n, Integrable (R n) ν ∧ (∫⁻ k, ENNReal.ofReal (R n k) ∂ν) ≠ ⊤) ∧
    Tendsto (fun n => ∫ k, R n k ∂ν) atTop (𝓝 0) := by
  dsimp only
  let ν : Measure (Rd d) := negativeAngularWeightedMeasure
    d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
  let R : ℕ → Rd d → ℝ := fun n k =>
    ‖L n • k‖^((d : ℝ)+q)*Complex.normSq (compactAngularAmplitude d χ (L n • k))
  letI : IsFiniteMeasure ν := inferInstance
  obtain ⟨C, hC, hbound, hzero⟩ := negativeR1_scaled_density_control d q hq hs χ hχsm
  have hRm (n : ℕ) : Measurable (R n) :=
    (((measurable_const_smul (L n)).norm.pow_const _).mul
      (Complex.continuous_normSq.measurable.comp
        ((measurable_compactAngularAmplitude d χ).comp (measurable_const_smul (L n)))))
  have hR0 (n : ℕ) (k : Rd d) : 0 ≤ R n k := mul_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _) (Complex.normSq_nonneg _)
  have hRInt (n : ℕ) : Integrable (R n) ν :=
    (integrable_const C).mono' (hRm n).aestronglyMeasurable
      (Eventually.of_forall (fun k => by
        rw [Real.norm_of_nonneg (hR0 n k)]
        exact hbound (L n • k)))
  refine ⟨fun n => ⟨hRInt n,
    (lintegral_ofReal_ne_top_iff_integrable (hRm n).aestronglyMeasurable
      (Eventually.of_forall (hR0 n))).2 (hRInt n)⟩, ?_⟩
  have hpoint : ∀ᵐ k ∂ν, Tendsto (fun n => R n k) atTop (𝓝 0) := by
    filter_upwards [negativeR1Weighted_ae_ne_zero d hd q hq hs P hP hW] with k hk
    have hnorm : Tendsto (fun n => ‖L n • k‖) atTop atTop :=
      Filter.Tendsto.congr' (Eventually.of_forall (fun n => by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (hL n)]))
        (hLinf.atTop_mul_const (norm_pos_iff.mpr hk))
    exact hzero (fun n => L n • k) hnorm
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (μ := ν) (F := R) (f := fun _ : Rd d => (0 : ℝ)) (fun _ : Rd d => C)
    (fun n => (hRm n).aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall (fun k => by
      rw [Real.norm_of_nonneg (hR0 n k)]
      exact hbound (L n • k))) hpoint

private def negativeR1Phase (d : ℕ) (v x : Rd d) : ℂ :=
  Complex.exp ((inner ℝ v x : ℂ) * Complex.I)

@[fun_prop] private theorem continuous_negativeR1Phase
    (d : ℕ) (v : Rd d) : Continuous (negativeR1Phase d v) := by
  unfold negativeR1Phase
  fun_prop

private def negativeR1CompactTest
    (d : ℕ) (χ h : C_c(Rd d, ℝ)) (v : Rd d) : C_c(Rd d, ℂ) :=
  ⟨⟨fun x => (χ x : ℂ) *
      (negativeR1Phase d v x - compactAngularAmplitude d h v), by fun_prop⟩,
    (χ.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) rfl).mul_right⟩

private def negativeR1MassDiscrepancy
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (η : CountingConfiguration d) : ℝ :=
  (∫ x, χ x ∂η.val) - ∫ x, χ x ∂volume

private def negativeR1NeutralSigned
    (d : ℕ) (χ h : C_c(Rd d, ℝ)) (η : CountingConfiguration d) :
    SignedMeasure (Rd d) :=
  (cutoffMeasure d η.val χ : Measure (Rd d)).toSignedMeasure -
    (cutoffMeasure d volume χ : Measure (Rd d)).toSignedMeasure -
    negativeR1MassDiscrepancy d χ η •
      (cutoffMeasure d volume h : Measure (Rd d)).toSignedMeasure

private theorem negativeR1_cutoff_charFun
    (d : ℕ) (μ : Measure (Rd d)) [IsFiniteMeasureOnCompacts μ]
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (v : Rd d) :
    charFun (cutoffMeasure d μ χ : Measure (Rd d)) v =
      ∫ x, (χ x : ℂ) * negativeR1Phase d v x ∂μ := by
  rw [charFun_apply]
  change (∫ x, Complex.exp ((inner ℝ x v : ℂ) * Complex.I)
    ∂μ.withDensity (fun y => ENNReal.ofReal (χ y))) = _
  rw [integral_withDensity_eq_integral_toReal_smul (μ := μ)
    (f := fun y : Rd d => ENNReal.ofReal (χ y))
    χ.continuous.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))
    (fun x : Rd d => Complex.exp ((inner ℝ x v : ℂ) * Complex.I))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    simp only [ENNReal.toReal_ofReal (hχ x), Complex.real_smul,
      negativeR1Phase, real_inner_comm x v])

private theorem negativeR1_cutoff_mass
    (d : ℕ) (μ : Measure (Rd d)) [IsFiniteMeasureOnCompacts μ]
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) :
    (cutoffMeasure d μ χ : Measure (Rd d)).real Set.univ = ∫ x, χ x ∂μ := by
  simpa only [integral_const, smul_eq_mul, mul_one] using
    (integral_cutoffMeasure d μ χ hχ (fun _ => (1 : ℝ)))

private theorem negativeR1NeutralSigned_mass_zero
    (d : ℕ) (χ h : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) (hh : ∀ x, 0 ≤ h x)
    (hhmass : (∫ x : Rd d, h x) = 1) (η : CountingConfiguration d) :
    negativeR1NeutralSigned d χ h η Set.univ = 0 := by
  simp only [negativeR1NeutralSigned, _root_.sub_apply, _root_.smul_apply,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    negativeR1_cutoff_mass d η.val χ hχ,
    negativeR1_cutoff_mass d volume χ hχ,
    negativeR1_cutoff_mass d volume h hh, hhmass,
    negativeR1MassDiscrepancy, smul_eq_mul, mul_one, sub_self]

private theorem negativeR1_cutoff_concentrated
    (d : ℕ) (μ : Measure (Rd d)) [IsFiniteMeasureOnCompacts μ]
    (χ : C_c(Rd d, ℝ)) (S : Set (Rd d)) (hS : MeasurableSet S)
    (hχS : tsupport χ ⊆ S) :
    (cutoffMeasure d μ χ : Measure (Rd d)) Sᶜ = 0 := by
  change μ.withDensity (fun x => ENNReal.ofReal (χ x)) Sᶜ = 0
  rw [withDensity_apply _ hS.compl]
  calc
    (∫⁻ x in Sᶜ, ENNReal.ofReal (χ x) ∂μ) = ∫⁻ x in Sᶜ, 0 ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hS.compl] with x hx
      have hx' : x ∉ tsupport χ := fun hxt => hx (hχS hxt)
      simp only [image_eq_zero_of_notMem_tsupport hx', ENNReal.ofReal_zero]
    _ = 0 := lintegral_zero

private theorem negativeR1NeutralSigned_compact_support
    (d : ℕ) (χ h : C_c(Rd d, ℝ)) (η : CountingConfiguration d) :
    (negativeR1NeutralSigned d χ h η).totalVariation
      (tsupport χ ∪ tsupport h)ᶜ = 0 := by
  let S : Set (Rd d) := tsupport χ ∪ tsupport h
  have hS : IsCompact S := χ.hasCompactSupport.union h.hasCompactSupport
  have hμ := negativeR1_cutoff_concentrated d η.val χ S hS.measurableSet
    Set.subset_union_left
  have hν := negativeR1_cutoff_concentrated d volume χ S hS.measurableSet
    Set.subset_union_left
  have hκ := negativeR1_cutoff_concentrated d volume h S hS.measurableSet
    Set.subset_union_right
  apply Riesz.Analysis.totalVariation_null_of_subsets _ Sᶜ hS.measurableSet.compl
  intro E hE
  simp [negativeR1NeutralSigned, _root_.sub_apply, _root_.smul_apply,
    Measure.toSignedMeasure_apply, measureReal_def,
    measure_mono_null hE hμ, measure_mono_null hE hν, measure_mono_null hE hκ]

private theorem negativeR1CompactTest_discrepancy
    (d : ℕ) (χ h : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (η : CountingConfiguration d) (v : Rd d) :
    negativeCompactTestDiscrepancy d (negativeR1CompactTest d χ h v) η =
      charFun (cutoffMeasure d η.val χ : Measure (Rd d)) v -
        charFun (cutoffMeasure d volume χ : Measure (Rd d)) v -
        (negativeR1MassDiscrepancy d χ η : ℂ) * compactAngularAmplitude d h v := by
  have hμ (μ : Measure (Rd d)) [IsFiniteMeasureOnCompacts μ] :
      (∫ x, negativeR1CompactTest d χ h v x ∂μ) =
        charFun (cutoffMeasure d μ χ : Measure (Rd d)) v -
          ((∫ x, χ x ∂μ : ℝ) : ℂ) * compactAngularAmplitude d h v := by
    have hphase : Integrable (fun x : Rd d => (χ x : ℂ)*negativeR1Phase d v x) μ :=
      (show Continuous _ from by fun_prop).integrable_of_hasCompactSupport
        (χ.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) rfl).mul_right
    calc
      _ = ∫ x, ((χ x : ℂ)*negativeR1Phase d v x -
          (χ x : ℂ)*compactAngularAmplitude d h v) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          change (χ x : ℂ)*(_-_) = _
          ring)
      _ = _ := by
        have hc : Integrable (fun x : Rd d =>
            (χ x : ℂ)*compactAngularAmplitude d h v) μ := χ.integrable.ofReal.mul_const _
        rw [integral_sub hphase hc,
          ← negativeR1_cutoff_charFun d μ χ hχ v,
          integral_mul_const, integral_complex_ofReal]
  rw [negativeCompactTestDiscrepancy, hμ η.val, hμ volume]
  simp only [negativeR1MassDiscrepancy, Complex.ofReal_sub]
  ring

private theorem negativeR1NeutralSigned_amplitude
    (d : ℕ) (χ h : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) (hh : ∀ x, 0 ≤ h x)
    (η : CountingConfiguration d) (v : Rd d) :
    signedAngularAmplitude d (negativeR1NeutralSigned d χ h η) v =
      negativeCompactTestDiscrepancy d (negativeR1CompactTest d χ h v) η := by
  rw [negativeR1CompactTest_discrepancy d χ h hχ η v]
  dsimp only [negativeR1NeutralSigned]
  rw [signedAngularAmplitude_three_finite,
    negativeR1_cutoff_charFun d volume h hh v]
  rfl

private theorem negativeR1CompactTest_amplitude
    (d : ℕ) (χ h : C_c(Rd d, ℝ)) (v k : Rd d) :
    negativeCompactAngularAmplitude d (negativeR1CompactTest d χ h v) k =
      compactAngularAmplitude d χ (k+v) -
        compactAngularAmplitude d h v * compactAngularAmplitude d χ k := by
  have hphase (w : Rd d) :
      Integrable (fun x : Rd d => (χ x : ℂ)*negativeR1Phase d w x) volume :=
    (show Continuous _ from by fun_prop).integrable_of_hasCompactSupport
      (χ.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) rfl).mul_right
  have hp (x : Rd d) : negativeR1Phase d v x * negativeR1Phase d k x =
      negativeR1Phase d (k+v) x := by
    dsimp only [negativeR1Phase]
    rw [← Complex.exp_add]
    congr 1
    simp only [inner_add_left, Complex.ofReal_add]
    ring
  calc
    _ = ∫ x : Rd d,
        ((χ x : ℂ)*negativeR1Phase d (k+v) x -
          compactAngularAmplitude d h v*((χ x : ℂ)*negativeR1Phase d k x)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        change ((χ x : ℂ)*(negativeR1Phase d v x -
          compactAngularAmplitude d h v))*negativeR1Phase d k x = _
        calc
          _ = (χ x : ℂ)*(negativeR1Phase d v x*negativeR1Phase d k x) -
              compactAngularAmplitude d h v*((χ x : ℂ)*negativeR1Phase d k x) := by ring
          _ = _ := by rw [hp x])
    _ = _ := by
      rw [integral_sub (hphase (k+v)) ((hphase k).const_mul _), integral_const_mul]
      rfl

private theorem negativeR1_measurable_complex_countingIntegral
    (d : ℕ) (f : C_c(Rd d, ℂ)) :
    Measurable (fun η : CountingConfiguration d => ∫ x, f x ∂η.val) := by
  let fr : C_c(Rd d, ℝ) := ⟨⟨fun x => (f x).re, by fun_prop⟩,
    f.hasCompactSupport.comp_left (g := Complex.re) rfl⟩
  let fi : C_c(Rd d, ℝ) := ⟨⟨fun x => (f x).im, by fun_prop⟩,
    f.hasCompactSupport.comp_left (g := Complex.im) rfl⟩
  have hr := (Complex.continuous_ofReal.measurable.comp
    (measurable_countingIntegral d fr))
  have hi := (Complex.continuous_ofReal.measurable.comp
    (measurable_countingIntegral d fi)).mul_const Complex.I
  have heq : (fun η : CountingConfiguration d => ∫ x, f x ∂η.val) =
      (fun η : CountingConfiguration d => ((∫ x, fr x ∂η.val : ℝ) : ℂ) +
        ((∫ x, fi x ∂η.val : ℝ) : ℂ)*Complex.I) := by
    funext η
    rw [show (∫ x, fr x ∂η.val) = (∫ x, f x ∂η.val).re from
        integral_re f.integrable,
      show (∫ x, fi x ∂η.val) = (∫ x, f x ∂η.val).im from
        integral_im f.integrable]
    exact (Complex.re_add_im _).symm
  rw [heq]
  exact hr.add hi

private theorem negativeR1CompactTest_joint_measurable
    (d : ℕ) (χ h : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) (hh : ∀ x, 0 ≤ h x) :
    Measurable (fun p : Rd d × CountingConfiguration d =>
      negativeCompactTestDiscrepancy d (negativeR1CompactTest d χ h p.1) p.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun (v : Rd d) (η : CountingConfiguration d) =>
      negativeCompactTestDiscrepancy d (negativeR1CompactTest d χ h v) η)
  · intro η
    have heq (v : Rd d) := negativeR1CompactTest_discrepancy d χ h hχ η v
    have hc : Continuous (fun v : Rd d =>
        charFun (cutoffMeasure d η.val χ : Measure (Rd d)) v -
          charFun (cutoffMeasure d volume χ : Measure (Rd d)) v -
          (negativeR1MassDiscrepancy d χ η : ℂ) *
            charFun (cutoffMeasure d volume h : Measure (Rd d)) v) :=
      (continuous_charFun.sub continuous_charFun).sub
        (continuous_const.mul continuous_charFun)
    convert hc using 1
    funext v
    rw [heq v, negativeR1_cutoff_charFun d volume h hh v]
    rfl
  · intro v
    exact (negativeR1_measurable_complex_countingIntegral d
      (negativeR1CompactTest d χ h v)).sub measurable_const

private theorem negativeR1_radial_nn_Tonelli
    (d : ℕ) (s : ℝ) (hs : -2 < s)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ h : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) (hh : ∀ x, 0 ≤ h x) (p : ℝ) :
    (∫⁻ η : CountingConfiguration d, ∫⁻ v : Rd d,
      ENNReal.ofReal (‖v‖^(-p)) * ENNReal.ofReal (Complex.normSq
        (negativeCompactTestDiscrepancy d (negativeR1CompactTest d χ h v) η))
        ∂volume ∂countingLawOfSimple d P) =
      ∫⁻ k, ∫⁻ v : Rd d,
        ENNReal.ofReal (‖v‖^(-p)) * ENNReal.ofReal (Complex.normSq
          (compactAngularAmplitude d χ (k+v) -
            compactAngularAmplitude d h v * compactAngularAmplitude d χ k))
          ∂volume ∂originalAngularSpectrumGeneral d s hs P hP hW := by
  let Qc := countingLawOfSimple d P
  let ρ := originalAngularSpectrumGeneral d s hs P hP hW
  letI : IsProbabilityMeasure P := hP.1
  letI : IsProbabilityMeasure Qc := inferInstance
  have hm : Measurable (fun z : Rd d × CountingConfiguration d =>
      ENNReal.ofReal (‖z.1‖^(-p)) * ENNReal.ofReal (Complex.normSq
        (negativeCompactTestDiscrepancy d (negativeR1CompactTest d χ h z.1) z.2))) :=
    (measurable_fst.norm.pow_const _).ennreal_ofReal.mul
      (Complex.continuous_normSq.measurable.comp
        (negativeR1CompactTest_joint_measurable d χ h hχ hh)).ennreal_ofReal
  have hn : Measurable (fun z : Rd d × Rd d =>
      ENNReal.ofReal (‖z.1‖^(-p)) * ENNReal.ofReal (Complex.normSq
        (compactAngularAmplitude d χ (z.2+z.1) -
          compactAngularAmplitude d h z.1 * compactAngularAmplitude d χ z.2))) :=
    (measurable_fst.norm.pow_const _).ennreal_ofReal.mul
      (Complex.continuous_normSq.measurable.comp
        (((measurable_compactAngularAmplitude d χ).comp
          (measurable_snd.add measurable_fst)).sub
          (((measurable_compactAngularAmplitude d h).comp measurable_fst).mul
            ((measurable_compactAngularAmplitude d χ).comp measurable_snd)))).ennreal_ofReal
  calc
    _ = ∫⁻ v : Rd d, ∫⁻ η : CountingConfiguration d,
        ENNReal.ofReal (‖v‖^(-p)) * ENNReal.ofReal (Complex.normSq
          (negativeCompactTestDiscrepancy d (negativeR1CompactTest d χ h v) η))
          ∂Qc ∂volume :=
      lintegral_lintegral_swap (μ := Qc) (ν := (volume : Measure (Rd d)))
        (f := fun η v => ENNReal.ofReal (‖v‖^(-p)) * ENNReal.ofReal (Complex.normSq
          (negativeCompactTestDiscrepancy d (negativeR1CompactTest d χ h v) η)))
        (hm.comp measurable_swap).aemeasurable
    _ = ∫⁻ v : Rd d, ∫⁻ k,
        ENNReal.ofReal (‖v‖^(-p)) * ENNReal.ofReal (Complex.normSq
          (compactAngularAmplitude d χ (k+v) -
            compactAngularAmplitude d h v * compactAngularAmplitude d χ k)) ∂ρ ∂volume := by
      apply lintegral_congr
      intro v
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        originalAngularSpectrumGeneral_compact_test_nn_variance
          d s hs P hP hW (negativeR1CompactTest d χ h v),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr (fun k => by rw [negativeR1CompactTest_amplitude])
    _ = _ := lintegral_lintegral_swap
      (μ := (volume : Measure (Rd d))) (ν := ρ)
      (f := fun v k => ENNReal.ofReal (‖v‖^(-p)) * ENNReal.ofReal (Complex.normSq
        (compactAngularAmplitude d χ (k+v) -
          compactAngularAmplitude d h v * compactAngularAmplitude d χ k))) hn.aemeasurable

private theorem negativeR1_lintegral_comp_inv_smul
    (d : ℕ) (f : Rd d → ℝ≥0∞) (hf : Measurable f)
    (L : ℝ) (hL : 0 < L) :
    (∫⁻ v : Rd d, f (L⁻¹ • v) ∂volume) =
      ENNReal.ofReal (L^d) * ∫⁻ v : Rd d, f v ∂volume := by
  calc
    _ = ∫⁻ v : Rd d, f v
        ∂(volume : Measure (Rd d)).map (fun v => L⁻¹ • v) :=
      (lintegral_map hf (measurable_const_smul (L⁻¹))).symm
    _ = _ := by
      rw [Measure.map_addHaar_smul (volume : Measure (Rd d)) (inv_ne_zero hL.ne'),
        lintegral_smul_measure]
      simp only [Rd, finrank_euclideanSpace_fin, inv_pow, inv_inv,
        abs_of_nonneg (pow_nonneg hL.le d), smul_eq_mul]

private def negativeR1ScaledCorrection
    (d : ℕ) (h : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) : C_c(Rd d, ℝ) :=
  (L^d)⁻¹ • angularScaledCompactWindow d h L hL

private theorem negativeR1ScaledCorrection_nonneg
    (d : ℕ) (h : C_c(Rd d, ℝ)) (hh : ∀ x, 0 ≤ h x)
    (L : ℝ) (hL : 0 < L) :
    ∀ x, 0 ≤ negativeR1ScaledCorrection d h L hL x := by
  intro x
  change 0 ≤ (L^d)⁻¹ * h (L⁻¹ • x)
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hL.le d)) (hh _)

private theorem negativeR1ScaledCorrection_mass
    (d : ℕ) (h : C_c(Rd d, ℝ)) (hh : (∫ x : Rd d, h x) = 1)
    (L : ℝ) (hL : 0 < L) :
    (∫ x : Rd d, negativeR1ScaledCorrection d h L hL x) = 1 := by
  have hscale : (∫ x : Rd d, h (L⁻¹ • x)) = (L^d)*(∫ x : Rd d, h x) := by
    simpa only [Rd, finrank_euclideanSpace_fin, smul_eq_mul] using
      Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Rd d)) h hL.le
  change (∫ x : Rd d, (L^d)⁻¹*h (L⁻¹ • x)) = 1
  rw [integral_const_mul, hscale, hh, mul_one,
    inv_mul_cancel₀ (pow_ne_zero d hL.ne')]

private theorem negativeR1ScaledCorrection_amplitude
    (d : ℕ) (h : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) (v : Rd d) :
    compactAngularAmplitude d (negativeR1ScaledCorrection d h L hL) v =
      compactAngularAmplitude d h (L • v) := by
  have hscale := compactAngularAmplitude_comp_inv_smul d h L hL v
  calc
    _ = (((L^d)⁻¹ : ℝ) : ℂ) *
        compactAngularAmplitude d (fun x => h (L⁻¹ • x)) v := by
      change (∫ x : Rd d, (((L^d)⁻¹*h (L⁻¹ • x) : ℝ) : ℂ) *
        negativeR1Phase d v x) = _
      simp only [Complex.ofReal_mul, mul_assoc, integral_const_mul]
      rfl
    _ = _ := by
      rw [hscale, ← mul_assoc, ← Complex.ofReal_mul,
        inv_mul_cancel₀ (pow_ne_zero d hL.ne'), Complex.ofReal_one, one_mul]

private theorem negativeR1_scaled_test_amplitude
    (d : ℕ) (χ h : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) (v k : Rd d) :
    negativeCompactAngularAmplitude d
      (negativeR1CompactTest d (angularScaledCompactWindow d χ L hL)
        (negativeR1ScaledCorrection d h L hL) v) k =
      ((L^d : ℝ) : ℂ) * neutralizedAngularAmplitude d χ h (-(L • k)) (L • v) := by
  have hχscale (z : Rd d) :
      compactAngularAmplitude d (angularScaledCompactWindow d χ L hL) z =
        ((L^d : ℝ) : ℂ)*compactAngularAmplitude d χ (L • z) :=
    compactAngularAmplitude_comp_inv_smul d χ L hL z
  rw [negativeR1CompactTest_amplitude, hχscale, hχscale,
    negativeR1ScaledCorrection_amplitude]
  simp only [neutralizedAngularAmplitude, neg_neg, sub_neg_eq_add, smul_add]
  rw [add_comm (L • k) (L • v)]
  ring

private theorem negativeR1_rpow_scale_cancels
    (L p : ℝ) (hL : 0 < L) : L^p * L^(-p) = 1 := by
  rw [← Real.rpow_add hL, add_neg_cancel, Real.rpow_zero]

private theorem negativeR1_scaled_profile_point
    (d : ℕ) (q : ℝ) (χ h : C_c(Rd d, ℝ))
    (L : ℝ) (hL : 0 < L) (k v : Rd d) :
    ENNReal.ofReal (‖v‖^(-((d : ℝ)+q))) * ENNReal.ofReal (Complex.normSq
      (negativeCompactAngularAmplitude d
        (negativeR1CompactTest d (angularScaledCompactWindow d χ L hL)
          (negativeR1ScaledCorrection d h L hL) v) k)) =
      ENNReal.ofReal (L^d*L^d*L^((d : ℝ)+q)) *
        ENNReal.ofReal (neutralizedFourierProfile d q χ h (-(L • k)) (L • v)) := by
  let p : ℝ := (d : ℝ)+q
  let Z : ℂ := neutralizedAngularAmplitude d χ h (-(L • k)) (L • v)
  have hnorm : ‖L • v‖ = L*‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  have hreal : ‖v‖^(-p) * ((L^d*L^d)*Complex.normSq Z) =
      (L^d*L^d*L^p)*((‖L • v‖^(-p))*Complex.normSq Z) := by
    rw [hnorm, Real.mul_rpow hL.le (norm_nonneg v)]
    calc
      _ = (L^d*L^d)*(L^p*L^(-p))*(‖v‖^(-p)*Complex.normSq Z) := by
        rw [negativeR1_rpow_scale_cancels L p hL]
        ring
      _ = _ := by ring
  rw [negativeR1_scaled_test_amplitude, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg v) _),
    ← ENNReal.ofReal_mul (mul_nonneg
      (mul_nonneg (pow_nonneg hL.le d) (pow_nonneg hL.le d))
      (Real.rpow_nonneg hL.le _))]
  exact congrArg ENNReal.ofReal hreal

private theorem negativeR1_scaled_profile_lintegral
    (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (χ h : C_c(Rd d, ℝ)) (hh : (∫ x : Rd d, h x) = 1)
    (L : ℝ) (hL : 0 < L) (k : Rd d) :
    (∫⁻ v : Rd d, ENNReal.ofReal (‖v‖^(-((d : ℝ)+q))) *
      ENNReal.ofReal (Complex.normSq
        (negativeCompactAngularAmplitude d
          (negativeR1CompactTest d (angularScaledCompactWindow d χ L hL)
            (negativeR1ScaledCorrection d h L hL) v) k)) ∂volume) =
      ENNReal.ofReal (L^d*L^((d : ℝ)+q)) *
        ENNReal.ofReal (neutralizedFourierF d q χ h (-(L • k))) := by
  let t : Rd d := -(L • k)
  let p : ℝ := (d : ℝ)+q
  let f : Rd d → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (neutralizedFourierProfile d q χ h t v)
  have hf : Measurable f :=
    ((measurable_id.norm.pow_const _).mul
      (Complex.continuous_normSq.measurable.comp
        (((measurable_compactAngularAmplitude d χ).comp
          (measurable_id.sub measurable_const)).sub
          (measurable_const.mul (measurable_compactAngularAmplitude d h))))).ennreal_ofReal
  have hDil : (∫⁻ v : Rd d, f (L • v) ∂volume) =
      ENNReal.ofReal ((L⁻¹)^d) * ∫⁻ v : Rd d, f v ∂volume := by
    simpa only [inv_inv] using negativeR1_lintegral_comp_inv_smul
      d f hf L⁻¹ (inv_pos.mpr hL)
  have hProfile : (∫⁻ v : Rd d, f v ∂volume) =
      ENNReal.ofReal (neutralizedFourierF d q χ h t) := by
    have hI := neutralizedFourierProfile_integrable d hd q hq hqTwo χ h hh t
    exact (ofReal_integral_eq_lintegral_ofReal hI.1
      (Eventually.of_forall (fun v => mul_nonneg
        (Real.rpow_nonneg (norm_nonneg v) _) (Complex.normSq_nonneg _)))).symm
  have hc : (L^d*L^d*L^p)*(L⁻¹)^d = L^d*L^p := by
    rw [inv_pow]
    field_simp [pow_ne_zero d hL.ne']
  calc
    _ = ENNReal.ofReal (L^d*L^d*L^p) * ∫⁻ v : Rd d, f (L • v) ∂volume :=
      (lintegral_congr (negativeR1_scaled_profile_point d q χ h L hL k)).trans
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
    _ = _ := by
      rw [hDil, hProfile, ← mul_assoc, ← ENNReal.ofReal_mul
        (mul_nonneg (mul_nonneg (pow_nonneg hL.le d) (pow_nonneg hL.le d))
          (Real.rpow_nonneg hL.le _)), hc]

private theorem negativeR1NeutralSigned_energy_nonneg_and_nn
    (d : ℕ) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (χ h : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (hh : ∀ x, 0 ≤ h x)
    (hhmass : (∫ x : Rd d, h x) = 1) (η : CountingConfiguration d) :
    0 ≤ Riesz.Analysis.signedDiscrepancyEnergy q (negativeR1NeutralSigned d χ h η) ∧
    ENNReal.ofReal (Riesz.Analysis.signedDiscrepancyEnergy q
      (negativeR1NeutralSigned d χ h η)) =
      ENNReal.ofReal (gamma_s (-q)*negativeR1RadialC d q) *
        ∫⁻ v : Rd d, ENNReal.ofReal (‖v‖^(-((d : ℝ)+q))) * ENNReal.ofReal
          (Complex.normSq (negativeCompactTestDiscrepancy d
            (negativeR1CompactTest d χ h v) η)) ∂volume := by
  let c : ℝ := gamma_s (-q)*negativeR1RadialC d q
  let ξ := negativeR1NeutralSigned d χ h η
  let f : Rd d → ℝ := fun v => ‖v‖^(-((d : ℝ)+q)) * Complex.normSq
    (negativeCompactTestDiscrepancy d (negativeR1CompactTest d χ h v) η)
  have hc : 0 ≤ c := mul_nonneg
    (Riesz.Analysis.gamma_s_pos (-q) (by linarith)).le
    (negativeR1RadialC_pos d q hq).le
  have hcompact : IsCompact (tsupport χ ∪ tsupport h) :=
    χ.hasCompactSupport.union h.hasCompactSupport
  have hraw := compactSigned_radial_fourier_energy d q hq hqTwo ξ
    (negativeR1NeutralSigned_mass_zero d χ h hχ hh hhmass η)
    (tsupport χ ∪ tsupport h) hcompact
    (negativeR1NeutralSigned_compact_support d χ h η)
  have hamp (v : Rd d) : signedAngularAmplitude d ξ v =
      negativeCompactTestDiscrepancy d (negativeR1CompactTest d χ h v) η :=
    negativeR1NeutralSigned_amplitude d χ h hχ hh η v
  have hfun : (fun v : Rd d => ‖v‖^(-((d : ℝ)+q)) *
      Complex.normSq (signedAngularAmplitude d ξ v)) = f := by
    funext v
    rw [hamp v]
  rw [hfun] at hraw
  have hI : Integrable f volume := hraw.1
  have hE : Riesz.Analysis.signedDiscrepancyEnergy q ξ = c*∫ v : Rd d, f v := by
    simpa only [c, negativeR1RadialC] using hraw.2
  have hf0 (v : Rd d) : 0 ≤ f v := mul_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _) (Complex.normSq_nonneg _)
  refine ⟨hE.symm ▸ mul_nonneg hc (integral_nonneg hf0), ?_⟩
  calc
    _ = ENNReal.ofReal c * ENNReal.ofReal (∫ v : Rd d, f v) := by
      rw [hE, ENNReal.ofReal_mul hc]
    _ = ENNReal.ofReal c * ∫⁻ v : Rd d, ENNReal.ofReal (f v) ∂volume := by
      rw [ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hf0)]
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro v
      exact ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg v) _)

def negativeR1ScaledInput
    (d : ℕ) (χ h : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L)
    (η : CountingConfiguration d) : SignedMeasure (Rd d) :=
  negativeR1NeutralSigned d (angularScaledCompactWindow d χ L hL)
    (negativeR1ScaledCorrection d h L hL) η

/-- Exact actual-law ENERGY-NN identity. Both sides may be top at this stage. -/
theorem negativeR1ScaledInput_energy_nn
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hs : -2 < -q)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (χ h : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (hh : ∀ x, 0 ≤ h x)
    (hhmass : (∫ x : Rd d, h x) = 1) (L : ℝ) (hL : 0 < L) :
    (∫⁻ η : CountingConfiguration d, ENNReal.ofReal
      (Riesz.Analysis.signedDiscrepancyEnergy q (negativeR1ScaledInput d χ h L hL η))
      ∂countingLawOfSimple d P) =
      ENNReal.ofReal (L^d / (2*Real.pi)^d) *
        ∫⁻ k, ENNReal.ofReal (‖-(L • k)‖^((d : ℝ)+q)*
          neutralizedFourierF d q χ h (-(L • k)))
          ∂(negativeAngularWeightedMeasure
            d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW : Measure (Rd d)) := by
  let φ := angularScaledCompactWindow d χ L hL
  let H := negativeR1ScaledCorrection d h L hL
  let ρ := originalAngularSpectrumGeneral d (-q) hs P hP hW
  let ν : Measure (Rd d) := negativeAngularWeightedMeasure
    d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
  let c : ℝ := gamma_s (-q)*negativeR1RadialC d q
  let A : ℝ := (2*Real.pi)^d
  let p : ℝ := (d : ℝ)+q
  let J : ℝ≥0∞ := ∫⁻ k, ENNReal.ofReal (neutralizedFourierF d q χ h (-(L • k))) ∂ρ
  have hqTwo : q < 2 := by linarith
  have hd' : 1 ≤ d := le_trans (by norm_num) hd
  have hφ : ∀ x, 0 ≤ φ x := angularScaledCompactWindow_nonneg d χ hχ L hL
  have hH : ∀ x, 0 ≤ H x := negativeR1ScaledCorrection_nonneg d h hh L hL
  have hHmass : (∫ x : Rd d, H x) = 1 := negativeR1ScaledCorrection_mass d h hhmass L hL
  have hc : 0 ≤ c := mul_nonneg (Riesz.Analysis.gamma_s_pos (-q) hs).le
    (negativeR1RadialC_pos d q hq).le
  have hA : 0 < A := pow_pos (by positivity) d
  have hκ : 0 ≤ negativeR1Kappa d q := (negativeR1Kappa_pos d q hq hs).le
  have hLd : 0 ≤ L^d := pow_nonneg hL.le d
  have hpL : 0 ≤ L^p := Real.rpow_nonneg hL.le p
  have hpoint (η : CountingConfiguration d) :=
    (negativeR1NeutralSigned_energy_nonneg_and_nn
      d q hq hqTwo φ H hφ hH hHmass η).2
  have hweighted :
      (∫⁻ k, ENNReal.ofReal (‖-(L • k)‖^p*neutralizedFourierF d q χ h (-(L • k))) ∂ν) =
      (ENNReal.ofReal (negativeR1Kappa d q)*ENNReal.ofReal (L^p))*J := by
    simpa only [norm_neg] using negativeR1Weighted_radial_lintegral
      d hd q hq hs P hP hW L hL
      (fun k => neutralizedFourierF d q χ h (-(L • k)))
      ((measurable_neutralizedFourierF d q χ h).comp (measurable_const_smul L).neg)
  have hcoefReal : c*(L^d*L^p) = (L^d/A)*(negativeR1Kappa d q*L^p) := by
    dsimp only [c, A, negativeR1Kappa]
    field_simp [hA.ne']
  have hcoef : ENNReal.ofReal c * ENNReal.ofReal (L^d*L^p) =
      ENNReal.ofReal (L^d/A) *
        (ENNReal.ofReal (negativeR1Kappa d q)*ENNReal.ofReal (L^p)) := by
    rw [← ENNReal.ofReal_mul hc, hcoefReal,
      ENNReal.ofReal_mul (div_nonneg hLd hA.le), ENNReal.ofReal_mul hκ]
  calc
    _ = ENNReal.ofReal c *
        ∫⁻ η : CountingConfiguration d, ∫⁻ v : Rd d,
          ENNReal.ofReal (‖v‖^(-p)) * ENNReal.ofReal (Complex.normSq
            (negativeCompactTestDiscrepancy d (negativeR1CompactTest d φ H v) η))
            ∂volume ∂countingLawOfSimple d P :=
      (lintegral_congr hpoint).trans
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
    _ = ENNReal.ofReal c *
        ∫⁻ k, ∫⁻ v : Rd d,
          ENNReal.ofReal (‖v‖^(-p)) * ENNReal.ofReal (Complex.normSq
            (compactAngularAmplitude d φ (k+v) -
              compactAngularAmplitude d H v * compactAngularAmplitude d φ k)) ∂volume ∂ρ := by
      rw [negativeR1_radial_nn_Tonelli d (-q) hs P hP hW φ H hφ hH p]
    _ = ENNReal.ofReal c * (ENNReal.ofReal (L^d*L^p)*J) := by
      congr 1
      calc
        _ = ∫⁻ k, ENNReal.ofReal (L^d*L^p) *
            ENNReal.ofReal (neutralizedFourierF d q χ h (-(L • k))) ∂ρ := by
          apply lintegral_congr
          intro k
          simpa only [negativeR1CompactTest_amplitude] using
            negativeR1_scaled_profile_lintegral d hd' q hq hqTwo χ h hhmass L hL k
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (L^d/A) *
        ((ENNReal.ofReal (negativeR1Kappa d q)*ENNReal.ofReal (L^p))*J) := by
      rw [← mul_assoc, hcoef, mul_assoc]
    _ = _ := by rw [← hweighted]

private def negativeR1RealToComplexWindow
    (d : ℕ) (φ : C_c(Rd d, ℝ)) : C_c(Rd d, ℂ) :=
  ⟨⟨fun x => (φ x : ℂ), by fun_prop⟩,
    φ.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) rfl⟩

private theorem negativeR1RealToComplexWindow_discrepancy
    (d : ℕ) (φ : C_c(Rd d, ℝ)) (η : CountingConfiguration d) :
    negativeCompactTestDiscrepancy d (negativeR1RealToComplexWindow d φ) η =
      (negativeR1MassDiscrepancy d φ η : ℂ) := by
  change (∫ x, (φ x : ℂ) ∂η.val) - (∫ x, (φ x : ℂ) ∂volume) = _
  rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_sub]
  rfl

/-- Exact actual-law VARIANCE-NN identity, with finite NN variance proved. -/
theorem negativeR1ScaledInput_mass_variance_nn
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hs : -2 < -q)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) :
    let φ := angularScaledCompactWindow d χ L hL
    let ν : Measure (Rd d) := negativeAngularWeightedMeasure
      d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
    (∫⁻ η : CountingConfiguration d,
      ENNReal.ofReal ((negativeR1MassDiscrepancy d φ η)^2)
      ∂countingLawOfSimple d P) =
      ENNReal.ofReal (L^((d : ℝ)-q)/negativeR1Kappa d q) *
        ∫⁻ k, ENNReal.ofReal (‖L • k‖^((d : ℝ)+q)*
          Complex.normSq (compactAngularAmplitude d χ (L • k))) ∂ν ∧
    (∫⁻ η : CountingConfiguration d,
      ENNReal.ofReal ((negativeR1MassDiscrepancy d φ η)^2)
      ∂countingLawOfSimple d P) ≠ ⊤ := by
  dsimp only
  let φ := angularScaledCompactWindow d χ L hL
  let f := negativeR1RealToComplexWindow d φ
  let ρ := originalAngularSpectrumGeneral d (-q) hs P hP hW
  let ν : Measure (Rd d) := negativeAngularWeightedMeasure
    d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
  let p : ℝ := (d : ℝ)+q
  let J : ℝ≥0∞ := ∫⁻ k, ENNReal.ofReal
    (Complex.normSq (compactAngularAmplitude d χ (L • k))) ∂ρ
  have hκ : 0 < negativeR1Kappa d q := negativeR1Kappa_pos d q hq hs
  have hLd : 0 ≤ L^d := pow_nonneg hL.le d
  have hD (η : CountingConfiguration d) := negativeR1RealToComplexWindow_discrepancy d φ η
  have hleft :
      (∫⁻ η : CountingConfiguration d,
        ENNReal.ofReal ((negativeR1MassDiscrepancy d φ η)^2) ∂countingLawOfSimple d P) =
      ∫⁻ η : CountingConfiguration d, ENNReal.ofReal (Complex.normSq
        (negativeCompactTestDiscrepancy d f η)) ∂countingLawOfSimple d P := by
    apply lintegral_congr
    intro η
    change ENNReal.ofReal ((negativeR1MassDiscrepancy d φ η)^2) =
      ENNReal.ofReal (Complex.normSq (negativeCompactTestDiscrepancy d
        (negativeR1RealToComplexWindow d φ) η))
    rw [hD η]
    simp only [Complex.normSq_ofReal, pow_two]
  have hamp (k : Rd d) : negativeCompactAngularAmplitude d f k =
      ((L^d : ℝ) : ℂ)*compactAngularAmplitude d χ (L • k) :=
    compactAngularAmplitude_comp_inv_smul d χ L hL k
  have hraw : (∫⁻ η : CountingConfiguration d,
      ENNReal.ofReal ((negativeR1MassDiscrepancy d φ η)^2) ∂countingLawOfSimple d P) =
      ENNReal.ofReal (L^d*L^d)*J := by
    rw [hleft, originalAngularSpectrumGeneral_compact_test_nn_variance
      d (-q) hs P hP hW f]
    calc
      _ = ∫⁻ k, ENNReal.ofReal (L^d*L^d)*ENNReal.ofReal
          (Complex.normSq (compactAngularAmplitude d χ (L • k))) ∂ρ := by
        apply lintegral_congr
        intro k
        rw [hamp k, Complex.normSq_mul, Complex.normSq_ofReal,
          ENNReal.ofReal_mul (mul_nonneg hLd hLd)]
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hweighted : (∫⁻ k, ENNReal.ofReal (‖L • k‖^p*
      Complex.normSq (compactAngularAmplitude d χ (L • k))) ∂ν) =
      (ENNReal.ofReal (negativeR1Kappa d q)*ENNReal.ofReal (L^p))*J :=
    negativeR1Weighted_radial_lintegral d hd q hq hs P hP hW L hL
      (fun k => Complex.normSq (compactAngularAmplitude d χ (L • k)))
      (Complex.continuous_normSq.measurable.comp
        ((measurable_compactAngularAmplitude d χ).comp (measurable_const_smul L)))
  have hpow : L^((d : ℝ)-q)*L^p = L^d*L^d := by
    rw [← Real.rpow_add hL]
    have he : ((d : ℝ)-q)+p = (d : ℝ)+(d : ℝ) := by dsimp only [p]; ring
    rw [he, Real.rpow_add hL]
    simp only [Real.rpow_natCast]
  have hcoefReal : (L^((d : ℝ)-q)/negativeR1Kappa d q)*
      (negativeR1Kappa d q*L^p) = L^d*L^d := by
    calc
      _ = L^((d : ℝ)-q)*L^p := by field_simp [hκ.ne']
      _ = _ := hpow
  have hcoef : ENNReal.ofReal (L^d*L^d) =
      ENNReal.ofReal (L^((d : ℝ)-q)/negativeR1Kappa d q) *
        (ENNReal.ofReal (negativeR1Kappa d q)*ENNReal.ofReal (L^p)) := by
    rw [← ENNReal.ofReal_mul hκ.le,
      ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hL.le _) hκ.le), hcoefReal]
  have hfinite : (∫⁻ η : CountingConfiguration d,
      ENNReal.ofReal ((negativeR1MassDiscrepancy d φ η)^2) ∂countingLawOfSimple d P) ≠ ⊤ := by
    have hv := originalAngularSpectrumGeneral_compact_test_variance d (-q) hs P hP hW f
    rw [hleft]
    exact (ofReal_integral_eq_lintegral_ofReal hv.1
      (Eventually.of_forall (fun _ => Complex.normSq_nonneg _))).symm.trans_ne
        ENNReal.ofReal_ne_top
  refine ⟨?_, hfinite⟩
  calc
    _ = ENNReal.ofReal (L^d*L^d)*J := hraw
    _ = ENNReal.ofReal (L^((d : ℝ)-q)/negativeR1Kappa d q)*
        ((ENNReal.ofReal (negativeR1Kappa d q)*ENNReal.ofReal (L^p))*J) := by
      rw [hcoef, mul_assoc]
    _ = _ := by rw [← hweighted]

private theorem negativeR1NeutralSigned_energy_measurable
    (d : ℕ) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (χ h : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (hh : ∀ x, 0 ≤ h x)
    (hhmass : (∫ x : Rd d, h x) = 1) :
    Measurable (fun η : CountingConfiguration d =>
      Riesz.Analysis.signedDiscrepancyEnergy q (negativeR1NeutralSigned d χ h η)) := by
  let E : CountingConfiguration d → ℝ := fun η =>
    Riesz.Analysis.signedDiscrepancyEnergy q (negativeR1NeutralSigned d χ h η)
  let c : ℝ := gamma_s (-q)*negativeR1RadialC d q
  let U : CountingConfiguration d × Rd d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (‖z.2‖^(-((d : ℝ)+q))) * ENNReal.ofReal (Complex.normSq
      (negativeCompactTestDiscrepancy d (negativeR1CompactTest d χ h z.2) z.1))
  have hU : Measurable U :=
    (measurable_snd.norm.pow_const _).ennreal_ofReal.mul
      (Complex.continuous_normSq.measurable.comp
        ((negativeR1CompactTest_joint_measurable d χ h hχ hh).comp
          measurable_swap)).ennreal_ofReal
  have hEq : (fun η => ENNReal.ofReal (E η)) =
      (fun η => ENNReal.ofReal c * ∫⁻ v : Rd d, U (η,v) ∂volume) :=
    funext (fun η => (negativeR1NeutralSigned_energy_nonneg_and_nn
      d q hq hqTwo χ h hχ hh hhmass η).2)
  have hENN : Measurable (fun η => ENNReal.ofReal (E η)) := by
    rw [hEq]
    exact measurable_const.mul hU.lintegral_prod_right'
  have hReal : (fun η => (ENNReal.ofReal (E η)).toReal) = E := by
    funext η
    exact ENNReal.toReal_ofReal
      (negativeR1NeutralSigned_energy_nonneg_and_nn
        d q hq hqTwo χ h hχ hh hhmass η).1
  change Measurable E
  rw [← hReal]
  exact hENN.ennreal_toReal

/-- Finite expected ACTUAL compact signed energy; finiteness precedes real conversion. -/
theorem negativeR1ScaledInput_energy_finite_and_real
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hs : -2 < -q)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (χ h : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (hh : ∀ x, 0 ≤ h x)
    (hχsm : ContDiff ℝ ∞ χ) (hhsm : ContDiff ℝ ∞ h)
    (hhmass : (∫ x : Rd d, h x) = 1) (L : ℝ) (hL : 0 < L) :
    let E : CountingConfiguration d → ℝ := fun η =>
      Riesz.Analysis.signedDiscrepancyEnergy q (negativeR1ScaledInput d χ h L hL η)
    let ν : Measure (Rd d) := negativeAngularWeightedMeasure
      d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
    (∫⁻ η : CountingConfiguration d, ENNReal.ofReal (E η) ∂countingLawOfSimple d P) ≠ ⊤ ∧
    Integrable E (countingLawOfSimple d P) ∧
    (∫ η : CountingConfiguration d, E η ∂countingLawOfSimple d P) =
      (L^d/(2*Real.pi)^d) * ∫ k, ‖-(L • k)‖^((d : ℝ)+q)*
        neutralizedFourierF d q χ h (-(L • k)) ∂ν := by
  dsimp only
  let E : CountingConfiguration d → ℝ := fun η =>
    Riesz.Analysis.signedDiscrepancyEnergy q (negativeR1ScaledInput d χ h L hL η)
  let ν : Measure (Rd d) := negativeAngularWeightedMeasure
    d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
  let R : Rd d → ℝ := fun k => ‖-(L • k)‖^((d : ℝ)+q)*
    neutralizedFourierF d q χ h (-(L • k))
  let φ := angularScaledCompactWindow d χ L hL
  let H := negativeR1ScaledCorrection d h L hL
  letI : IsFiniteMeasure ν := inferInstance
  have hd' : 1 ≤ d := le_trans (by norm_num) hd
  have hqTwo : q < 2 := by linarith
  have hφ : ∀ x, 0 ≤ φ x := angularScaledCompactWindow_nonneg d χ hχ L hL
  have hH : ∀ x, 0 ≤ H x := negativeR1ScaledCorrection_nonneg d h hh L hL
  have hHmass : (∫ x : Rd d, H x) = 1 := negativeR1ScaledCorrection_mass d h hhmass L hL
  have hE0 (η : CountingConfiguration d) : 0 ≤ E η :=
    (negativeR1NeutralSigned_energy_nonneg_and_nn
      d q hq hqTwo φ H hφ hH hHmass η).1
  have hEM : Measurable E := negativeR1NeutralSigned_energy_measurable
    d q hq hqTwo φ H hφ hH hHmass
  have hRM : Measurable R :=
    (((measurable_const_smul L).neg.norm.pow_const _).mul
      ((measurable_neutralizedFourierF d q χ h).comp (measurable_const_smul L).neg))
  have hR0 (k : Rd d) : 0 ≤ R k := mul_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _)
    (neutralizedFourierProfile_integrable d hd' q hq hqTwo χ h hhmass (-(L • k))).2.2.2
  obtain ⟨C, hC, hbound, _⟩ := neutralizedFourierF_scaled_bound_and_sharp_limit
    d hd' q hq hqTwo χ h hχsm hhsm hhmass
  have hRInt : Integrable R ν := (integrable_const C).mono' hRM.aestronglyMeasurable
    (Eventually.of_forall (fun k => by
      rw [Real.norm_of_nonneg (hR0 k)]
      exact hbound (-(L • k))))
  have hRFinite : (∫⁻ k, ENNReal.ofReal (R k) ∂ν) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hRM.aestronglyMeasurable
      (Eventually.of_forall hR0)).2 hRInt
  have hNN := negativeR1ScaledInput_energy_nn
    d hd q hq hs P hP hW χ h hχ hh hhmass L hL
  have hEFinite : (∫⁻ η : CountingConfiguration d, ENNReal.ofReal (E η)
      ∂countingLawOfSimple d P) ≠ ⊤ :=
    hNN.trans_ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRFinite)
  have hEInt : Integrable E (countingLawOfSimple d P) :=
    (lintegral_ofReal_ne_top_iff_integrable hEM.aestronglyMeasurable
      (Eventually.of_forall hE0)).1 hEFinite
  have hEO := ofReal_integral_eq_lintegral_ofReal hEInt (Eventually.of_forall hE0)
  have hRO := ofReal_integral_eq_lintegral_ofReal hRInt (Eventually.of_forall hR0)
  rw [← hEO, ← hRO] at hNN
  have hReal := congrArg ENNReal.toReal hNN
  have hcoef : 0 ≤ L^d/(2*Real.pi)^d :=
    div_nonneg (pow_nonneg hL.le d) (pow_nonneg (by positivity) d)
  refine ⟨hEFinite, hEInt, ?_⟩
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hE0), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hcoef, ENNReal.toReal_ofReal (integral_nonneg hR0)] using hReal

/-- The exact real variance bridge needs no smoothness assumption. -/
theorem negativeR1ScaledInput_mass_variance_real
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hs : -2 < -q)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) :
    let φ := angularScaledCompactWindow d χ L hL
    let ν : Measure (Rd d) := negativeAngularWeightedMeasure
      d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
    let R : Rd d → ℝ := fun k => ‖L • k‖^((d : ℝ)+q)*
      Complex.normSq (compactAngularAmplitude d χ (L • k))
    Integrable (fun η : CountingConfiguration d => (negativeR1MassDiscrepancy d φ η)^2)
      (countingLawOfSimple d P) ∧
    Integrable R ν ∧
    (∫ η : CountingConfiguration d, (negativeR1MassDiscrepancy d φ η)^2
      ∂countingLawOfSimple d P) =
      (L^((d : ℝ)-q)/negativeR1Kappa d q) * ∫ k, R k ∂ν := by
  dsimp only
  let φ := angularScaledCompactWindow d χ L hL
  let f := negativeR1RealToComplexWindow d φ
  let ν : Measure (Rd d) := negativeAngularWeightedMeasure
    d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
  let R : Rd d → ℝ := fun k => ‖L • k‖^((d : ℝ)+q)*
    Complex.normSq (compactAngularAmplitude d χ (L • k))
  have hNN := negativeR1ScaledInput_mass_variance_nn d hd q hq hs P hP hW χ L hL
  have hv := originalAngularSpectrumGeneral_compact_test_variance d (-q) hs P hP hW f
  have hVInt : Integrable (fun η : CountingConfiguration d =>
      (negativeR1MassDiscrepancy d φ η)^2) (countingLawOfSimple d P) :=
    hv.1.congr (Eventually.of_forall (fun η => by
      change Complex.normSq (negativeCompactTestDiscrepancy d
        (negativeR1RealToComplexWindow d φ) η) = (negativeR1MassDiscrepancy d φ η)^2
      rw [negativeR1RealToComplexWindow_discrepancy]
      simp only [Complex.normSq_ofReal, pow_two]))
  have hRM : Measurable R :=
    ((measurable_const_smul L).norm.pow_const _).mul
      (Complex.continuous_normSq.measurable.comp
        ((measurable_compactAngularAmplitude d χ).comp (measurable_const_smul L)))
  have hR0 (k : Rd d) : 0 ≤ R k := mul_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _) (Complex.normSq_nonneg _)
  have hcoef : 0 < L^((d : ℝ)-q)/negativeR1Kappa d q :=
    div_pos (Real.rpow_pos_of_pos hL _) (negativeR1Kappa_pos d q hq hs)
  have hRFinite : (∫⁻ k, ENNReal.ofReal (R k) ∂ν) ≠ ⊤ :=
    (ENNReal.lt_top_of_mul_ne_top_right (hNN.1.symm.trans_ne hNN.2)
      (ENNReal.ofReal_ne_zero_iff.mpr hcoef)).ne
  have hRInt : Integrable R ν :=
    (lintegral_ofReal_ne_top_iff_integrable hRM.aestronglyMeasurable
      (Eventually.of_forall hR0)).1 hRFinite
  have hVO := ofReal_integral_eq_lintegral_ofReal hVInt
    (Eventually.of_forall (fun η => sq_nonneg (negativeR1MassDiscrepancy d φ η)))
  have hRO := ofReal_integral_eq_lintegral_ofReal hRInt (Eventually.of_forall hR0)
  have heq := hNN.1
  rw [← hVO, ← hRO] at heq
  have hReal := congrArg ENNReal.toReal heq
  refine ⟨hVInt, hRInt, ?_⟩
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun η =>
      sq_nonneg (negativeR1MassDiscrepancy d φ η))), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hcoef.le, ENNReal.toReal_ofReal (integral_nonneg hR0)] using hReal

/-- Actual R1 energy and variance limits; the only law inputs are original admissibility and finite W. -/
theorem negativeR1ScaledInput_energy_and_variance_tendsto
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hs : -2 < -q)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (χ h : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (hh : ∀ x, 0 ≤ h x)
    (hχsm : ContDiff ℝ ∞ χ) (hhsm : ContDiff ℝ ∞ h)
    (hhmass : (∫ x : Rd d, h x) = 1)
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n) (hLinf : Tendsto L atTop atTop) :
    let E : ℕ → CountingConfiguration d → ℝ := fun n η =>
      Riesz.Analysis.signedDiscrepancyEnergy q (negativeR1ScaledInput d χ h (L n) (hL n) η)
    let D : ℕ → CountingConfiguration d → ℝ := fun n η =>
      negativeR1MassDiscrepancy d (angularScaledCompactWindow d χ (L n) (hL n)) η
    (∀ n, Integrable (E n) (countingLawOfSimple d P)) ∧
    Tendsto (fun n => (L n^d)⁻¹ * ∫ η, E n η ∂countingLawOfSimple d P) atTop
      (𝓝 ((∫ x : Rd d, (χ x)^2)*(W d (-q) P).toReal)) ∧
    (∀ n, Integrable (fun η => (D n η)^2) (countingLawOfSimple d P)) ∧
    Tendsto (fun n => (L n^((d : ℝ)-q))⁻¹ *
      ∫ η, (D n η)^2 ∂countingLawOfSimple d P) atTop (𝓝 0) := by
  dsimp only
  let ν : Measure (Rd d) := negativeAngularWeightedMeasure
    d hd (-q) hs (neg_lt_zero.mpr hq) P hP hW
  let A : ℝ := (2*Real.pi)^d
  let a : ℝ := ∫ x : Rd d, (χ x)^2
  have hA : 0 < A := pow_pos (by positivity) d
  have hκ : 0 < negativeR1Kappa d q := negativeR1Kappa_pos d q hq hs
  have hE (n : ℕ) := negativeR1ScaledInput_energy_finite_and_real
    d hd q hq hs P hP hW χ h hχ hh hχsm hhsm hhmass (L n) (hL n)
  have hV (n : ℕ) := negativeR1ScaledInput_mass_variance_real
    d hd q hq hs P hP hW χ (L n) (hL n)
  have hEnergy := ((negativeWeighted_neutralizedF_integrable_and_tendsto
    d hd q hq hs P hP hW χ h hχsm hhsm hhmass L hL hLinf).2).const_mul A⁻¹
  have hVariance := ((negativeWeighted_scaled_density_integrable_and_tendsto
    d hd q hq hs P hP hW χ hχsm L hL hLinf).2).const_mul (negativeR1Kappa d q)⁻¹
  have hEnergyValue : A⁻¹*((A*a)*(W d (-q) P).toReal) = a*(W d (-q) P).toReal := by
    field_simp [hA.ne']
  rw [hEnergyValue] at hEnergy
  simp only [mul_zero] at hVariance
  refine ⟨fun n => (hE n).2.1, ?_, fun n => (hV n).1, ?_⟩
  · apply Filter.Tendsto.congr' (h := hEnergy)
    apply Eventually.of_forall
    intro n
    change A⁻¹ * (∫ k, ‖-(L n • k)‖^((d : ℝ)+q) *
        neutralizedFourierF d q χ h (-(L n • k)) ∂ν) =
      (L n^d)⁻¹ * (∫ η : CountingConfiguration d,
        Riesz.Analysis.signedDiscrepancyEnergy q
          (negativeR1ScaledInput d χ h (L n) (hL n) η) ∂countingLawOfSimple d P)
    rw [(hE n).2.2]
    field_simp [pow_ne_zero d (hL n).ne', hA.ne']
    ring
  · apply Filter.Tendsto.congr' (h := hVariance)
    apply Eventually.of_forall
    intro n
    change (negativeR1Kappa d q)⁻¹ * (∫ k, ‖L n • k‖^((d : ℝ)+q) *
        Complex.normSq (compactAngularAmplitude d χ (L n • k)) ∂ν) =
      (L n^((d : ℝ)-q))⁻¹ * (∫ η : CountingConfiguration d,
        (negativeR1MassDiscrepancy d (angularScaledCompactWindow d χ (L n) (hL n)) η)^2
          ∂countingLawOfSimple d P)
    rw [(hV n).2.2]
    field_simp [(Real.rpow_pos_of_pos (hL n) ((d : ℝ)-q)).ne', hκ.ne']
    ring


theorem negativeR1ScaledInput_energy_nonneg
    (d : ℕ) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (χ h : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (hh : ∀ x, 0 ≤ h x)
    (hhmass : (∫ x : Rd d, h x) = 1) (L : ℝ) (hL : 0 < L)
    (η : CountingConfiguration d) :
    0 ≤ Riesz.Analysis.signedDiscrepancyEnergy q (negativeR1ScaledInput d χ h L hL η) := by
  exact (negativeR1NeutralSigned_energy_nonneg_and_nn d q hq hqTwo
    (angularScaledCompactWindow d χ L hL) (negativeR1ScaledCorrection d h L hL)
    (angularScaledCompactWindow_nonneg d χ hχ L hL)
    (negativeR1ScaledCorrection_nonneg d h hh L hL)
    (negativeR1ScaledCorrection_mass d h hhmass L hL) η).1

end Riesz.Stationary
