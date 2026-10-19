import Riesz.Stationary.CompactPairHeatRemoval
import Mathlib.MeasureTheory.Integral.CompactlySupported

noncomputable section
open MeasureTheory Filter RieszShowcase Riesz.Configuration
open scoped ENNReal Topology ComplexConjugate CompactlySupported RealInnerProductSpace

namespace Riesz.Stationary

def compactAngularAmplitude (d : ℕ) (χ : Rd d → ℝ) (q : Rd d) : ℂ :=
  ∫ x, (χ x : ℂ) * Complex.exp ((inner ℝ q x : ℂ) * Complex.I)

theorem angularPhase_pair (d : ℕ) (q a b : Rd d) :
    Complex.exp ((inner ℝ q (b - a) : ℂ) * Complex.I) =
      conj (Complex.exp ((inner ℝ q a : ℂ) * Complex.I)) *
        Complex.exp ((inner ℝ q b : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [inner_sub_right, Complex.ofReal_sub, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  ring

theorem compactAngularAmplitude_pair (d : ℕ) (χ : Rd d → ℝ) (q : Rd d) :
    (∫ p : Rd d × Rd d, (χ p.1 : ℂ) * (χ p.2 : ℂ) *
        Complex.exp ((inner ℝ q (p.2 - p.1) : ℂ) * Complex.I)
          ∂(volume.prod volume)) =
      (Complex.normSq (compactAngularAmplitude d χ q) : ℂ) := by
  have hp (p : Rd d × Rd d) :
      (χ p.1 : ℂ) * (χ p.2 : ℂ) *
          Complex.exp ((inner ℝ q (p.2 - p.1) : ℂ) * Complex.I) =
        conj ((χ p.1 : ℂ) * Complex.exp ((inner ℝ q p.1 : ℂ) * Complex.I)) *
          ((χ p.2 : ℂ) * Complex.exp ((inner ℝ q p.2 : ℂ) * Complex.I)) := by
    rw [angularPhase_pair]
    simp only [map_mul, Complex.conj_ofReal]
    ring
  rw [integral_congr_ae (Eventually.of_forall hp),
    integral_prod_mul
      (fun x : Rd d => conj ((χ x : ℂ) * Complex.exp ((inner ℝ q x : ℂ) * Complex.I)))
      (fun x : Rd d => (χ x : ℂ) * Complex.exp ((inner ℝ q x : ℂ) * Complex.I)),
    integral_conj, ← Complex.normSq_eq_conj_mul_self, compactAngularAmplitude]

theorem compactAngularAmplitude_norm_le
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (q : Rd d) :
    ‖compactAngularAmplitude d χ q‖ ≤ ∫ x, χ x := by
  refine (norm_integral_le_integral_norm _).trans_eq
    (integral_congr_ae (Eventually.of_forall (fun x => ?_)))
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ x)]

theorem measurable_compactAngularAmplitude
    (d : ℕ) (χ : C_c(Rd d, ℝ)) :
    Measurable (compactAngularAmplitude d χ) := by
  have hm : StronglyMeasurable (fun p : Rd d × Rd d =>
      (χ p.2 : ℂ) * Complex.exp ((inner ℝ p.1 p.2 : ℂ) * Complex.I)) :=
    (show Continuous _ from by fun_prop).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem angularPhase_sub_frequency (d : ℕ) (k η z : Rd d) :
    Complex.exp ((inner ℝ (k - η) z : ℂ) * Complex.I) =
      Complex.exp ((inner ℝ η (-z) : ℂ) * Complex.I) *
        Complex.exp ((inner ℝ k z : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [inner_sub_left, inner_neg_right, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

theorem integrable_gaussianAngularPair
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (u : ℝ) (hu : 0 < u) (k : Rd d) :
    Integrable (fun q : Rd d × (Rd d × Rd d) =>
      (originalHeatGaussian d u q.1 : ℂ) *
        ((χ q.2.1 : ℂ) * (χ q.2.2 : ℂ) *
          Complex.exp ((inner ℝ (k - q.1) (q.2.2 - q.2.1) : ℂ) * Complex.I)))
      (volume.prod (volume.prod volume)) := by
  have hp : Integrable (fun p : Rd d × Rd d => χ p.1 * χ p.2)
      (volume.prod volume) := χ.integrable.mul_prod χ.integrable
  refine ((integrable_originalHeatGaussian d u hu).mul_prod hp).mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp
      ((continuous_originalHeatGaussian d u).comp continuous_fst)).mul
        (((Complex.continuous_ofReal.comp (χ.continuous.comp
            (continuous_fst.comp continuous_snd))).mul
          (Complex.continuous_ofReal.comp (χ.continuous.comp
            (continuous_snd.comp continuous_snd)))).mul
          (show Continuous _ from by fun_prop))).aestronglyMeasurable
  · exact Eventually.of_forall (fun q => by
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (originalHeatGaussian_nonneg d u hu q.1),
        abs_of_nonneg (hχ q.2.1), abs_of_nonneg (hχ q.2.2), le_refl])

theorem compactGaussianAngularPair_eq
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (u : ℝ) (hu : 0 < u) (k : Rd d) :
    (∫ p : Rd d × Rd d, (χ p.1 : ℂ) * (χ p.2 : ℂ) *
      (Real.exp (-u * ‖p.2 - p.1‖ ^ 2) : ℂ) *
        Complex.exp ((inner ℝ k (p.2 - p.1) : ℂ) * Complex.I)
          ∂(volume.prod volume)) =
    ∫ η : Rd d, (originalHeatGaussian d u η : ℂ) *
      (Complex.normSq (compactAngularAmplitude d χ (k - η)) : ℂ) := by
  let F : Rd d → (Rd d × Rd d) → ℂ := fun η p =>
    (originalHeatGaussian d u η : ℂ) *
      ((χ p.1 : ℂ) * (χ p.2 : ℂ) *
        Complex.exp ((inner ℝ (k - η) (p.2 - p.1) : ℂ) * Complex.I))
  have hF : Integrable (Function.uncurry F)
      (volume.prod (volume.prod volume)) := integrable_gaussianAngularPair d χ hχ u hu k
  have he (η : Rd d) : (∫ p : Rd d × Rd d, F η p ∂(volume.prod volume)) =
      (originalHeatGaussian d u η : ℂ) *
        (Complex.normSq (compactAngularAmplitude d χ (k - η)) : ℂ) :=
    (integral_const_mul _ _).trans
      (congrArg (fun z : ℂ => (originalHeatGaussian d u η : ℂ) * z)
        (compactAngularAmplitude_pair d χ (k - η)))
  have hp (p : Rd d × Rd d) : (∫ η : Rd d, F η p) =
      (χ p.1 : ℂ) * (χ p.2 : ℂ) *
        (Real.exp (-u * ‖p.2 - p.1‖ ^ 2) : ℂ) *
          Complex.exp ((inner ℝ k (p.2 - p.1) : ℂ) * Complex.I) := by
    calc
      _ = ((χ p.1 : ℂ) * (χ p.2 : ℂ) *
          Complex.exp ((inner ℝ k (p.2 - p.1) : ℂ) * Complex.I)) *
          ∫ η : Rd d, (originalHeatGaussian d u η : ℂ) *
            Complex.exp ((inner ℝ η (-(p.2 - p.1)) : ℂ) * Complex.I) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall (fun η => ?_))
        dsimp only [F]
        rw [angularPhase_sub_frequency]
        ring
      _ = _ := by
        rw [integral_originalHeatGaussian_mul_angularExp d u hu, norm_neg]
        ring
  exact (integral_congr_ae (Eventually.of_forall hp)).symm.trans
    ((integral_integral_swap hF).symm.trans
      (integral_congr_ae (Eventually.of_forall he)))

theorem measurable_originalHeatGaussian_joint (d : ℕ) :
    Measurable (fun p : ℝ × Rd d => originalHeatGaussian d p.1 p.2) := by
  exact ((measurable_const.mul measurable_fst).pow_const (-((d : ℝ) / 2))).mul
    (((measurable_const.div (measurable_const.mul measurable_fst)).neg.mul
      (measurable_snd.norm.pow_const 2)).exp)

def angularHeadBaseNN (d : ℕ) (s : ℝ) (p : ℝ × Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (p.1 ^ (s / 2 - 1)) *
    ENNReal.ofReal (originalHeatGaussian d p.1 p.2)

theorem measurable_angularHeadBaseNN (d : ℕ) (s : ℝ) :
    Measurable (angularHeadBaseNN d s) := by
  exact (measurable_fst.pow_const (s / 2 - 1)).ennreal_ofReal.mul
    (measurable_originalHeatGaussian_joint d).ennreal_ofReal

theorem angularHeadBaseNN_lintegral (d : ℕ) (s : ℝ) (hs : 0 < s) :
    (∫⁻ p, angularHeadBaseNN d s p
      ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure (Rd d))) =
        ENNReal.ofReal (2 / s) := by
  let τ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  obtain ⟨hwint, hwmass⟩ := positiveHeadWeight_integrable_and_integral s hs
  have hu : ∀ᵐ u ∂τ, u ∈ Set.Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  refine (lintegral_prod _ (measurable_angularHeadBaseNN d s).aemeasurable).trans
    ((?_ : (∫⁻ u, ∫⁻ η : Rd d, angularHeadBaseNN d s (u, η) ∂volume ∂τ) =
        ∫⁻ u, ENNReal.ofReal (u ^ (s / 2 - 1)) ∂τ).trans
      ((ofReal_integral_eq_lintegral_ofReal hwint
        (hu.mono (fun u hu => Real.rpow_nonneg hu.1.le _))).symm.trans
          (congrArg ENNReal.ofReal hwmass)))
  refine lintegral_congr_ae (hu.mono (fun u hu => ?_))
  simp only [angularHeadBaseNN, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_originalHeatGaussian_unshifted d u hu.1, mul_one]

def compactAngularHeadJ (d : ℕ) (s : ℝ) (χ : C_c(Rd d, ℝ)) (k : Rd d) : ℝ≥0∞ :=
  ∫⁻ u in Set.Ioc (0 : ℝ) 1, ∫⁻ η : Rd d,
    angularHeadBaseNN d s (u, η) *
      ENNReal.ofReal (Complex.normSq (compactAngularAmplitude d χ (k - η)))

theorem measurable_compactAngularHeadJ_integrand
    (d : ℕ) (s : ℝ) (χ : C_c(Rd d, ℝ)) (k : Rd d) :
    Measurable (fun p : ℝ × Rd d => angularHeadBaseNN d s p *
      ENNReal.ofReal (Complex.normSq (compactAngularAmplitude d χ (k - p.2)))) := by
  exact (measurable_angularHeadBaseNN d s).mul
    (Complex.continuous_normSq.measurable.comp
      ((measurable_compactAngularAmplitude d χ).comp
        (measurable_const.sub measurable_snd))).ennreal_ofReal

theorem measurable_compactAngularHeadJ (d : ℕ) (s : ℝ) (χ : C_c(Rd d, ℝ)) :
    Measurable (compactAngularHeadJ d s χ) := by
  have hm : Measurable (fun p : (Rd d × ℝ) × Rd d =>
      angularHeadBaseNN d s (p.1.2, p.2) *
        ENNReal.ofReal (Complex.normSq (compactAngularAmplitude d χ (p.1.1 - p.2)))) :=
    ((measurable_angularHeadBaseNN d s).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
        (Complex.continuous_normSq.measurable.comp
          ((measurable_compactAngularAmplitude d χ).comp
            ((measurable_fst.comp measurable_fst).sub measurable_snd))).ennreal_ofReal
  exact hm.lintegral_prod_right'.lintegral_prod_right'

theorem compactAngularHeadJ_le
    (d : ℕ) (s : ℝ) (hs : 0 < s) (χ : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) (k : Rd d) :
    compactAngularHeadJ d s χ k ≤ ENNReal.ofReal ((2 / s) * (∫ x, χ x) ^ 2) := by
  have hR (η : Rd d) :
      Complex.normSq (compactAngularAmplitude d χ (k - η)) ≤ (∫ x, χ x) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) (integral_nonneg hχ)).2
      (compactAngularAmplitude_norm_le d χ hχ (k - η))
  have hprod : compactAngularHeadJ d s χ k =
      ∫⁻ p : ℝ × Rd d, angularHeadBaseNN d s p *
        ENNReal.ofReal (Complex.normSq (compactAngularAmplitude d χ (k - p.2)))
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume :=
    (lintegral_prod _ (measurable_compactAngularHeadJ_integrand d s χ k).aemeasurable).symm
  refine calc
    _ = ∫⁻ p : ℝ × Rd d, angularHeadBaseNN d s p *
          ENNReal.ofReal (Complex.normSq (compactAngularAmplitude d χ (k - p.2)))
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume := hprod
    _ ≤ ∫⁻ p : ℝ × Rd d, angularHeadBaseNN d s p *
          ENNReal.ofReal ((∫ x, χ x) ^ 2)
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume :=
      lintegral_mono (fun p => mul_le_mul_right
        (ENNReal.ofReal_le_ofReal (hR p.2)) (angularHeadBaseNN d s p))
    _ = _ := ?_
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    angularHeadBaseNN_lintegral d s hs, ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / s)]

theorem compactAngularHeadJ_ne_top
    (d : ℕ) (s : ℝ) (hs : 0 < s) (χ : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) (k : Rd d) : compactAngularHeadJ d s χ k ≠ ∞ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (compactAngularHeadJ_le d s hs χ hχ k)

theorem compactAngularHeadJ_real_product
    (d : ℕ) (s : ℝ) (hs : 0 < s) (χ : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) (k : Rd d) :
    Integrable (fun p : ℝ × Rd d => p.1 ^ (s / 2 - 1) *
      originalHeatGaussian d p.1 p.2 *
        Complex.normSq (compactAngularAmplitude d χ (k - p.2)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure (Rd d))) ∧
    (∫ u in Set.Ioc (0 : ℝ) 1, ∫ η : Rd d,
      u ^ (s / 2 - 1) * originalHeatGaussian d u η *
        Complex.normSq (compactAngularAmplitude d χ (k - η))) =
          (compactAngularHeadJ d s χ k).toReal := by
  let τ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let H : ℝ × Rd d → ℝ≥0∞ := fun p => angularHeadBaseNN d s p *
    ENNReal.ofReal (Complex.normSq (compactAngularAmplitude d χ (k - p.2)))
  let h : ℝ × Rd d → ℝ := fun p => p.1 ^ (s / 2 - 1) *
    originalHeatGaussian d p.1 p.2 *
      Complex.normSq (compactAngularAmplitude d χ (k - p.2))
  have hHm : Measurable H := measurable_compactAngularHeadJ_integrand d s χ k
  have hprod : (∫⁻ p, H p ∂τ.prod volume) = compactAngularHeadJ d s χ k :=
    lintegral_prod H hHm.aemeasurable
  have hfin : (∫⁻ p, H p ∂τ.prod volume) ≠ ∞ :=
    hprod.trans_ne (compactAngularHeadJ_ne_top d s hs χ hχ k)
  have hu : ∀ᵐ p : ℝ × Rd d ∂τ.prod volume, p.1 ∈ Set.Ioc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := τ) (ν := (volume : Measure (Rd d)))).ae
      (ae_restrict_mem measurableSet_Ioc)
  have heq : (fun p => (H p).toReal) =ᵐ[τ.prod volume] h :=
    hu.mono (fun p hp => by
      simp only [H, h, angularHeadBaseNN, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hp.1.le _),
        ENNReal.toReal_ofReal (originalHeatGaussian_nonneg d p.1 hp.1 p.2),
        ENNReal.toReal_ofReal (Complex.normSq_nonneg _)])
  have hint : Integrable h (τ.prod volume) :=
    (integrable_toReal_of_lintegral_ne_top hHm.aemeasurable hfin).congr heq
  have hvalue : (∫ p, h p ∂τ.prod volume) = (compactAngularHeadJ d s χ k).toReal :=
    (integral_congr_ae heq).symm.trans
      ((integral_toReal hHm.aemeasurable (ae_lt_top hHm hfin)).trans
        (congrArg ENNReal.toReal hprod))
  exact ⟨hint, (integral_prod h hint).symm.trans hvalue⟩

theorem compactPositiveHeadPairTest_angular_eq
    (d : ℕ) (s : ℝ) (hs : 0 < s) (χ : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) (k : Rd d) :
    (∫ p : Rd d × Rd d, (compactPositiveHeadPairTest d s hs χ p : ℂ) *
      Complex.exp ((inner ℝ k (p.2 - p.1) : ℂ) * Complex.I)
        ∂(volume : Measure (Rd d)).prod volume) =
          ((compactAngularHeadJ d s χ k).toReal : ℂ) := by
  let τ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let F : ℝ → (Rd d × Rd d) → ℂ := fun u p => ((u ^ (s / 2 - 1) : ℝ) : ℂ) *
    ((χ p.1 : ℂ) * (χ p.2 : ℂ) *
      (Real.exp (-(u * ‖p.2 - p.1‖ ^ (2 : ℕ))) : ℂ) *
        Complex.exp ((inner ℝ k (p.2 - p.1) : ℂ) * Complex.I))
  have hmajor : Integrable (fun q : ℝ × (Rd d × Rd d) =>
      q.1 ^ (s / 2 - 1) * (χ q.2.1 * χ q.2.2))
        (τ.prod ((volume : Measure (Rd d)).prod volume)) :=
    (positiveHeadWeight_integrable_and_integral s hs).1.mul_prod
      (χ.integrable.mul_prod χ.integrable)
  have hFm : Measurable (Function.uncurry F) := by
    dsimp [F]
    fun_prop
  have hu : ∀ᵐ q : ℝ × (Rd d × Rd d) ∂τ.prod (volume.prod volume),
      q.1 ∈ Set.Ioc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst
      (μ := τ) (ν := (volume : Measure (Rd d)).prod volume)).ae
        (ae_restrict_mem measurableSet_Ioc)
  have hF : Integrable (Function.uncurry F) (τ.prod (volume.prod volume)) := by
    refine hmajor.mono' hFm.aestronglyMeasurable (hu.mono (fun q hq => ?_))
    simpa only [Function.uncurry, F, norm_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hq.1.le (s / 2 - 1)),
      abs_of_nonneg (hχ q.2.1), abs_of_nonneg (hχ q.2.2),
      abs_of_pos (Real.exp_pos _), mul_assoc] using
        (mul_le_of_le_one_right
          (mul_nonneg (Real.rpow_nonneg hq.1.le (s / 2 - 1))
            (mul_nonneg (hχ q.2.1) (hχ q.2.2)))
          (Real.exp_le_one_iff.mpr
            (neg_nonpos.mpr (mul_nonneg hq.1.le (sq_nonneg ‖q.2.2 - q.2.1‖)))))
  have hp (p : Rd d × Rd d) :
      (∫ u, F u p ∂τ) = (compactPositiveHeadPairTest d s hs χ p : ℂ) *
        Complex.exp ((inner ℝ k (p.2 - p.1) : ℂ) * Complex.I) := by
    have heq (u : ℝ) : F u p =
        ((u ^ (s / 2 - 1) * Real.exp (-(u * ‖p.2 - p.1‖ ^ (2 : ℕ))) : ℝ) : ℂ) *
          ((χ p.1 : ℂ) * (χ p.2 : ℂ) *
            Complex.exp ((inner ℝ k (p.2 - p.1) : ℂ) * Complex.I)) := by
      dsimp only [F]
      push_cast
      ring
    rw [integral_congr_ae (Eventually.of_forall heq), integral_mul_const,
      integral_complex_ofReal]
    change (positiveHeadKernel d s (p.2 - p.1) : ℂ) *
      ((χ p.1 : ℂ) * (χ p.2 : ℂ) *
        Complex.exp ((inner ℝ k (p.2 - p.1) : ℂ) * Complex.I)) =
      ((χ p.1 * χ p.2 * positiveHeadKernel d s (p.2 - p.1) : ℝ) : ℂ) *
        Complex.exp ((inner ℝ k (p.2 - p.1) : ℂ) * Complex.I)
    push_cast
    ring
  have huFixed : (fun u => ∫ p, F u p ∂volume.prod volume) =ᵐ[τ]
      (fun u => ((u ^ (s / 2 - 1) : ℝ) : ℂ) *
        ∫ η : Rd d, (originalHeatGaussian d u η : ℂ) *
          (Complex.normSq (compactAngularAmplitude d χ (k - η)) : ℂ)) := by
    refine (show ∀ᵐ u ∂τ, u ∈ Set.Ioc (0 : ℝ) 1 from
      ae_restrict_mem measurableSet_Ioc).mono (fun u hu => ?_)
    exact (integral_const_mul _ _).trans
      (congrArg (fun z : ℂ => ((u ^ (s / 2 - 1) : ℝ) : ℂ) * z)
        (by simpa only [neg_mul] using compactGaussianAngularPair_eq d χ hχ u hu.1 k))
  have hcast (u : ℝ) :
      ((u ^ (s / 2 - 1) : ℝ) : ℂ) *
        (∫ η : Rd d, (originalHeatGaussian d u η : ℂ) *
          (Complex.normSq (compactAngularAmplitude d χ (k - η)) : ℂ)) =
      (((∫ η : Rd d, u ^ (s / 2 - 1) * originalHeatGaussian d u η *
        Complex.normSq (compactAngularAmplitude d χ (k - η))) : ℝ) : ℂ) := by
    rw [← integral_const_mul, ← integral_complex_ofReal]
    simp only [Complex.ofReal_mul, mul_assoc]
  exact calc
    _ = ∫ p : Rd d × Rd d, ∫ u, F u p ∂τ ∂volume.prod volume :=
      (integral_congr_ae (Eventually.of_forall hp)).symm
    _ = ∫ u, ∫ p : Rd d × Rd d, F u p ∂volume.prod volume ∂τ :=
      (integral_integral_swap hF).symm
    _ = ∫ u, (((∫ η : Rd d, u ^ (s / 2 - 1) * originalHeatGaussian d u η *
        Complex.normSq (compactAngularAmplitude d χ (k - η))) : ℝ) : ℂ) ∂τ :=
      integral_congr_ae (huFixed.trans (Eventually.of_forall hcast))
    _ = (((∫ u, (∫ η : Rd d, u ^ (s / 2 - 1) * originalHeatGaussian d u η *
        Complex.normSq (compactAngularAmplitude d χ (k - η))) ∂τ) : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = _ := congrArg Complex.ofReal (compactAngularHeadJ_real_product d s hs χ hχ k).2

theorem compactPair_charFun_fubini
    (d : ℕ) (ψ : C_c(Rd d × Rd d, ℝ)) (hψ : ∀ p, 0 ≤ ψ p)
    (σ : Measure (Rd d)) [IsFiniteMeasure σ] :
    (∫ p : Rd d × Rd d, (ψ p : ℂ) * charFun σ (p.2 - p.1)
      ∂(volume.prod volume)) =
      ∫ k : Rd d, (∫ p : Rd d × Rd d, (ψ p : ℂ) *
        Complex.exp ((inner ℝ k (p.2 - p.1) : ℂ) * Complex.I)
          ∂(volume.prod volume)) ∂σ := by
  have hK : Integrable (fun q : (Rd d × Rd d) × Rd d =>
      (ψ q.1 : ℂ) *
        Complex.exp ((inner ℝ q.2 (q.1.2 - q.1.1) : ℂ) * Complex.I))
      ((volume.prod volume).prod σ) := by
    refine (ψ.integrable.comp_fst σ).mono'
      (show Continuous _ from by fun_prop).aestronglyMeasurable ?_
    exact Eventually.of_forall (fun q => by
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ q.1), le_refl])
  refine Eq.trans ?_ (integral_integral_swap hK)
  simp only [integral_const_mul, ← charFun_apply]

theorem integrable_compactAngularHeadJ_toReal
    (d : ℕ) (s : ℝ) (hs : 0 < s) (χ : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) (σ : Measure (Rd d)) [IsFiniteMeasure σ] :
    Integrable (fun k => (compactAngularHeadJ d s χ k).toReal) σ := by
  refine integrable_toReal_of_lintegral_ne_top
    (measurable_compactAngularHeadJ d s χ).aemeasurable
      (ne_top_of_le_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.ofReal_ne_top (r := (2 / s) * (∫ x, χ x) ^ 2))
          (measure_ne_top σ Set.univ)) ?_)
  exact calc
    _ ≤ ∫⁻ _k : Rd d, ENNReal.ofReal ((2 / s) * (∫ x, χ x) ^ 2) ∂σ :=
      lintegral_mono (fun k => compactAngularHeadJ_le d s hs χ hχ k)
    _ = _ := lintegral_const _

theorem compactPositiveHeadPairTest_heatSpectrum_integral
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (t : ℝ) (ht : 0 < t) :
    (∫ q : Rd d × Rd d, compactPositiveHeadPairTest d s hs χ q *
      originalHeatCovariance d P t (q.2 - q.1)
        ∂(volume : Measure (Rd d)).prod volume) =
      ∫ k, (compactAngularHeadJ d s χ k).toReal
        ∂(originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)) := by
  have hComplex := compactPair_charFun_fubini d (compactPositiveHeadPairTest d s hs χ)
    (fun q => (compactPositiveHeadPairTest_nonneg_and_bound d s hs χ hχ q).1)
      (originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d))
  exact Complex.ofReal_inj.mp (by
    simpa only [charFun_originalHeatSpectrum d s hs P hP hW t ht,
      compactPositiveHeadPairTest_angular_eq d s hs χ hχ,
      ← Complex.ofReal_mul, integral_complex_ofReal] using hComplex)

theorem compactPositiveHeadPairTest_angularSpectrum_lintegral
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (∫ q : Rd d × Rd d, compactPositiveHeadPairTest d s hs χ q *
      originalHeatCovariance d P t (q.2 - q.1)
        ∂(volume : Measure (Rd d)).prod volume) =
      ∫⁻ k, heatSpectralWeight d t k * compactAngularHeadJ d s χ k
        ∂originalAngularSpectrum d s hs P hP hW := by
  refine Eq.trans ?_ (lintegral_withDensity_eq_lintegral_mul
    (originalAngularSpectrum d s hs P hP hW)
      (measurable_heatSpectralWeight d t) (measurable_compactAngularHeadJ d s χ))
  rw [originalAngularSpectrum_withDensity_eq_heatSpectrum d s hs P hP hW t ht]
  exact (congrArg ENNReal.ofReal
    (compactPositiveHeadPairTest_heatSpectrum_integral d s hs P hP hW χ hχ t ht)).trans
      ((ofReal_integral_eq_lintegral_ofReal
        (integrable_compactAngularHeadJ_toReal d s hs χ hχ _)
          (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))).trans
            (lintegral_congr (fun k => ENNReal.ofReal_toReal
              (compactAngularHeadJ_ne_top d s hs χ hχ k))))

theorem angularHead_heatWeight_sq_lintegral_tendsto
    (d : ℕ) (ρ : Measure (Rd d)) (J : Rd d → ℝ≥0∞)
    (hJ : Measurable J) (hJfin : ∀ k, J k ≠ ∞) :
    Tendsto (fun n : ℕ => ∫⁻ k,
      heatSpectralWeight d ((1 / ((n : ℝ) + 1)) ^ 2) k * J k ∂ρ)
      atTop (𝓝 (∫⁻ k, J k ∂ρ)) := by
  have ht : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow two_ne_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun n => ((measurable_heatSpectralWeight d _).mul hJ).aemeasurable) ?_ ?_
  · refine Eventually.of_forall (fun k n m hnm => ?_)
    have hrecSq : (1 / ((m : ℝ) + 1)) ^ 2 ≤ (1 / ((n : ℝ) + 1)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2
        (one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.add_le_add_right hnm 1))
    exact mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right
          (neg_le_neg (mul_le_mul_of_nonneg_left hrecSq (by norm_num : (0 : ℝ) ≤ 2)))
            (sq_nonneg ‖k‖)))) (J k)
  · refine Eventually.of_forall (fun k => ?_)
    have hw : Tendsto (fun n : ℕ => heatSpectralWeight d ((1 / ((n : ℝ) + 1)) ^ 2) k)
        atTop (𝓝 (1 : ℝ≥0∞)) := by
      simpa only [heatSpectralWeight, Function.comp_def, mul_zero, neg_zero, zero_mul,
        Real.exp_zero, ENNReal.ofReal_one] using
          ((ENNReal.continuous_ofReal.comp
            (show Continuous (fun t : ℝ => Real.exp (-(2 * t) * ‖k‖ ^ 2)) from
              by fun_prop)).tendsto 0).comp ht
    simpa only [Function.comp_def, one_mul] using
      (ENNReal.continuous_mul_const (hJfin k)).continuousAt.tendsto.comp hw

theorem compactPositiveHeadPairTest_angularSpectrum_identity
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) :
    (∫⁻ k, compactAngularHeadJ d s χ k
      ∂originalAngularSpectrum d s hs P hP hW) ≠ ∞ ∧
    Integrable (fun k => (compactAngularHeadJ d s χ k).toReal)
      (originalAngularSpectrum d s hs P hP hW) ∧
    (∫ k, (compactAngularHeadJ d s χ k).toReal
      ∂originalAngularSpectrum d s hs P hP hW) =
      (∫ q, compactPositiveHeadPairTest d s hs χ q
        ∂originalAdmissibleFactorialMeasure d P hP) +
          (2 / s) * (∫ x : Rd d, (χ x) ^ 2 ∂volume) -
            ∫ q : Rd d × Rd d, compactPositiveHeadPairTest d s hs χ q
              ∂(volume : Measure (Rd d)).prod volume := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by positivity
  have hε : Tendsto ε atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let ρ := originalAngularSpectrum d s hs P hP hW
  let T0 : ℝ := (∫ q, compactPositiveHeadPairTest d s hs χ q
      ∂originalAdmissibleFactorialMeasure d P hP) +
        (2 / s) * (∫ x : Rd d, (χ x) ^ 2 ∂volume) -
          ∫ q : Rd d × Rd d, compactPositiveHeadPairTest d s hs χ q
            ∂(volume : Measure (Rd d)).prod volume
  let T : ℕ → ℝ := fun n => ∫ q : Rd d × Rd d,
    compactPositiveHeadPairTest d s hs χ q *
      originalHeatCovariance d P ((ε n) ^ 2) (q.2 - q.1)
        ∂(volume : Measure (Rd d)).prod volume
  have hphysical : Tendsto T atTop (𝓝 T0) :=
    (compactPositiveHeadPairTest_covariance_tendsto d s hs P hP hW χ hχ ε hεpos hε).2
  have hnonneg : 0 ≤ T0 :=
    ge_of_tendsto hphysical (Eventually.of_forall (fun n =>
      (integral_nonneg (fun k => ENNReal.toReal_nonneg)).trans_eq
        (compactPositiveHeadPairTest_heatSpectrum_integral d s hs P hP hW χ hχ
          ((ε n) ^ 2) (sq_pos_of_pos (hεpos n))).symm))
  have hvalue : (∫⁻ k, compactAngularHeadJ d s χ k ∂ρ) = ENNReal.ofReal T0 :=
    tendsto_nhds_unique
      (angularHead_heatWeight_sq_lintegral_tendsto d ρ (compactAngularHeadJ d s χ)
        (measurable_compactAngularHeadJ d s χ) (compactAngularHeadJ_ne_top d s hs χ hχ))
      ((ENNReal.tendsto_ofReal hphysical).congr' (Eventually.of_forall (fun n =>
        compactPositiveHeadPairTest_angularSpectrum_lintegral d s hs P hP hW χ hχ
          ((ε n) ^ 2) (sq_pos_of_pos (hεpos n)))))
  have hfinite : (∫⁻ k, compactAngularHeadJ d s χ k ∂ρ) ≠ ∞ :=
    hvalue.trans_ne ENNReal.ofReal_ne_top
  exact ⟨hfinite,
    integrable_toReal_of_lintegral_ne_top
      (measurable_compactAngularHeadJ d s χ).aemeasurable hfinite,
    (integral_toReal (measurable_compactAngularHeadJ d s χ).aemeasurable
      (ae_lt_top (measurable_compactAngularHeadJ d s χ) hfinite)).trans
        ((congrArg ENNReal.toReal hvalue).trans (ENNReal.toReal_ofReal hnonneg))⟩

end Riesz.Stationary
