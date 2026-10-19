import Riesz.Stationary.HeatSpectrumCompatibility
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Compact-pair Gaussian regularization for the original admissible law. -/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration
open scoped ENNReal Classical Topology CompactlySupported

namespace Riesz.Stationary

theorem originalAdmissible_boundedCount_memLp_two
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (K : Set (Rd d)) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K) :
    MemLp (fun μ : Measure (Rd d) => (μ K).toReal) 2 P := by
  have hmeas : Measurable (fun μ : Measure (Rd d) => μ K) := Measure.measurable_coe hK
  have hfinite : (∫⁻ μ : Measure (Rd d), (μ K) ^ 2 ∂P) ≠ ∞ :=
    (hP.2.2.2.2 K hK hKb).ne
  have hsq : Integrable (fun μ : Measure (Rd d) => (μ K).toReal ^ 2) P := by
    simpa only [ENNReal.toReal_pow] using
      integrable_toReal_of_lintegral_ne_top (hmeas.pow_const 2).aemeasurable hfinite
  exact (memLp_two_iff_integrable_sq hmeas.ennreal_toReal.aestronglyMeasurable).mpr hsq

def originalHeatEnvelope (d : ℕ) (K : Set (Rd d)) (A D T : ℝ) (x : Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal A * K.indicator (fun _ => (1 : ℝ≥0∞)) x +
    ENNReal.ofReal D * ENNReal.ofReal (originalHeatGaussian d T x)

theorem measurable_originalHeatEnvelope
    (d : ℕ) (K : Set (Rd d)) (hK : MeasurableSet K) (A D T : ℝ) :
    Measurable (originalHeatEnvelope d K A D T) := by
  exact (measurable_const.mul (measurable_const.indicator hK)).add
    (measurable_const.mul (continuous_originalHeatGaussian d T).measurable.ennreal_ofReal)

theorem lintegral_originalHeatEnvelope
    (d : ℕ) (K : Set (Rd d)) (hK : MeasurableSet K) (A D T : ℝ)
    (μ : Measure (Rd d)) :
    (∫⁻ x, originalHeatEnvelope d K A D T x ∂μ) =
      ENNReal.ofReal A * μ K + ENNReal.ofReal D * originalHeatMass d T 0 μ := by
  simp only [originalHeatEnvelope]
  rw [lintegral_add_left
    (f := fun x : Rd d => ENNReal.ofReal A * K.indicator (fun _ => (1 : ℝ≥0∞)) x)
    (measurable_const.mul (measurable_const.indicator hK)),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    show (∫⁻ x : Rd d, K.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) = μ K from
      lintegral_indicator_one hK]
  simp only [originalHeatMass, zero_sub, originalHeatGaussian_neg]

theorem originalHeatEnvelope_mass_memLp_two
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (K : Set (Rd d)) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (A D T : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hT : 0 < T)
    (hQ : Q d P (1 / (8 * T)) ≠ ∞) :
    MemLp (fun μ : Measure (Rd d) =>
      (∫⁻ x, originalHeatEnvelope d K A D T x ∂μ).toReal) 2 P ∧
      ∀ᵐ μ ∂P, (∫⁻ x, originalHeatEnvelope d K A D T x ∂μ) ≠ ∞ := by
  have haeC : ∀ᵐ μ : Measure (Rd d) ∂P, μ K ≠ ∞ :=
    (ae_lt_top ((Measure.measurable_coe hK).pow_const 2) (hP.2.2.2.2 K hK hKb).ne).mono
      (fun μ hμ => (ENNReal.pow_ne_top_iff.mp hμ.ne).resolve_right (by decide : ¬ (2 : ℕ) = 0))
  have haeG : ∀ᵐ μ ∂P, originalHeatMass d T 0 μ ≠ ∞ :=
    (ae_lt_top (measurable_originalHeatMass d T 0)
      ((lintegral_originalHeatMass d P hP T hT 0).trans_ne ENNReal.one_ne_top)).mono
        (fun _ hμ => hμ.ne)
  have haeFinite : ∀ᵐ μ ∂P, (∫⁻ x, originalHeatEnvelope d K A D T x ∂μ) ≠ ∞ :=
    (haeC.and haeG).mono (fun μ hμ =>
      (lintegral_originalHeatEnvelope d K hK A D T μ).trans_ne (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ.1,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ.2⟩))
  have haeReal : ∀ᵐ μ ∂P,
      (∫⁻ x, originalHeatEnvelope d K A D T x ∂μ).toReal =
        A * (μ K).toReal + D * (originalHeatMass d T 0 μ).toReal :=
    (haeC.and haeG).mono (fun μ hμ => by
      rw [lintegral_originalHeatEnvelope d K hK A D T μ,
        ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ.1)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ.2),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hD])
  exact ⟨(memLp_congr_ae haeReal).mpr
    (((originalAdmissible_boundedCount_memLp_two d P hP K hK hKb).const_mul A).add
      ((originalHeatMass_memLp_two d P hP T hT 0 hQ).const_mul D)), haeFinite⟩

theorem originalHeatEnvelope_pair_and_diagonal_ne_top
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (K : Set (Rd d)) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (A D T : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hT : 0 < T)
    (hQ : Q d P (1 / (8 * T)) ≠ ∞) :
    (∫⁻ p, originalHeatEnvelope d K A D T p.1 * originalHeatEnvelope d K A D T p.2
      ∂originalAdmissibleFactorialMeasure d P hP) ≠ ∞ ∧
      (∫⁻ x, (originalHeatEnvelope d K A D T x) ^ 2 ∂volume) ≠ ∞ := by
  let H := originalHeatEnvelope d K A D T
  have hMassMeas : Measurable (fun μ : Measure (Rd d) => ∫⁻ x, H x ∂μ) :=
    Measure.measurable_lintegral (measurable_originalHeatEnvelope d K hK A D T)
  obtain ⟨hL2, haeFinite⟩ := originalHeatEnvelope_mass_memLp_two
    d P hP K hK hKb A D T hA hD hT hQ
  have hSqAE : ∀ᵐ μ ∂P, (∫⁻ x, H x ∂μ) ^ 2 ≠ ∞ :=
    haeFinite.mono (fun _ hμ => ENNReal.pow_ne_top hμ)
  have hSqFinite : (∫⁻ μ, (∫⁻ x, H x ∂μ) ^ 2 ∂P) ≠ ∞ :=
    (integrable_toReal_iff (hMassMeas.pow_const 2).aemeasurable hSqAE).mp
      (by simpa only [ENNReal.toReal_pow] using hL2.integrable_sq)
  rw [originalAdmissible_mass_square_expectation d P hP H
    (measurable_originalHeatEnvelope d K hK A D T)] at hSqFinite
  exact ENNReal.add_ne_top.mp hSqFinite

theorem originalHeatEnvelope_pair_and_diagonal_ne_top_of_W
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (K : Set (Rd d)) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (A D T : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hT : 0 < T) :
    (∫⁻ p, originalHeatEnvelope d K A D T p.1 * originalHeatEnvelope d K A D T p.2
      ∂originalAdmissibleFactorialMeasure d P hP) ≠ ∞ ∧
      (∫⁻ x, (originalHeatEnvelope d K A D T x) ^ 2 ∂volume) ≠ ∞ := by
  exact originalHeatEnvelope_pair_and_diagonal_ne_top d P hP K hK hKb A D T
    hA hD hT (Q_ne_top_of_W_ne_top_pos d s hs P hW _ (by positivity))

theorem tendsto_compactPair_fixedGaussian_average
    (d : ℕ) (ψ : C_c(Rd d × Rd d, ℝ))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (z : Rd d × Rd d) :
    Tendsto (fun n => ∫ q : Rd d × Rd d,
      (originalHeatGaussian d 1 q.1 * originalHeatGaussian d 1 q.2) *
        ψ (z + ε n • q) ∂(volume : Measure (Rd d)).prod volume)
      atTop (𝓝 (ψ z)) := by
  let ν : Measure (Rd d × Rd d) := (volume : Measure (Rd d)).prod volume
  let φ : Rd d × Rd d → ℝ := fun q =>
    originalHeatGaussian d 1 q.1 * originalHeatGaussian d 1 q.2
  have hφnonneg (q : Rd d × Rd d) : 0 ≤ φ q := mul_nonneg
    (originalHeatGaussian_nonneg d 1 zero_lt_one q.1)
    (originalHeatGaussian_nonneg d 1 zero_lt_one q.2)
  have hφint : Integrable φ ν :=
    (integrable_originalHeatGaussian d 1 zero_lt_one).mul_prod
      (integrable_originalHeatGaussian d 1 zero_lt_one)
  have hφmass : (∫ q, φ q ∂ν) = 1 :=
    (integral_prod_mul (originalHeatGaussian d 1) (originalHeatGaussian d 1)).trans
      (by simp only [integral_originalHeatGaussian d 1 zero_lt_one, one_mul])
  have hshift (n : ℕ) : Continuous (fun q : Rd d × Rd d => z + ε n • q) :=
    continuous_const.add (continuous_id.const_smul (ε n))
  have hFmeas (n : ℕ) : AEStronglyMeasurable
      (fun q : Rd d × Rd d => φ q * ψ (z + ε n • q)) ν :=
    ((((continuous_originalHeatGaussian d 1).comp continuous_fst).mul
      ((continuous_originalHeatGaussian d 1).comp continuous_snd)).mul
        (ψ.continuous.comp (hshift n))).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ q ∂ν,
      ‖φ q * ψ (z + ε n • q)‖ ≤ φ q * ‖ψ.toBoundedContinuousFunction‖ :=
    Filter.Eventually.of_forall (fun q => by
      simpa only [norm_mul, Real.norm_of_nonneg (hφnonneg q),
        CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
        mul_le_mul_of_nonneg_left
          (ψ.toBoundedContinuousFunction.norm_coe_le_norm _) (hφnonneg q))
  have hz (q : Rd d × Rd d) : Tendsto (fun n => z + ε n • q) atTop (𝓝 z) := by
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds (x := z)).add (hε.smul_const q)
  have hpoint : ∀ᵐ q ∂ν,
      Tendsto (fun n => φ q * ψ (z + ε n • q)) atTop (𝓝 (φ q * ψ z)) :=
    Filter.Eventually.of_forall (fun q =>
      tendsto_const_nhds.mul (ψ.continuous.continuousAt.tendsto.comp (hz q)))
  simpa only [integral_mul_const, hφmass, one_mul] using
    (tendsto_integral_of_dominated_convergence (μ := ν)
      (fun q => φ q * ‖ψ.toBoundedContinuousFunction‖) hFmeas
      (hφint.mul_const ‖ψ.toBoundedContinuousFunction‖) hbound hpoint)

theorem originalHeatGaussian_square_smul
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) (v : Rd d) :
    originalHeatGaussian d (ε ^ 2) (ε • v) =
      (ε ^ d)⁻¹ * originalHeatGaussian d 1 v := by
  have hκ : (4 * Real.pi * ε ^ 2) ^ (-((d : ℝ) / 2)) =
      (ε ^ d)⁻¹ * (4 * Real.pi * 1) ^ (-((d : ℝ) / 2)) := by
    rw [mul_one, Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) (sq_nonneg ε),
      ← Real.rpow_natCast_mul hε.le 2 (-((d : ℝ) / 2)),
      Nat.cast_ofNat,
      show (2 : ℝ) * (-((d : ℝ) / 2)) = -(d : ℝ) by ring,
      Real.rpow_neg hε.le, Real.rpow_natCast, mul_comm]
  have he : -(1 / (4 * ε ^ 2)) * ‖ε • v‖ ^ 2 =
      -(1 / (4 * (1 : ℝ))) * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, mul_pow]
    field_simp [hε.ne']
  change (4 * Real.pi * ε ^ 2) ^ (-((d : ℝ) / 2)) *
      Real.exp (-(1 / (4 * ε ^ 2)) * ‖ε • v‖ ^ 2) =
    (ε ^ d)⁻¹ * ((4 * Real.pi * 1) ^ (-((d : ℝ) / 2)) *
      Real.exp (-(1 / (4 * (1 : ℝ))) * ‖v‖ ^ 2))
  rw [hκ, he, mul_assoc]

theorem integral_compactPair_heat_square_eq_fixedGaussian
    (d : ℕ) (ψ : C_c(Rd d × Rd d, ℝ)) (ε : ℝ) (hε : 0 < ε)
    (z : Rd d × Rd d) :
    (∫ q : Rd d × Rd d,
      (originalHeatGaussian d (ε ^ 2) (q.1 - z.1) *
        originalHeatGaussian d (ε ^ 2) (q.2 - z.2)) * ψ q
          ∂(volume : Measure (Rd d)).prod volume) =
      ∫ q : Rd d × Rd d,
        (originalHeatGaussian d 1 q.1 * originalHeatGaussian d 1 q.2) *
          ψ (z + ε • q) ∂(volume : Measure (Rd d)).prod volume := by
  let ν : Measure (Rd d × Rd d) := (volume : Measure (Rd d)).prod volume
  let F : Rd d × Rd d → ℝ := fun q =>
    (originalHeatGaussian d (ε ^ 2) (q.1 - z.1) *
      originalHeatGaussian d (ε ^ 2) (q.2 - z.2)) * ψ q
  have hJ : ((ε ^ d)⁻¹) ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero (pow_ne_zero d hε.ne'))
  have hJac : |(ε ^ Module.finrank ℝ (Rd d × Rd d))⁻¹| = ((ε ^ d)⁻¹) ^ 2 := by
    simp only [Module.finrank_prod, Rd, finrank_euclideanSpace_fin, pow_add,
      mul_inv_rev, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hε d)), pow_two]
  have hscale : (∫ q, F (z + ε • q) ∂ν) =
      |(ε ^ Module.finrank ℝ (Rd d × Rd d))⁻¹| * ∫ q, F (z + q) ∂ν := by
    simpa only [smul_eq_mul] using
      Measure.integral_comp_smul ν (fun q => F (z + q)) ε
  have hchange : (∫ q, F (z + ε • q) ∂ν) = ((ε ^ d)⁻¹) ^ 2 * ∫ q, F q ∂ν := by
    simpa only [hJac, integral_add_left_eq_self F z] using hscale
  have hpoint (q : Rd d × Rd d) : F (z + ε • q) =
      ((ε ^ d)⁻¹) ^ 2 * ((originalHeatGaussian d 1 q.1 * originalHeatGaussian d 1 q.2) *
        ψ (z + ε • q)) := by
    change ((originalHeatGaussian d (ε ^ 2) ((z.1 + ε • q.1) - z.1)) *
      originalHeatGaussian d (ε ^ 2) ((z.2 + ε • q.2) - z.2)) * _ = _
    rw [add_sub_cancel_left, add_sub_cancel_left,
      originalHeatGaussian_square_smul d ε hε q.1,
      originalHeatGaussian_square_smul d ε hε q.2]
    ring
  have hscaled : (∫ q, F (z + ε • q) ∂ν) = ((ε ^ d)⁻¹) ^ 2 *
      ∫ q, (originalHeatGaussian d 1 q.1 * originalHeatGaussian d 1 q.2) *
        ψ (z + ε • q) ∂ν :=
    (integral_congr_ae (Filter.Eventually.of_forall hpoint)).trans (integral_const_mul _ _)
  exact mul_left_cancel₀ hJ (hchange.symm.trans hscaled)

theorem tendsto_compactPair_heat_of_square_scale
    (d : ℕ) (ψ : C_c(Rd d × Rd d, ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (z : Rd d × Rd d) :
    Tendsto (fun n => ∫ q : Rd d × Rd d,
      (originalHeatGaussian d ((ε n) ^ 2) (q.1 - z.1) *
        originalHeatGaussian d ((ε n) ^ 2) (q.2 - z.2)) * ψ q
          ∂(volume : Measure (Rd d)).prod volume) atTop (𝓝 (ψ z)) := by
  exact (tendsto_compactPair_fixedGaussian_average d ψ ε hε z).congr'
    (Filter.Eventually.of_forall (fun n =>
      (integral_compactPair_heat_square_eq_fixedGaussian d ψ (ε n) (hεpos n) z).symm))

def compactPairHeatRegularization (d : ℕ) (t : ℝ)
    (ψ : C_c(Rd d × Rd d, ℝ)) (z : Rd d × Rd d) : ℝ≥0∞ :=
  ∫⁻ q : Rd d × Rd d,
    (ENNReal.ofReal (originalHeatGaussian d t (q.1 - z.1)) *
      ENNReal.ofReal (originalHeatGaussian d t (q.2 - z.2))) * ENNReal.ofReal (ψ q)
        ∂(volume : Measure (Rd d)).prod volume

theorem measurable_compactPairHeatRegularization
    (d : ℕ) (t : ℝ) (ψ : C_c(Rd d × Rd d, ℝ)) :
    Measurable (compactPairHeatRegularization d t ψ) := by
  have hK : Measurable (fun r : (Rd d × Rd d) × (Rd d × Rd d) =>
      (ENNReal.ofReal (originalHeatGaussian d t (r.2.1 - r.1.1)) *
        ENNReal.ofReal (originalHeatGaussian d t (r.2.2 - r.1.2))) *
          ENNReal.ofReal (ψ r.2)) :=
    ((((continuous_originalHeatGaussian d t).comp
      ((continuous_fst.comp continuous_snd).sub
        (continuous_fst.comp continuous_fst))).measurable.ennreal_ofReal).mul
      (((continuous_originalHeatGaussian d t).comp
        ((continuous_snd.comp continuous_snd).sub
          (continuous_snd.comp continuous_fst))).measurable.ennreal_ofReal)).mul
            (ψ.continuous.comp continuous_snd).measurable.ennreal_ofReal
  exact hK.lintegral_prod_right'

theorem compactPairHeatRegularization_eq_ofReal_integral
    (d : ℕ) (t : ℝ) (ht : 0 < t) (ψ : C_c(Rd d × Rd d, ℝ))
    (hψ : ∀ q, 0 ≤ ψ q) (z : Rd d × Rd d) :
    compactPairHeatRegularization d t ψ z =
      ENNReal.ofReal (∫ q : Rd d × Rd d,
        (originalHeatGaussian d t (q.1 - z.1) *
          originalHeatGaussian d t (q.2 - z.2)) * ψ q
            ∂(volume : Measure (Rd d)).prod volume) := by
  let ρ : Rd d × Rd d → ℝ := fun q =>
    originalHeatGaussian d t (q.1 - z.1) * originalHeatGaussian d t (q.2 - z.2)
  have hmean (a : Rd d) : (∫ x : Rd d, originalHeatGaussian d t (x - a) ∂volume) = 1 :=
    (integral_sub_right_eq_self (originalHeatGaussian d t) a).trans
      (integral_originalHeatGaussian d t ht)
  have hρint : Integrable ρ ((volume : Measure (Rd d)).prod volume) :=
    (integrable_of_integral_eq_one (hmean z.1)).mul_prod
      (integrable_of_integral_eq_one (hmean z.2))
  have hρnonneg (q : Rd d × Rd d) : 0 ≤ ρ q := mul_nonneg
    (originalHeatGaussian_nonneg d t ht (q.1 - z.1))
    (originalHeatGaussian_nonneg d t ht (q.2 - z.2))
  have hFint : Integrable (fun q => ρ q * ψ q)
      ((volume : Measure (Rd d)).prod volume) :=
    hρint.mul_bdd ψ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => by
        simpa only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
          ψ.toBoundedContinuousFunction.norm_coe_le_norm q))
  have hOf (q : Rd d × Rd d) : ENNReal.ofReal (ρ q * ψ q) =
      (ENNReal.ofReal (originalHeatGaussian d t (q.1 - z.1)) *
        ENNReal.ofReal (originalHeatGaussian d t (q.2 - z.2))) * ENNReal.ofReal (ψ q) :=
    (ENNReal.ofReal_mul (hρnonneg q)).trans
      (congrArg (fun x => x * ENNReal.ofReal (ψ q))
        (ENNReal.ofReal_mul (originalHeatGaussian_nonneg d t ht (q.1 - z.1))))
  exact ((ofReal_integral_eq_lintegral_ofReal hFint
    (Filter.Eventually.of_forall (fun q => mul_nonneg (hρnonneg q) (hψ q)))).trans
      (lintegral_congr hOf)).symm

theorem compactPairHeatRegularization_ne_top
    (d : ℕ) (t : ℝ) (ht : 0 < t) (ψ : C_c(Rd d × Rd d, ℝ))
    (hψ : ∀ q, 0 ≤ ψ q) (z : Rd d × Rd d) :
    compactPairHeatRegularization d t ψ z ≠ ∞ :=
  (compactPairHeatRegularization_eq_ofReal_integral d t ht ψ hψ z).trans_ne
    ENNReal.ofReal_ne_top

theorem tendsto_compactPairHeatRegularization_of_square_scale
    (d : ℕ) (ψ : C_c(Rd d × Rd d, ℝ)) (hψ : ∀ q, 0 ≤ ψ q)
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (z : Rd d × Rd d) :
    Tendsto (fun n => compactPairHeatRegularization d ((ε n) ^ 2) ψ z)
      atTop (𝓝 (ENNReal.ofReal (ψ z))) := by
  exact (ENNReal.tendsto_ofReal
    (tendsto_compactPair_heat_of_square_scale d ψ ε hεpos hε z)).congr'
      (Filter.Eventually.of_forall (fun n =>
        (compactPairHeatRegularization_eq_ofReal_integral d ((ε n) ^ 2)
          (sq_pos_of_pos (hεpos n)) ψ hψ z).symm))

theorem exists_rpow_mul_exp_neg_bound
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ → τ ^ r * Real.exp (-τ) ≤ C := by
  have hf : Continuous (fun τ : ℝ => τ ^ r * Real.exp (-τ)) :=
    (Real.continuous_rpow_const hr).mul (Real.continuous_exp.comp continuous_neg)
  have hlim : Tendsto (fun τ : ℝ => τ ^ r * Real.exp (-τ)) atTop (𝓝 0) := by
    simpa only [one_mul, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero r 1 zero_lt_one
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hlim.eventually (gt_mem_nhds zero_lt_one))
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (max N 0))).bddAbove_image
    hf.continuousOn
  exact ⟨max 1 B, le_trans zero_le_one (le_max_left _ _), fun τ hτ =>
    if hτN : τ ≤ max N 0 then
      (hB ⟨τ, ⟨hτ, hτN⟩, rfl⟩).trans (le_max_right _ _)
    else (hN τ ((le_max_left N 0).trans (le_of_not_ge hτN))).le.trans (le_max_left _ _)⟩

theorem exists_uniform_far_heatGaussian_bound
    (d : ℕ) (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ a x : Rd d,
      1 ≤ ‖x‖ → ‖x‖ / 2 ≤ ‖a - x‖ →
        originalHeatGaussian d t (a - x) ≤ D * originalHeatGaussian d (8 * t₀) x := by
  let r : ℝ := (d : ℝ) / 2
  obtain ⟨C, hC, hCbound⟩ := exists_rpow_mul_exp_neg_bound r (by positivity)
  let B : ℝ := (32 : ℝ) ^ r * C
  let c₀ : ℝ := (4 * Real.pi) ^ (-r)
  let κ : ℝ := (4 * Real.pi * (8 * t₀)) ^ (-r)
  have hκ : 0 < κ := by positivity
  have hfactor (t : ℝ) (ht : 0 < t) :
      t ^ (-r) * Real.exp (-(1 / (32 * t))) ≤ B := by
    have hp : t ^ (-r) = (32 : ℝ) ^ r * (1 / (32 * t)) ^ r := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) (by positivity : 0 ≤ 1 / (32 * t)),
        show (32 : ℝ) * (1 / (32 * t)) = t⁻¹ by field_simp [ht.ne'],
        Real.inv_rpow ht.le, Real.rpow_neg ht.le]
    simpa only [hp, B, mul_assoc] using
      mul_le_mul_of_nonneg_left (hCbound (1 / (32 * t)) (by positivity))
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 32) r)
  refine ⟨c₀ * B / κ, by positivity, fun t ht htt₀ a x hx hax => ?_⟩
  have hsq : ‖x‖ ^ 2 ≤ 4 * ‖a - x‖ ^ 2 := by
    nlinarith [norm_nonneg x, norm_nonneg (a - x)]
  have hx2 : 1 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hpoly : t₀ + t * ‖x‖ ^ 2 ≤ 8 * t₀ * ‖a - x‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq ht₀.le,
      mul_le_mul_of_nonneg_right htt₀ (sq_nonneg ‖x‖),
      mul_le_mul_of_nonneg_left hx2 ht₀.le]
  have hExp : -(1 / (4 * t)) * ‖a - x‖ ^ 2 ≤
      -(1 / (32 * t)) + -(1 / (32 * t₀)) * ‖x‖ ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right (show 0 < 32 * t * t₀ by positivity)).mp
    field_simp [ht.ne', ht₀.ne']
    nlinarith only [hpoly]
  have hκt : (4 * Real.pi * t) ^ (-r) = c₀ * t ^ (-r) :=
    Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) ht.le
  have hTform : originalHeatGaussian d (8 * t₀) x =
      κ * Real.exp (-(1 / (32 * t₀)) * ‖x‖ ^ 2) := by
    simp only [originalHeatGaussian, κ, r, show 4 * (8 * t₀) = 32 * t₀ by ring]
  have hle : originalHeatGaussian d t (a - x) ≤
      (c₀ * t ^ (-r)) * Real.exp (-(1 / (32 * t)) + -(1 / (32 * t₀)) * ‖x‖ ^ 2) := by
    simpa only [originalHeatGaussian, ← hκt] using
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp)
        (show 0 ≤ c₀ * t ^ (-r) by positivity)
  have hexpand : (c₀ * t ^ (-r)) *
      Real.exp (-(1 / (32 * t)) + -(1 / (32 * t₀)) * ‖x‖ ^ 2) =
      c₀ * (t ^ (-r) * Real.exp (-(1 / (32 * t)))) *
        Real.exp (-(1 / (32 * t₀)) * ‖x‖ ^ 2) := by
    rw [Real.exp_add, mul_assoc, mul_assoc, mul_assoc]
  have hlast : c₀ * B * Real.exp (-(1 / (32 * t₀)) * ‖x‖ ^ 2) =
      c₀ * B / κ * originalHeatGaussian d (8 * t₀) x := by
    rw [hTform]
    field_simp [hκ.ne']
  exact ((hle.trans_eq hexpand).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hfactor t ht) (by positivity : 0 ≤ c₀))
      (Real.exp_pos _).le)).trans_eq hlast

def nonnegativeHeatWindow (d : ℕ) (t : ℝ) (f : Rd d → ℝ≥0∞) (x : Rd d) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal (originalHeatGaussian d t (a - x)) * f a ∂volume

theorem nonnegativeHeatWindow_le_const
    (d : ℕ) (t : ℝ) (ht : 0 < t) (f : Rd d → ℝ≥0∞)
    (M : ℝ) (hbound : ∀ a, f a ≤ ENNReal.ofReal M) (x : Rd d) :
    nonnegativeHeatWindow d t f x ≤ ENNReal.ofReal M := by
  have hp : Measurable (fun a : Rd d =>
      ENNReal.ofReal (originalHeatGaussian d t (a - x))) :=
    ((continuous_originalHeatGaussian d t).comp
      (continuous_id.sub continuous_const)).measurable.ennreal_ofReal
  have hnorm : (∫⁻ a, ENNReal.ofReal (originalHeatGaussian d t (a - x)) ∂volume) = 1 :=
    (lintegral_sub_right_eq_self
      (fun a : Rd d => ENNReal.ofReal (originalHeatGaussian d t a)) x).trans
        (lintegral_originalHeatGaussian_unshifted d t ht)
  exact (lintegral_mono (fun a => mul_le_mul_right (hbound a) _)).trans_eq
    ((lintegral_mul_const (ENNReal.ofReal M) hp).trans (by rw [hnorm, one_mul]))

theorem exists_uniform_nonnegativeHeatWindow_envelope
    (d : ℕ) (t₀ : ℝ) (ht₀ : 0 < t₀) (f : Rd d → ℝ≥0∞)
    (M R : ℝ) (_hM : 0 ≤ M) (hR : 1 ≤ R)
    (hbound : ∀ a, f a ≤ ENNReal.ofReal M)
    (hsupp : ∀ a, R < ‖a‖ → f a = 0)
    (hfin : (∫⁻ a, f a ∂volume) ≠ ∞) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ x : Rd d,
      nonnegativeHeatWindow d t f x ≤
        originalHeatEnvelope d (Metric.closedBall 0 (2 * R)) M D (8 * t₀) x := by
  obtain ⟨D₀, hD₀, hfar⟩ := exists_uniform_far_heatGaussian_bound d t₀ ht₀
  let A : ℝ≥0∞ := ∫⁻ a, f a ∂volume
  have hDcoef : ENNReal.ofReal (D₀ * A.toReal) = ENNReal.ofReal D₀ * A := by
    rw [ENNReal.ofReal_mul hD₀, ENNReal.ofReal_toReal hfin]
  refine ⟨D₀ * A.toReal, mul_nonneg hD₀ ENNReal.toReal_nonneg, fun t ht htt₀ x => ?_⟩
  by_cases hx : x ∈ Metric.closedBall (0 : Rd d) (2 * R)
  · simpa only [originalHeatEnvelope, Set.indicator_of_mem hx, mul_one] using
      (nonnegativeHeatWindow_le_const d t ht f M hbound x).trans
        (le_add_of_nonneg_right (show 0 ≤ ENNReal.ofReal (D₀ * A.toReal) *
          ENNReal.ofReal (originalHeatGaussian d (8 * t₀) x) from bot_le))
  · have hxnorm : 2 * R < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hxone : 1 ≤ ‖x‖ := by linarith
    have hpoint (a : Rd d) :
        ENNReal.ofReal (originalHeatGaussian d t (a - x)) * f a ≤
          (ENNReal.ofReal D₀ * ENNReal.ofReal (originalHeatGaussian d (8 * t₀) x)) * f a := by
      by_cases ha : R < ‖a‖
      · simp only [hsupp a ha, mul_zero, le_refl]
      · have hatri : ‖x‖ ≤ ‖a‖ + ‖a - x‖ := by
          simpa only [sub_sub_cancel] using (norm_sub_le a (a - x))
        have hdist : ‖x‖ / 2 ≤ ‖a - x‖ := by linarith [le_of_not_gt ha]
        exact mul_le_mul_left
          ((ENNReal.ofReal_le_ofReal (hfar t ht htt₀ a x hxone hdist)).trans_eq
            (ENNReal.ofReal_mul hD₀)) (f a)
    have hle : nonnegativeHeatWindow d t f x ≤
        ENNReal.ofReal (D₀ * A.toReal) * ENNReal.ofReal (originalHeatGaussian d (8 * t₀) x) :=
      (lintegral_mono hpoint).trans_eq
        ((lintegral_const_mul' _ f
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).trans
            (by rw [hDcoef, mul_right_comm]))
    simpa only [originalHeatEnvelope, Set.indicator_of_notMem hx, mul_zero, zero_add] using hle

theorem compactPairHeatRegularization_le_heatWindow_product
    (d : ℕ) (t : ℝ) (ψ : C_c(Rd d × Rd d, ℝ))
    (f : Rd d → ℝ≥0∞) (hf : Measurable f) (B : ℝ)
    (hψbound : ∀ q : Rd d × Rd d,
      ENNReal.ofReal (ψ q) ≤ ENNReal.ofReal B * (f q.1 * f q.2))
    (z : Rd d × Rd d) :
    compactPairHeatRegularization d t ψ z ≤ ENNReal.ofReal B *
      (nonnegativeHeatWindow d t f z.1 * nonnegativeHeatWindow d t f z.2) := by
  let c : Rd d → ℝ≥0∞ := fun a =>
    ENNReal.ofReal (originalHeatGaussian d t (a - z.1)) * f a
  let e : Rd d → ℝ≥0∞ := fun b =>
    ENNReal.ofReal (originalHeatGaussian d t (b - z.2)) * f b
  have hc : Measurable c := (((continuous_originalHeatGaussian d t).comp
    (continuous_id.sub continuous_const)).measurable.ennreal_ofReal).mul hf
  have he : Measurable e := (((continuous_originalHeatGaussian d t).comp
    (continuous_id.sub continuous_const)).measurable.ennreal_ofReal).mul hf
  have hpoint (q : Rd d × Rd d) :
      (ENNReal.ofReal (originalHeatGaussian d t (q.1 - z.1)) *
        ENNReal.ofReal (originalHeatGaussian d t (q.2 - z.2))) * ENNReal.ofReal (ψ q) ≤
      ENNReal.ofReal B * (c q.1 * e q.2) :=
    (mul_le_mul_right (hψbound q) _).trans_eq
      (by simp only [c, e, mul_assoc, mul_comm, mul_left_comm])
  exact (lintegral_mono hpoint).trans_eq
    ((lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
      (congrArg (fun x => ENNReal.ofReal B * x)
        (lintegral_prod_mul hc.aemeasurable he.aemeasurable)))

theorem compactPairHeatRegularization_originalGamma_tendsto
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (ψ : C_c(Rd d × Rd d, ℝ)) (hψ : ∀ q, 0 ≤ ψ q)
    (f : Rd d → ℝ≥0∞) (hf : Measurable f)
    (M R B : ℝ) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hbound : ∀ a, f a ≤ ENNReal.ofReal M)
    (hsupp : ∀ a, R < ‖a‖ → f a = 0)
    (hfin : (∫⁻ a, f a ∂volume) ≠ ∞)
    (hψbound : ∀ q : Rd d × Rd d,
      ENNReal.ofReal (ψ q) ≤ ENNReal.ofReal B * (f q.1 * f q.2))
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    (∫⁻ q, ENNReal.ofReal (ψ q) ∂originalAdmissibleFactorialMeasure d P hP) ≠ ∞ ∧
      (∫⁻ x, ENNReal.ofReal (ψ (x, x)) ∂volume) ≠ ∞ ∧
      Tendsto (fun n => ∫⁻ q, compactPairHeatRegularization d ((ε n) ^ 2) ψ q
        ∂originalAdmissibleFactorialMeasure d P hP) atTop
          (𝓝 (∫⁻ q, ENNReal.ofReal (ψ q) ∂originalAdmissibleFactorialMeasure d P hP)) ∧
      Tendsto (fun n => ∫⁻ x, compactPairHeatRegularization d ((ε n) ^ 2) ψ (x, x) ∂volume)
        atTop (𝓝 (∫⁻ x, ENNReal.ofReal (ψ (x, x)) ∂volume)) := by
  let Γ := originalAdmissibleFactorialMeasure d P hP
  obtain ⟨D, hD, hEnv⟩ := exists_uniform_nonnegativeHeatWindow_envelope
    d 1 zero_lt_one f M R hM hR hbound hsupp hfin
  simp only [mul_one] at hEnv
  let H := originalHeatEnvelope d (Metric.closedBall (0 : Rd d) (2 * R)) M D 8
  obtain ⟨hΓH, hdiagH⟩ := originalHeatEnvelope_pair_and_diagonal_ne_top_of_W
    d s hs P hP hW (Metric.closedBall 0 (2 * R)) measurableSet_closedBall
      Metric.isBounded_closedBall M D 8 hM hD (by norm_num)
  have hΓbound : (∫⁻ q, ENNReal.ofReal B * (H q.1 * H q.2) ∂Γ) ≠ ∞ :=
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans_ne
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΓH)
  have hdiagbound : (∫⁻ x, ENNReal.ofReal B * (H x) ^ 2 ∂volume) ≠ ∞ :=
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans_ne
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdiagH)
  have htend : Tendsto (fun n => (ε n) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow two_ne_zero] using hε.pow 2
  have hsmall : ∀ᶠ n in atTop, (ε n) ^ 2 ≤ 1 :=
    (htend.eventually (Iio_mem_nhds zero_lt_one)).mono (fun _ hn => hn.le)
  have hdom (n : ℕ) (hn : (ε n) ^ 2 ≤ 1) (z : Rd d × Rd d) :
      compactPairHeatRegularization d ((ε n) ^ 2) ψ z ≤
        ENNReal.ofReal B * (H z.1 * H z.2) :=
    (compactPairHeatRegularization_le_heatWindow_product d ((ε n) ^ 2) ψ f hf B hψbound z).trans
      (mul_le_mul_right (mul_le_mul'
        (hEnv ((ε n) ^ 2) (sq_pos_of_pos (hεpos n)) hn z.1)
        (hEnv ((ε n) ^ 2) (sq_pos_of_pos (hεpos n)) hn z.2)) (ENNReal.ofReal B))
  have hpoint (z : Rd d × Rd d) :=
    tendsto_compactPairHeatRegularization_of_square_scale d ψ hψ ε hεpos hε z
  have htarget (z : Rd d × Rd d) :
      ENNReal.ofReal (ψ z) ≤ ENNReal.ofReal B * (H z.1 * H z.2) :=
    le_of_tendsto (hpoint z) (hsmall.mono (fun n hn => hdom n hn z))
  refine ⟨ne_top_of_le_ne_top hΓbound (lintegral_mono htarget),
    ne_top_of_le_ne_top hdiagbound (lintegral_mono (fun x => by
      simpa only [pow_two] using htarget (x, x))), ?_, ?_⟩
  · exact tendsto_lintegral_filter_of_dominated_convergence (μ := Γ)
      (fun q => ENNReal.ofReal B * (H q.1 * H q.2))
      (Filter.Eventually.of_forall (fun n => measurable_compactPairHeatRegularization d _ ψ))
      (hsmall.mono (fun n hn => Filter.Eventually.of_forall (hdom n hn)))
      hΓbound (Filter.Eventually.of_forall hpoint)
  · exact tendsto_lintegral_filter_of_dominated_convergence (μ := (volume : Measure (Rd d)))
      (fun x => ENNReal.ofReal B * (H x) ^ 2)
      (Filter.Eventually.of_forall (fun n =>
        (measurable_compactPairHeatRegularization d ((ε n) ^ 2) ψ).comp
          (measurable_id.prodMk measurable_id)))
      (hsmall.mono (fun n hn => Filter.Eventually.of_forall (fun x => by
        simpa only [pow_two] using hdom n hn (x, x))))
      hdiagbound (Filter.Eventually.of_forall (fun x => hpoint (x, x)))

theorem positiveHeadWeight_integrable_and_integral (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => u ^ (s / 2 - 1)) (Set.Ioc 0 1) ∧
      (∫ u : ℝ in Set.Ioc 0 1, u ^ (s / 2 - 1)) = 2 / s := by
  refine ⟨?_, ?_⟩
  · rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  · rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith : -1 < s / 2 - 1))]
    simp only [sub_add_cancel, Real.one_rpow,
      Real.zero_rpow (by linarith : s / 2 ≠ 0), sub_zero]
    field_simp

def positiveHeadKernel (d : ℕ) (s : ℝ) (z : Rd d) : ℝ :=
  ∫ u : ℝ in Set.Ioc 0 1,
    u ^ (s / 2 - 1) * Real.exp (-(u * ‖z‖ ^ (2 : ℕ)))

theorem positiveHeadKernel_continuous_and_bounds
    (d : ℕ) (s : ℝ) (hs : 0 < s) :
    Continuous (positiveHeadKernel d s) ∧
      (∀ z, 0 ≤ positiveHeadKernel d s z ∧ positiveHeadKernel d s z ≤ 2 / s) ∧
      positiveHeadKernel d s 0 = 2 / s := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let w : ℝ → ℝ := fun u => u ^ (s / 2 - 1)
  let F : Rd d → ℝ → ℝ := fun z u => w u * Real.exp (-(u * ‖z‖ ^ (2 : ℕ)))
  obtain ⟨hwint, hwmass⟩ := positiveHeadWeight_integrable_and_integral s hs
  have hFm (z : Rd d) : AEStronglyMeasurable (F z) ν :=
    (((measurable_id.pow_const (s / 2 - 1)).mul
      (measurable_id.mul measurable_const).neg.exp).aestronglyMeasurable)
  have hpos (z : Rd d) : ∀ᵐ u ∂ν, 0 ≤ F z u :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun u hu =>
      mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.exp_pos _).le)
  have hle (z : Rd d) : ∀ᵐ u ∂ν, F z u ≤ w u :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun u hu =>
      mul_le_of_le_one_right (Real.rpow_nonneg hu.1.le _)
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr
          (mul_nonneg hu.1.le (sq_nonneg ‖z‖)))))
  have hnorm (z : Rd d) : ∀ᵐ u ∂ν, ‖F z u‖ ≤ w u :=
    ((hpos z).and (hle z)).mono (fun u hu => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hu.1] using hu.2)
  have hFint (z : Rd d) : Integrable (F z) ν := hwint.mono' (hFm z) (hnorm z)
  have hcont : ∀ᵐ u ∂ν, Continuous (fun z : Rd d => F z u) :=
    Filter.Eventually.of_forall (fun u => continuous_const.mul (Real.continuous_exp.comp
      ((continuous_const.mul (continuous_id.norm.pow 2)).neg)))
  refine ⟨continuous_of_dominated hFm hnorm hwint hcont, ?_, ?_⟩
  · exact fun z => ⟨integral_nonneg_of_ae (hpos z),
      (integral_mono_ae (hFint z) hwint (hle z)).trans_eq hwmass⟩
  · simpa only [positiveHeadKernel, norm_zero, zero_pow two_ne_zero,
      mul_zero, neg_zero, Real.exp_zero, mul_one] using hwmass

def compactPositiveHeadPairTest
    (d : ℕ) (s : ℝ) (hs : 0 < s) (χ : C_c(Rd d, ℝ)) : C_c(Rd d × Rd d, ℝ) :=
  ⟨⟨fun p => compactWindowPairAnchor d χ p * positiveHeadKernel d s (p.2 - p.1),
    (compactWindowPairAnchor d χ).continuous.mul
      ((positiveHeadKernel_continuous_and_bounds d s hs).1.comp
        (continuous_snd.sub continuous_fst))⟩,
      (compactWindowPairAnchor d χ).hasCompactSupport.mul_right⟩

theorem compactPositiveHeadPairTest_nonneg_and_bound
    (d : ℕ) (s : ℝ) (hs : 0 < s) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (p : Rd d × Rd d) :
    0 ≤ compactPositiveHeadPairTest d s hs χ p ∧
      ENNReal.ofReal (compactPositiveHeadPairTest d s hs χ p) ≤
        ENNReal.ofReal (2 / s) * (ENNReal.ofReal (χ p.1) * ENNReal.ofReal (χ p.2)) := by
  obtain ⟨hk0, hkle⟩ := (positiveHeadKernel_continuous_and_bounds d s hs).2.1 (p.2 - p.1)
  have hc0 : 0 ≤ χ p.1 * χ p.2 := mul_nonneg (hχ p.1) (hχ p.2)
  refine ⟨mul_nonneg hc0 hk0, ?_⟩
  have hreal : compactPositiveHeadPairTest d s hs χ p ≤ (2 / s) * (χ p.1 * χ p.2) := by
    exact (mul_le_mul_of_nonneg_left hkle hc0).trans_eq (mul_comm _ _)
  exact (ENNReal.ofReal_le_ofReal hreal).trans_eq (by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / s), ENNReal.ofReal_mul (hχ p.1)])

theorem compactPositiveHeadPairTest_diagonal
    (d : ℕ) (s : ℝ) (hs : 0 < s) (χ : C_c(Rd d, ℝ)) (x : Rd d) :
    compactPositiveHeadPairTest d s hs χ (x, x) = (2 / s) * (χ x) ^ 2 := by
  change χ x * χ x * positiveHeadKernel d s (x - x) = (2 / s) * (χ x) ^ 2
  simp only [sub_self, (positiveHeadKernel_continuous_and_bounds d s hs).2.2,
    pow_two, mul_comm]

theorem compactPositiveHeadPairTest_originalGamma_tendsto
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    (∫⁻ q, ENNReal.ofReal (compactPositiveHeadPairTest d s hs χ q)
      ∂originalAdmissibleFactorialMeasure d P hP) ≠ ∞ ∧
      (∫⁻ x, ENNReal.ofReal (compactPositiveHeadPairTest d s hs χ (x, x))
        ∂volume) ≠ ∞ ∧
      Tendsto (fun n => ∫⁻ q, compactPairHeatRegularization d ((ε n) ^ 2)
        (compactPositiveHeadPairTest d s hs χ) q
          ∂originalAdmissibleFactorialMeasure d P hP) atTop
        (𝓝 (∫⁻ q, ENNReal.ofReal (compactPositiveHeadPairTest d s hs χ q)
          ∂originalAdmissibleFactorialMeasure d P hP)) ∧
      Tendsto (fun n => ∫⁻ x, compactPairHeatRegularization d ((ε n) ^ 2)
        (compactPositiveHeadPairTest d s hs χ) (x, x) ∂volume) atTop
        (𝓝 (∫⁻ x, ENNReal.ofReal (compactPositiveHeadPairTest d s hs χ (x, x))
          ∂volume)) := by
  obtain ⟨R, hR, hRsupp⟩ :=
    χ.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 1 (0 : Rd d)
  have hbound (a : Rd d) : ENNReal.ofReal (χ a) ≤
      ENNReal.ofReal ‖χ.toBoundedContinuousFunction‖ :=
    ENNReal.ofReal_le_ofReal ((le_abs_self (χ a)).trans (by
      simpa only [Real.norm_eq_abs,
        CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
          χ.toBoundedContinuousFunction.norm_coe_le_norm a))
  have hsupp (a : Rd d) (ha : R < ‖a‖) : ENNReal.ofReal (χ a) = 0 := by
    have hz : χ a = 0 := by
      by_contra hne
      exact (not_le_of_gt ha) (by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          hRsupp (subset_tsupport χ hne))
    simp only [hz, ENNReal.ofReal_zero]
  have hχint : Integrable χ volume :=
    χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport
  have hfin : (∫⁻ a, ENNReal.ofReal (χ a) ∂volume) ≠ ∞ :=
    (ofReal_integral_eq_lintegral_ofReal hχint (Filter.Eventually.of_forall hχ)).symm.trans_ne
      ENNReal.ofReal_ne_top
  exact compactPairHeatRegularization_originalGamma_tendsto d s hs P hP hW
    (compactPositiveHeadPairTest d s hs χ)
    (fun q => (compactPositiveHeadPairTest_nonneg_and_bound d s hs χ hχ q).1)
    (fun a => ENNReal.ofReal (χ a)) χ.continuous.measurable.ennreal_ofReal
    ‖χ.toBoundedContinuousFunction‖ R (2 / s) (norm_nonneg _) hR.le hbound hsupp hfin
    (fun q => (compactPositiveHeadPairTest_nonneg_and_bound d s hs χ hχ q).2)
    ε hεpos hε

theorem originalHeatPairProfile_eq_shifted_pair_lintegral
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a b : Rd d) :
    originalHeatPairProfile d P hP t (b - a) =
      ∫⁻ z, ENNReal.ofReal (originalHeatGaussian d t (a - z.1)) *
        ENNReal.ofReal (originalHeatGaussian d t (b - z.2))
          ∂originalAdmissibleFactorialMeasure d P hP := by
  let Γ := originalAdmissibleFactorialMeasure d P hP
  let F : Rd d × Rd d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (originalHeatGaussian d t (-z.1)) *
      ENNReal.ofReal (originalHeatGaussian d t ((b - a) - z.2))
  have hF : Measurable F :=
    (((continuous_originalHeatGaussian d t).comp
      continuous_fst.neg).measurable.ennreal_ofReal).mul
        (((continuous_originalHeatGaussian d t).comp
          (continuous_const.sub continuous_snd)).measurable.ennreal_ofReal)
  have hT : Measurable (fun z : Rd d × Rd d => (-a + z.1, -a + z.2)) :=
    (measurable_const.add measurable_fst).prodMk
      (measurable_const.add measurable_snd)
  have htrans := lintegral_map (μ := Γ) hF hT
  rw [originalAdmissibleFactorialMeasure_map_diagAdd_eq_self d P hP (-a)] at htrans
  refine (originalHeatPairProfile_eq_pair_lintegral d P hP t ht (b - a)).trans
    (htrans.trans (lintegral_congr (fun z => ?_)))
  dsimp only [F]
  rw [show -(-a + z.1) = a - z.1 by abel,
    show (b - a) - (-a + z.2) = b - z.2 by abel]

theorem originalHeatSecondProfile_eq_shifted_pair_add_diagonal
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a b : Rd d) :
    originalHeatSecondProfile d P hP t (b - a) =
      (∫⁻ z, ENNReal.ofReal (originalHeatGaussian d t (a - z.1)) *
        ENNReal.ofReal (originalHeatGaussian d t (b - z.2))
          ∂originalAdmissibleFactorialMeasure d P hP) +
        ∫⁻ x, ENNReal.ofReal (originalHeatGaussian d t (a - x)) *
          ENNReal.ofReal (originalHeatGaussian d t (b - x)) ∂volume := by
  have hdiag := lintegral_originalHeatGaussian_mul d t t ht ht a b
  rw [show t + t = 2 * t by ring] at hdiag
  rw [originalHeatSecondProfile,
    originalHeatPairProfile_eq_shifted_pair_lintegral d P hP t ht a b, hdiag]

theorem compactPairHeatRegularization_secondProfile_lintegral
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (ψ : C_c(Rd d × Rd d, ℝ)) :
    (∫⁻ q : Rd d × Rd d, ENNReal.ofReal (ψ q) *
      originalHeatSecondProfile d P hP t (q.2 - q.1)
        ∂(volume : Measure (Rd d)).prod volume) =
      (∫⁻ z, compactPairHeatRegularization d t ψ z
        ∂originalAdmissibleFactorialMeasure d P hP) +
        ∫⁻ x, compactPairHeatRegularization d t ψ (x, x) ∂volume := by
  let Γ := originalAdmissibleFactorialMeasure d P hP
  let ν : Measure (Rd d × Rd d) := (volume : Measure (Rd d)).prod volume
  letI : SFinite Γ := by infer_instance
  let F : (Rd d × Rd d) → (Rd d × Rd d) → ℝ≥0∞ := fun q z =>
    ENNReal.ofReal (ψ q) *
      (ENNReal.ofReal (originalHeatGaussian d t (q.1 - z.1)) *
        ENNReal.ofReal (originalHeatGaussian d t (q.2 - z.2)))
  have hF : Measurable (Function.uncurry F) :=
    (ψ.continuous.comp continuous_fst).measurable.ennreal_ofReal.mul
      ((((continuous_originalHeatGaussian d t).comp
        ((continuous_fst.comp continuous_fst).sub
          (continuous_fst.comp continuous_snd))).measurable.ennreal_ofReal).mul
            (((continuous_originalHeatGaussian d t).comp
              ((continuous_snd.comp continuous_fst).sub
                (continuous_snd.comp continuous_snd))).measurable.ennreal_ofReal))
  have hFd : Measurable (fun r : (Rd d × Rd d) × Rd d => F r.1 (r.2, r.2)) :=
    hF.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd))
  have hPairMeas : Measurable (fun q => ∫⁻ z, F q z ∂Γ) := hF.lintegral_prod_right
  have hpoint (q : Rd d × Rd d) :
      ENNReal.ofReal (ψ q) * originalHeatSecondProfile d P hP t (q.2 - q.1) =
        (∫⁻ z, F q z ∂Γ) + ∫⁻ x, F q (x, x) ∂volume := by
    rw [originalHeatSecondProfile_eq_shifted_pair_add_diagonal d P hP t ht q.1 q.2,
      mul_add]
    exact congrArg₂ (fun u v : ℝ≥0∞ => u + v)
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  have hpairSwap : (∫⁻ q, ∫⁻ z, F q z ∂Γ ∂ν) =
      ∫⁻ z, compactPairHeatRegularization d t ψ z ∂Γ :=
    (lintegral_lintegral_swap hF.aemeasurable).trans
      (lintegral_congr (fun z => lintegral_congr (fun q => mul_comm _ _)))
  have hdiagSwap : (∫⁻ q, ∫⁻ x, F q (x, x) ∂volume ∂ν) =
      ∫⁻ x, compactPairHeatRegularization d t ψ (x, x) ∂volume :=
    (lintegral_lintegral_swap hFd.aemeasurable).trans
      (lintegral_congr (fun x => lintegral_congr (fun q => mul_comm _ _)))
  exact (lintegral_congr hpoint).trans ((lintegral_add_left hPairMeas _).trans
    (congrArg₂ (fun u v : ℝ≥0∞ => u + v) hpairSwap hdiagSwap))

theorem compactPairHeatRegularization_covariance_integral
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (hQ : Q d P (1 / (8 * t)) ≠ ∞)
    (ψ : C_c(Rd d × Rd d, ℝ)) (hψ : ∀ q, 0 ≤ ψ q)
    (hΓ : (∫⁻ z, compactPairHeatRegularization d t ψ z
      ∂originalAdmissibleFactorialMeasure d P hP) ≠ ∞)
    (hdiag : (∫⁻ x, compactPairHeatRegularization d t ψ (x, x) ∂volume) ≠ ∞) :
    Integrable (fun q : Rd d × Rd d => ψ q * originalHeatCovariance d P t (q.2 - q.1))
      ((volume : Measure (Rd d)).prod volume) ∧
      (∫ q : Rd d × Rd d, ψ q * originalHeatCovariance d P t (q.2 - q.1)
        ∂(volume : Measure (Rd d)).prod volume) =
        (∫⁻ z, compactPairHeatRegularization d t ψ z
          ∂originalAdmissibleFactorialMeasure d P hP).toReal +
          (∫⁻ x, compactPairHeatRegularization d t ψ (x, x) ∂volume).toReal -
            ∫ q : Rd d × Rd d, ψ q ∂(volume : Measure (Rd d)).prod volume := by
  let ν : Measure (Rd d × Rd d) := (volume : Measure (Rd d)).prod volume
  let F : Rd d × Rd d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (ψ q) * originalHeatSecondProfile d P hP t (q.2 - q.1)
  have hF : Measurable F := ψ.continuous.measurable.ennreal_ofReal.mul
    ((measurable_originalHeatSecondProfile d P hP t).comp
      (measurable_snd.sub measurable_fst))
  have hNN := compactPairHeatRegularization_secondProfile_lintegral d P hP t ht ψ
  have hfin : (∫⁻ q, F q ∂ν) ≠ ∞ :=
    hNN.trans_ne (ENNReal.add_ne_top.mpr ⟨hΓ, hdiag⟩)
  have hFint : Integrable (fun q => (F q).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top hF.aemeasurable hfin
  have hψint : Integrable ψ ν :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hpoint (q : Rd d × Rd d) :
      ψ q * originalHeatCovariance d P t (q.2 - q.1) = (F q).toReal - ψ q := by
    rw [originalHeatCovariance_eq_secondProfile_toReal d P hP t ht hQ (q.2 - q.1)]
    dsimp only [F]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hψ q)]
    ring
  refine ⟨(hFint.sub hψint).congr
    (Filter.Eventually.of_forall (fun q => (hpoint q).symm)), ?_⟩
  refine (integral_congr_ae (Filter.Eventually.of_forall hpoint)).trans
    ((integral_sub hFint hψint).trans ?_)
  rw [integral_toReal hF.aemeasurable (ae_lt_top hF hfin), hNN,
    ENNReal.toReal_add hΓ hdiag]

theorem compactPositiveHeadPairTest_covariance_tendsto
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    Integrable (compactPositiveHeadPairTest d s hs χ)
      (originalAdmissibleFactorialMeasure d P hP) ∧
      Tendsto (fun n => ∫ q : Rd d × Rd d,
        compactPositiveHeadPairTest d s hs χ q *
          originalHeatCovariance d P ((ε n) ^ 2) (q.2 - q.1)
            ∂(volume : Measure (Rd d)).prod volume) atTop
        (𝓝 ((∫ q, compactPositiveHeadPairTest d s hs χ q
          ∂originalAdmissibleFactorialMeasure d P hP) +
            (2 / s) * (∫ x : Rd d, (χ x) ^ 2 ∂volume) -
              ∫ q : Rd d × Rd d, compactPositiveHeadPairTest d s hs χ q
                ∂(volume : Measure (Rd d)).prod volume)) := by
  let Γ := originalAdmissibleFactorialMeasure d P hP
  let ψ := compactPositiveHeadPairTest d s hs χ
  have hψ (q : Rd d × Rd d) : 0 ≤ ψ q :=
    (compactPositiveHeadPairTest_nonneg_and_bound d s hs χ hχ q).1
  have hψmeas : Measurable (fun q => ENNReal.ofReal (ψ q)) :=
    ψ.continuous.measurable.ennreal_ofReal
  have hψdiagmeas : Measurable (fun x : Rd d => ENNReal.ofReal (ψ (x, x))) :=
    hψmeas.comp (measurable_id.prodMk measurable_id)
  obtain ⟨hΓfin, hdiagfin, hΓlim, hdiaglim⟩ :=
    compactPositiveHeadPairTest_originalGamma_tendsto d s hs P hP hW χ hχ ε hεpos hε
  have hψint : Integrable ψ Γ :=
    (integrable_toReal_of_lintegral_ne_top hψmeas.aemeasurable hΓfin).congr
      (Filter.Eventually.of_forall (fun q => ENNReal.toReal_ofReal (hψ q)))
  have hΓtarget : (∫⁻ q, ENNReal.ofReal (ψ q) ∂Γ).toReal = ∫ q, ψ q ∂Γ :=
    (integral_toReal hψmeas.aemeasurable (ae_lt_top hψmeas hΓfin)).symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall (fun q =>
        ENNReal.toReal_ofReal (hψ q))))
  have hdiagtarget : (∫⁻ x, ENNReal.ofReal (ψ (x, x)) ∂volume).toReal =
      (2 / s) * (∫ x : Rd d, (χ x) ^ 2 ∂volume) :=
    (integral_toReal hψdiagmeas.aemeasurable
      (ae_lt_top hψdiagmeas hdiagfin)).symm.trans
        ((integral_congr_ae (Filter.Eventually.of_forall (fun x =>
          ENNReal.toReal_ofReal (hψ (x, x))))).trans
          ((integral_congr_ae (Filter.Eventually.of_forall
            (compactPositiveHeadPairTest_diagonal d s hs χ))).trans
              (integral_const_mul _ _)))
  have hΓn : ∀ᶠ n in atTop, (∫⁻ q, compactPairHeatRegularization d ((ε n) ^ 2) ψ q
      ∂Γ) ≠ ∞ :=
    (hΓlim.eventually (Iio_mem_nhds (lt_top_iff_ne_top.mpr hΓfin))).mono
      (fun _ hn => hn.ne)
  have hdiagn : ∀ᶠ n in atTop, (∫⁻ x, compactPairHeatRegularization d ((ε n) ^ 2)
      ψ (x, x) ∂volume) ≠ ∞ :=
    (hdiaglim.eventually (Iio_mem_nhds (lt_top_iff_ne_top.mpr hdiagfin))).mono
      (fun _ hn => hn.ne)
  have hreal := ((ENNReal.tendsto_toReal hΓfin).comp hΓlim).add
    ((ENNReal.tendsto_toReal hdiagfin).comp hdiaglim)
  have hbackground : Tendsto (fun _ : ℕ =>
      ∫ q : Rd d × Rd d, ψ q ∂(volume : Measure (Rd d)).prod volume)
      atTop (𝓝 (∫ q : Rd d × Rd d, ψ q
        ∂(volume : Measure (Rd d)).prod volume)) := tendsto_const_nhds
  have hreal' := hreal.sub hbackground
  rw [hΓtarget, hdiagtarget] at hreal'
  refine ⟨hψint, hreal'.congr' ?_⟩
  filter_upwards [hΓn, hdiagn] with n hnΓ hndiag
  have ht : 0 < (ε n) ^ 2 := sq_pos_of_pos (hεpos n)
  exact (compactPairHeatRegularization_covariance_integral d P hP ((ε n) ^ 2) ht
    (Q_ne_top_of_W_ne_top_pos d s hs P hW _ (by positivity))
      ψ hψ hnΓ hndiag).2.symm

end Riesz.Stationary
