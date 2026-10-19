import Riesz.Stationary.HeatSpectrumCompatibility
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section

open MeasureTheory RieszShowcase Riesz.Configuration
open scoped ENNReal Topology

namespace Riesz.Stationary

/-- The Gamma mixture of Gaussian weights, as an identity of nonnegative integrals. -/
theorem lintegral_gamma_heat_mixture
    (r v : ℝ) (hr : 0 ≤ r) (hv : 0 ≤ v) :
    (∫⁻ τ : ℝ in Set.Ioi 0,
      ENNReal.ofReal (τ ^ r * Real.exp (-τ)) *
        ENNReal.ofReal (Real.exp (-τ * v)) ∂volume) =
      ENNReal.ofReal (Real.Gamma (r + 1)) *
        ENNReal.ofReal ((1 + v) ^ (-(r + 1))) := by
  have ha : 0 < r + 1 := by linarith
  have hb : 0 < 1 + v := by linarith
  have hGamma : 0 < Real.Gamma (r + 1) := Real.Gamma_pos_of_pos ha
  have hscalar :
      (∫ τ : ℝ in Set.Ioi 0, τ ^ r * Real.exp (-((1 + v) * τ)) ∂volume) =
        Real.Gamma (r + 1) * (1 + v) ^ (-(r + 1)) := by
    simpa only [show r + 1 - 1 = r by ring, one_div,
      ← Real.rpow_neg_eq_inv_rpow] using
        (Real.integral_rpow_mul_exp_neg_mul_Ioi ha hb).trans (mul_comm _ _)
  have hint : IntegrableOn
      (fun τ : ℝ => τ ^ r * Real.exp (-((1 + v) * τ))) (Set.Ioi 0) :=
    Integrable.of_integral_ne_zero (hscalar.trans_ne
      (mul_pos hGamma (Real.rpow_pos_of_pos hb _)).ne')
  have hnonneg : ∀ᵐ τ : ℝ ∂volume.restrict (Set.Ioi 0),
      0 ≤ τ ^ r * Real.exp (-((1 + v) * τ)) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun τ hτ =>
      mul_nonneg (Real.rpow_pos_of_pos hτ _).le (Real.exp_pos _).le
  refine Eq.trans ?_ ((ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm.trans
    ((congrArg ENNReal.ofReal hscalar).trans (ENNReal.ofReal_mul hGamma.le)))
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  rw [← ENNReal.ofReal_mul
    (mul_nonneg (Real.rpow_pos_of_pos hτ _).le (Real.exp_pos _).le)]
  congr 1
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A short-time Gaussian mass bound gives precisely the tail needed below. -/
theorem integrable_polynomialTail_of_gaussianMass_bound
    (d : ℕ) (S : Measure (Rd d)) [SFinite S]
    (C T : ℝ) (hC : 0 ≤ C) (hT : 0 < T)
    (hheat : ∀ τ : ℝ, 0 < τ → τ ≤ T →
      (∫⁻ k, ENNReal.ofReal (Real.exp (-τ * ‖k‖ ^ 2)) ∂S) ≤
        ENNReal.ofReal (C * τ ^ (-((d : ℝ) / 2)))) :
    Integrable (fun k => (1 + ‖k‖) ^ (-((d + 2 : ℕ) : ℝ))) S := by
  let r : ℝ := (d : ℝ) / 2
  have hr : 0 ≤ r := div_nonneg (Nat.cast_nonneg d) (by norm_num)
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  let L : ℝ → ℝ≥0∞ := fun τ =>
    ∫⁻ k, ENNReal.ofReal (Real.exp (-τ * ‖k‖ ^ 2)) ∂S
  let M : ℝ → ℝ := fun τ => C * Real.exp (-τ) +
    (C * T ^ (-r)) * (τ ^ r * Real.exp (-τ))
  have hweightInt : Integrable (fun τ : ℝ => τ ^ r * Real.exp (-τ)) ν := by
    simpa only [ν, IntegrableOn, show r + 1 - 1 = r by ring, mul_comm] using
      Real.GammaIntegral_convergent (show 0 < r + 1 by linarith)
  have hexpInt : Integrable (fun τ : ℝ => Real.exp (-τ)) ν := by
    simpa only [ν, IntegrableOn, sub_self, Real.rpow_zero, mul_one] using
      Real.GammaIntegral_convergent (show (0 : ℝ) < 1 by norm_num)
  have hMInt : Integrable M ν :=
    (hexpInt.const_mul C).add (hweightInt.const_mul (C * T ^ (-r)))
  have hM0 : ∀ᵐ τ ∂ν, 0 ≤ M τ :=
    (ae_restrict_mem measurableSet_Ioi).mono fun τ hτ =>
      add_nonneg (mul_nonneg hC (Real.exp_pos _).le)
        (mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hT _).le)
          (mul_nonneg (Real.rpow_pos_of_pos hτ _).le (Real.exp_pos _).le))
  have hMFinite : (∫⁻ τ, ENNReal.ofReal (M τ) ∂ν) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hMInt.aestronglyMeasurable hM0).mpr hMInt
  have hglobal (τ : ℝ) (hτ : 0 < τ) :
      L τ ≤ ENNReal.ofReal (C * τ ^ (-r) + C * T ^ (-r)) := by
    by_cases hsmall : τ ≤ T
    · exact (hheat τ hτ hsmall).trans (ENNReal.ofReal_le_ofReal
        (le_add_of_nonneg_right (mul_nonneg hC (Real.rpow_pos_of_pos hT _).le)))
    · have hTτ : T ≤ τ := (lt_of_not_ge hsmall).le
      have hmono : L τ ≤ L T := lintegral_mono (fun k =>
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (neg_le_neg hTτ) (sq_nonneg ‖k‖))))
      exact (hmono.trans (hheat T hT le_rfl)).trans (ENNReal.ofReal_le_ofReal
        (le_add_of_nonneg_left (mul_nonneg hC (Real.rpow_pos_of_pos hτ _).le)))
  have hweighted (τ : ℝ) (hτ : 0 < τ) :
      ENNReal.ofReal (τ ^ r * Real.exp (-τ)) * L τ ≤ ENNReal.ofReal (M τ) := by
    have hcancel : τ ^ r * τ ^ (-r) = 1 := by
      rw [← Real.rpow_add hτ, add_neg_cancel, Real.rpow_zero]
    refine (mul_le_mul_right (hglobal τ hτ) _).trans_eq ?_
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (Real.rpow_pos_of_pos hτ _).le (Real.exp_pos _).le)]
    congr 1
    linear_combination C * Real.exp (-τ) * hcancel
  have hdoubleFinite :
      (∫⁻ τ, ENNReal.ofReal (τ ^ r * Real.exp (-τ)) * L τ ∂ν) ≠ ∞ :=
    ne_top_of_le_ne_top hMFinite (lintegral_mono_ae
      ((ae_restrict_mem measurableSet_Ioi).mono fun τ hτ => hweighted τ hτ))
  have hwCont : Continuous (fun τ : ℝ => τ ^ r * Real.exp (-τ)) :=
    (Real.continuous_rpow_const hr).mul continuous_id.neg.rexp
  have hGm : Measurable (fun q : ℝ × Rd d =>
      ENNReal.ofReal (q.1 ^ r * Real.exp (-q.1)) *
        ENNReal.ofReal (Real.exp (-q.1 * ‖q.2‖ ^ 2))) :=
    ((hwCont.measurable.comp measurable_fst).ennreal_ofReal).mul
      ((show Continuous (fun q : ℝ × Rd d => Real.exp (-q.1 * ‖q.2‖ ^ 2)) from
        by fun_prop).measurable.ennreal_ofReal)
  have hTonelli :
      (∫⁻ k, ∫⁻ τ, ENNReal.ofReal (τ ^ r * Real.exp (-τ)) *
          ENNReal.ofReal (Real.exp (-τ * ‖k‖ ^ 2)) ∂ν ∂S) =
        ∫⁻ τ, ENNReal.ofReal (τ ^ r * Real.exp (-τ)) * L τ ∂ν :=
    (lintegral_lintegral_swap (μ := ν) (ν := S)
      (f := fun τ k => ENNReal.ofReal (τ ^ r * Real.exp (-τ)) *
        ENNReal.ofReal (Real.exp (-τ * ‖k‖ ^ 2))) hGm.aemeasurable).symm.trans
      (lintegral_congr fun τ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
  have hmixture : ENNReal.ofReal (Real.Gamma (r + 1)) *
      (∫⁻ k, ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (-(r + 1))) ∂S) =
        ∫⁻ τ, ENNReal.ofReal (τ ^ r * Real.exp (-τ)) * L τ ∂ν :=
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm.trans
      ((lintegral_congr fun k => (lintegral_gamma_heat_mixture r (‖k‖ ^ 2) hr
        (sq_nonneg ‖k‖)).symm).trans hTonelli)
  have hproductFinite : ENNReal.ofReal (Real.Gamma (r + 1)) *
      (∫⁻ k, ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (-(r + 1))) ∂S) ≠ ∞ :=
    hmixture.trans_ne hdoubleFinite
  have htailFinite :
      (∫⁻ k, ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (-(r + 1))) ∂S) ≠ ∞ := by
    intro htop
    apply hproductFinite
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr
      (Real.Gamma_pos_of_pos (show 0 < r + 1 by linarith)))]
  have hbaseCont : Continuous (fun k : Rd d => 1 + ‖k‖ ^ (2 : ℕ)) :=
    continuous_const.add (continuous_norm.pow 2)
  have htailCont : Continuous (fun k : Rd d => (1 + ‖k‖ ^ 2) ^ (-(r + 1))) :=
    hbaseCont.rpow_const (fun k => Or.inl (show 1 + ‖k‖ ^ 2 ≠ 0 from
      (show 0 < 1 + ‖k‖ ^ 2 by positivity).ne'))
  have hBesselInt : Integrable (fun k : Rd d => (1 + ‖k‖ ^ 2) ^ (-(r + 1))) S :=
    (lintegral_ofReal_ne_top_iff_integrable htailCont.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun k =>
        (Real.rpow_pos_of_pos (show 0 < 1 + ‖k‖ ^ 2 by positivity) _).le))).mp htailFinite
  have hpolyCont : Continuous (fun k : Rd d => (1 + ‖k‖) ^ (-((d + 2 : ℕ) : ℝ))) :=
    (continuous_const.add continuous_norm).rpow_const (fun k =>
      Or.inl (show 1 + ‖k‖ ≠ 0 from (show 0 < 1 + ‖k‖ by positivity).ne'))
  apply hBesselInt.mono' hpolyCont.measurable.aestronglyMeasurable
  refine Filter.Eventually.of_forall (fun k => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (Real.rpow_pos_of_pos (show 0 < 1 + ‖k‖ by positivity) _).le]
  have hcompare := Real.rpow_le_rpow_of_nonpos
    (show 0 < 1 + ‖k‖ ^ 2 by positivity)
    (show 1 + ‖k‖ ^ 2 ≤ (1 + ‖k‖) ^ 2 by nlinarith [norm_nonneg k])
    (show -(r + 1) ≤ 0 by linarith)
  have hexponent : (2 : ℝ) * (-(r + 1)) = -((d + 2 : ℕ) : ℝ) := by
    norm_num [r]
    ring
  have hpower : ((1 + ‖k‖) ^ (2 : ℕ)) ^ (-(r + 1)) =
      (1 + ‖k‖) ^ (-((d + 2 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast_mul (show 0 ≤ 1 + ‖k‖ by positivity) 2 (-(r + 1)),
      Nat.cast_ofNat, hexponent]
  simpa only [hpower] using hcompare

/-- The checked heat trace bounds the Gaussian mass of the actual spectrum. -/
theorem originalAngularSpectrum_gaussianMass_le
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (τ : ℝ) (hτ : 0 < τ) (hsmall : τ ≤ 1 / 4) :
    (∫⁻ k, ENNReal.ofReal (Real.exp (-τ * ‖k‖ ^ 2))
      ∂originalAngularSpectrum d s hs P hP hW) ≤
        ENNReal.ofReal (((4 * Real.pi) ^ (-((d : ℝ) / 2)) *
          ((Q d P 1).toReal + 1)) * τ ^ (-((d : ℝ) / 2))) := by
  have ht : 0 < τ / 2 := by positivity
  have hu : 1 ≤ 1 / (8 * (τ / 2)) :=
    (le_div_iff₀ (show 0 < 8 * (τ / 2) by positivity)).mpr (by nlinarith)
  have hQ1 : Q d P 1 ≠ ∞ := Q_ne_top_of_W_ne_top_pos d s hs P hW 1 (by norm_num)
  have hQle : (Q d P (1 / (8 * (τ / 2)))).toReal ≤ (Q d P 1).toReal :=
    ENNReal.toReal_mono hQ1 (antitone_Q d P hu)
  have hmass :
      (∫⁻ k, ENNReal.ofReal (Real.exp (-τ * ‖k‖ ^ 2))
        ∂originalAngularSpectrum d s hs P hP hW) =
      ENNReal.ofReal ((8 * Real.pi * (τ / 2)) ^ (-((d : ℝ) / 2)) *
        ((Q d P (1 / (8 * (τ / 2)))).toReal + 1) - 1) := by
    simpa only [heatSpectralWeight, show (2 : ℝ) * (τ / 2) = τ by ring] using
      lintegral_originalAngularSpectrum_heatSpectralWeight_eq d s hs P hP hW (τ / 2) ht
  have hbound : ENNReal.ofReal ((8 * Real.pi * (τ / 2)) ^ (-((d : ℝ) / 2)) *
      ((Q d P (1 / (8 * (τ / 2)))).toReal + 1) - 1) ≤
      ENNReal.ofReal ((8 * Real.pi * (τ / 2)) ^ (-((d : ℝ) / 2)) *
        ((Q d P 1).toReal + 1)) := ENNReal.ofReal_le_ofReal
    ((sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans
      (mul_le_mul_of_nonneg_left (add_le_add_left hQle 1)
        (Real.rpow_pos_of_pos (show 0 < 8 * Real.pi * (τ / 2) by positivity) _).le))
  refine (hmass.le.trans hbound).trans_eq ?_
  rw [show 8 * Real.pi * (τ / 2) = (4 * Real.pi) * τ by ring,
    Real.mul_rpow (show 0 ≤ 4 * Real.pi by positivity) hτ.le]
  exact congrArg ENNReal.ofReal (mul_right_comm _ _ _)

/-- The original finite-energy law supplies the spectral domination tail. -/
theorem integrable_originalAngularSpectrum_polynomialTail
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    Integrable (fun k => (1 + ‖k‖) ^ (-((d + 2 : ℕ) : ℝ)))
      (originalAngularSpectrum d s hs P hP hW) := by
  exact integrable_polynomialTail_of_gaussianMass_bound d
    (originalAngularSpectrum d s hs P hP hW)
    ((4 * Real.pi) ^ (-((d : ℝ) / 2)) * ((Q d P 1).toReal + 1)) (1 / 4)
    (by positivity) (by norm_num)
    (fun τ hτ hsmall => originalAngularSpectrum_gaussianMass_le d s hs P hP hW τ hτ hsmall)

end Riesz.Stationary
