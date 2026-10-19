import Riesz.Stationary.PositiveWindowConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Riesz.Stationary.CompactSignedFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

noncomputable section
open MeasureTheory Filter RieszShowcase
open scoped ENNReal CompactlySupported RealInnerProductSpace

namespace Riesz.Stationary

private abbrev neutralPhase (d : ℕ) (k x : Rd d) : ℂ :=
  Complex.exp ((inner ℝ k x : ℂ) * Complex.I)

def angularAbsoluteMass (d : ℕ) (χ : C_c(Rd d, ℝ)) : ℝ :=
  ∫ x : Rd d, |χ x|

def angularFirstAbsoluteMoment (d : ℕ) (χ : C_c(Rd d, ℝ)) : ℝ :=
  ∫ x : Rd d, |χ x| * ‖x‖

private theorem integrable_angular_firstMoment
    (d : ℕ) (χ : C_c(Rd d, ℝ)) :
    Integrable (fun x : Rd d => |χ x| * ‖x‖) volume :=
  (χ.continuous.abs.mul continuous_norm).integrable_of_hasCompactSupport
    χ.hasCompactSupport.abs.mul_right

theorem angularAbsoluteMass_nonneg (d : ℕ) (χ : C_c(Rd d, ℝ)) :
    0 ≤ angularAbsoluteMass d χ := integral_nonneg (fun _ => abs_nonneg _)

theorem angularFirstAbsoluteMoment_nonneg (d : ℕ) (χ : C_c(Rd d, ℝ)) :
    0 ≤ angularFirstAbsoluteMoment d χ :=
  integral_nonneg (fun _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))

private theorem neutralPhase_norm_sub_le
    (d : ℕ) (k l x : Rd d) :
    ‖neutralPhase d k x - neutralPhase d l x‖ ≤ ‖k-l‖ * ‖x‖ := by
  have he : neutralPhase d l x * neutralPhase d (k-l) x =
      neutralPhase d k x := by
    dsimp only [neutralPhase]
    rw [← Complex.exp_add]
    congr 1
    simp only [inner_sub_left, Complex.ofReal_sub]
    ring
  have heq : neutralPhase d k x - neutralPhase d l x =
      neutralPhase d l x * (neutralPhase d (k-l) x - 1) := by
    rw [mul_sub, he, mul_one]
  rw [heq, norm_mul]
  have hn : ‖neutralPhase d l x‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  rw [hn, one_mul]
  calc
    _ ≤ ‖inner ℝ (k-l) x‖ := by
      simpa only [neutralPhase, mul_comm] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := inner ℝ (k-l) x))
    _ ≤ _ := norm_inner_le_norm (k-l) x

private theorem integrable_neutralPhase_window
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (k : Rd d) :
    Integrable (fun x : Rd d => (χ x : ℂ) * neutralPhase d k x) volume := by
  have hc : HasCompactSupport (fun x : Rd d => (χ x : ℂ)) :=
    χ.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  exact (show Continuous (fun x : Rd d => (χ x : ℂ) * neutralPhase d k x)
    from by fun_prop).integrable_of_hasCompactSupport hc.mul_right

theorem compactAngularAmplitude_norm_le_absoluteMass
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (k : Rd d) :
    ‖compactAngularAmplitude d χ k‖ ≤ angularAbsoluteMass d χ := by
  refine (norm_integral_le_integral_norm _).trans_eq
    (integral_congr_ae (Eventually.of_forall (fun x => ?_)))
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

theorem compactAngularAmplitude_sub_norm_le_firstMoment
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (k l : Rd d) :
    ‖compactAngularAmplitude d χ k - compactAngularAmplitude d χ l‖ ≤
      ‖k-l‖ * angularFirstAbsoluteMoment d χ := by
  have hp (x : Rd d) :
      ‖(χ x : ℂ) * neutralPhase d k x - (χ x : ℂ) * neutralPhase d l x‖ ≤
        ‖k-l‖ * (|χ x| * ‖x‖) := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |χ x| * (‖k-l‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (neutralPhase_norm_sub_le d k l x) (abs_nonneg _)
      _ = _ := by ring
  calc
    _ = ‖∫ x : Rd d, (χ x : ℂ) * neutralPhase d k x -
        (χ x : ℂ) * neutralPhase d l x‖ :=
      (congrArg norm (integral_sub (f := fun x : Rd d => (χ x : ℂ) * neutralPhase d k x)
        (g := fun x : Rd d => (χ x : ℂ) * neutralPhase d l x)
        (integrable_neutralPhase_window d χ k) (integrable_neutralPhase_window d χ l))).symm
    _ ≤ ∫ x : Rd d, ‖k-l‖ * (|χ x| * ‖x‖) :=
      norm_integral_le_of_norm_le ((integrable_angular_firstMoment d χ).const_mul _)
        (Eventually.of_forall hp)
    _ = _ := integral_const_mul ‖k-l‖ (fun x : Rd d => |χ x| * ‖x‖)

theorem compactAngularAmplitude_zero_integral
    (d : ℕ) (χ : C_c(Rd d, ℝ)) :
    compactAngularAmplitude d χ 0 = (∫ x : Rd d, χ x : ℝ) := by
  simp only [compactAngularAmplitude, inner_zero_left, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, mul_one, integral_complex_ofReal]

def neutralizedAngularAmplitude (d : ℕ) (χ h : C_c(Rd d, ℝ))
    (t v : Rd d) : ℂ :=
  compactAngularAmplitude d χ (v-t) -
    compactAngularAmplitude d χ (-t) * compactAngularAmplitude d h v

theorem neutralizedAngularAmplitude_zero
    (d : ℕ) (χ h : C_c(Rd d, ℝ)) (hh : (∫ x : Rd d, h x) = 1) (t : Rd d) :
    neutralizedAngularAmplitude d χ h t 0 = 0 := by
  simp only [neutralizedAngularAmplitude, zero_sub,
    compactAngularAmplitude_zero_integral, hh, Complex.ofReal_one, mul_one, sub_self]

theorem neutralizedAngularAmplitude_firstOrder
    (d : ℕ) (χ h : C_c(Rd d, ℝ)) (hh : (∫ x : Rd d, h x) = 1)
    (t v : Rd d) :
    ‖neutralizedAngularAmplitude d χ h t v‖ ≤
      (angularFirstAbsoluteMoment d χ +
        angularAbsoluteMass d χ * angularFirstAbsoluteMoment d h) * ‖v‖ := by
  let a := compactAngularAmplitude d χ
  let b := compactAngularAmplitude d h
  have hb0 : b 0 = 1 := by
    simpa only [b, hh, Complex.ofReal_one] using compactAngularAmplitude_zero_integral d h
  have hda : ‖a (v-t) - a (-t)‖ ≤ ‖v‖ * angularFirstAbsoluteMoment d χ := by
    simpa only [a, sub_neg_eq_add, sub_add_cancel] using
      compactAngularAmplitude_sub_norm_le_firstMoment d χ (v-t) (-t)
  have hdb' : ‖b v - b 0‖ ≤ ‖v‖ * angularFirstAbsoluteMoment d h := by
    simpa only [sub_zero] using compactAngularAmplitude_sub_norm_le_firstMoment d h v 0
  have hdb : ‖1 - b v‖ ≤ ‖v‖ * angularFirstAbsoluteMoment d h := by
    calc
      _ = ‖b v - b 0‖ := by rw [hb0, norm_sub_rev]
      _ ≤ _ := hdb'
  have ha : ‖a (-t)‖ ≤ angularAbsoluteMass d χ :=
    compactAngularAmplitude_norm_le_absoluteMass d χ (-t)
  have hm := mul_le_mul ha hdb (norm_nonneg (1-b v))
    (angularAbsoluteMass_nonneg d χ)
  have heq : neutralizedAngularAmplitude d χ h t v =
      (a (v-t) - a (-t)) + a (-t) * (1-b v) := by
    dsimp only [neutralizedAngularAmplitude, a, b]
    ring
  rw [heq]
  calc
    _ ≤ ‖a (v-t)-a (-t)‖ + ‖a (-t)‖ * ‖1-b v‖ := by
      simpa only [norm_mul] using norm_add_le (a (v-t)-a (-t)) (a (-t)*(1-b v))
    _ ≤ _ := by nlinarith

theorem neutralizedAngularAmplitude_uniformBound
    (d : ℕ) (χ h : C_c(Rd d, ℝ)) (t v : Rd d) :
    ‖neutralizedAngularAmplitude d χ h t v‖ ≤
      angularAbsoluteMass d χ * (1 + angularAbsoluteMass d h) := by
  have ha := compactAngularAmplitude_norm_le_absoluteMass d χ (v-t)
  have hat := compactAngularAmplitude_norm_le_absoluteMass d χ (-t)
  have hb := compactAngularAmplitude_norm_le_absoluteMass d h v
  have hm := mul_le_mul hat hb (norm_nonneg _)
    (angularAbsoluteMass_nonneg d χ)
  have hn := norm_sub_le (compactAngularAmplitude d χ (v-t))
    (compactAngularAmplitude d χ (-t) * compactAngularAmplitude d h v)
  rw [norm_mul] at hn
  dsimp only [neutralizedAngularAmplitude]
  nlinarith

def neutralizedFourierProfile (d : ℕ) (q : ℝ) (χ h : C_c(Rd d, ℝ))
    (t v : Rd d) : ℝ :=
  ‖v‖ ^ (-((d : ℝ)+q)) * Complex.normSq (neutralizedAngularAmplitude d χ h t v)

def neutralizedFourierF (d : ℕ) (q : ℝ) (χ h : C_c(Rd d, ℝ)) (t : Rd d) : ℝ :=
  ∫ v : Rd d, neutralizedFourierProfile d q χ h t v

private theorem neutralized_rpow_outside_one
    (p r : ℝ) (hp : 0 ≤ p) (hr : 1 ≤ r) :
    r ^ (-p) ≤ (2 : ℝ)^p * (1+r)^(-p) := by
  have hhalf : 0 < (1+r)/2 := by positivity
  calc
    _ ≤ ((1+r)/2)^(-p) :=
      Real.rpow_le_rpow_of_nonpos hhalf (by linarith) (neg_nonpos.mpr hp)
    _ = _ := by
      rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ 1+r) (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, inv_inv, mul_comm]

theorem neutralizedFourierProfile_integrable
    (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (χ h : C_c(Rd d, ℝ)) (hh : (∫ x : Rd d, h x) = 1) (t : Rd d) :
    Integrable (neutralizedFourierProfile d q χ h t) volume ∧
      (∫⁻ v : Rd d, ENNReal.ofReal (neutralizedFourierProfile d q χ h t v)) ≠ ∞ ∧
      (∫⁻ v : Rd d, ENNReal.ofReal (neutralizedFourierProfile d q χ h t v)).toReal =
        neutralizedFourierF d q χ h t ∧
      0 ≤ neutralizedFourierF d q χ h t := by
  let p : ℝ := (d : ℝ)+q
  let f : Rd d → ℝ := neutralizedFourierProfile d q χ h t
  let K₁ : ℝ := angularFirstAbsoluteMoment d χ +
    angularAbsoluteMass d χ * angularFirstAbsoluteMoment d h
  let K₀ : ℝ := angularAbsoluteMass d χ * (1 + angularAbsoluteMass d h)
  have hp : 0 < p := add_pos_of_nonneg_of_pos (Nat.cast_nonneg d) hq
  have hfm : Measurable f :=
    (measurable_id.norm.pow_const _).mul
      (Complex.continuous_normSq.measurable.comp
        (((measurable_compactAngularAmplitude d χ).comp
          (measurable_id.sub measurable_const)).sub
            (measurable_const.mul (measurable_compactAngularAmplitude d h))))
  have hfnn (v : Rd d) : 0 ≤ f v :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg v) _) (Complex.normSq_nonneg _)
  have hLip (v : Rd d) : ‖neutralizedAngularAmplitude d χ h t v‖ ≤ K₁ * ‖v‖ :=
    neutralizedAngularAmplitude_firstOrder d χ h hh t v
  have hBound (v : Rd d) : ‖neutralizedAngularAmplitude d χ h t v‖ ≤ K₀ :=
    neutralizedAngularAmplitude_uniformBound d χ h t v
  have hnearPoint (v : Rd d) : f v ≤ K₁^2 * ‖v‖^(-(p-2)) := by
    by_cases hv : v = 0
    · have hz : f v = 0 := by
        simp only [f, neutralizedFourierProfile, hv,
          neutralizedAngularAmplitude_zero d χ h hh t, Complex.normSq_zero, mul_zero]
      rw [hz]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (norm_nonneg v) _)
    · have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hs := pow_le_pow_left₀ (norm_nonneg (neutralizedAngularAmplitude d χ h t v))
        (hLip v) 2
      have hexp : -p+(2 : ℝ) = -(p-2) := by ring
      have hpow : ‖v‖^(-p) * ‖v‖^2 = ‖v‖^(-(p-2)) := by
        rw [← Real.rpow_two, ← Real.rpow_add hr, hexp]
      calc
        _ = ‖v‖^(-p) * ‖neutralizedAngularAmplitude d χ h t v‖^2 := by
          simp only [f, neutralizedFourierProfile, p, Complex.normSq_eq_norm_sq]
        _ ≤ ‖v‖^(-p) * (K₁ * ‖v‖)^2 :=
          mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hr.le _)
        _ = K₁^2 * (‖v‖^(-p) * ‖v‖^2) := by ring
        _ = _ := congrArg (K₁^2 * ·) hpow
  have hnear : IntegrableOn f (Metric.ball (0 : Rd d) 1) volume :=
    integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure (Rd d)))
      (by simpa only [Rd, finrank_euclideanSpace_fin] using hd)
      (by simp only [Rd, finrank_euclideanSpace_fin]; dsimp only [p]; linarith)
      (C := K₁^2) (α := p-2)
      (Eventually.of_forall (fun v => by
        simpa only [Real.norm_of_nonneg (hfnn v)] using hnearPoint v))
      hfm.aestronglyMeasurable
  let H : Rd d → ℝ := fun v => (K₀^2 * (2 : ℝ)^p) * (1+‖v‖)^(-p)
  have hH : Integrable H volume :=
    (integrable_one_add_norm (E := Rd d) (μ := volume) (r := p) (by
      simp only [Rd, finrank_euclideanSpace_fin]; dsimp only [p]; linarith)).const_mul _
  have hfarPoint (v : Rd d) (hv : 1 ≤ ‖v‖) : f v ≤ H v := by
    have hs := pow_le_pow_left₀ (norm_nonneg (neutralizedAngularAmplitude d χ h t v))
      (hBound v) 2
    have hpow := neutralized_rpow_outside_one p ‖v‖ hp.le hv
    calc
      _ = ‖v‖^(-p) * ‖neutralizedAngularAmplitude d χ h t v‖^2 := by
        simp only [f, neutralizedFourierProfile, p, Complex.normSq_eq_norm_sq]
      _ ≤ ((2 : ℝ)^p * (1+‖v‖)^(-p)) * K₀^2 :=
        mul_le_mul hpow hs (sq_nonneg _)
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg (by positivity) _))
      _ = _ := by dsimp only [H]; ring
  have hfar : IntegrableOn f (Metric.ball (0 : Rd d) 1)ᶜ volume := by
    have hHB : Integrable H (volume.restrict (Metric.ball (0 : Rd d) 1)ᶜ) := hH.restrict
    refine hHB.mono' hfm.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with v hv
    have hv' : 1 ≤ ‖v‖ := le_of_not_gt (by
      simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right] using hv)
    simpa only [Real.norm_of_nonneg (hfnn v)] using hfarPoint v hv'
  have hInt : Integrable f volume := by
    simpa only [Set.union_compl_self, integrableOn_univ] using hnear.union hfar
  have hNNfin : (∫⁻ v : Rd d, ENNReal.ofReal (f v)) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable
      (Eventually.of_forall hfnn)).2 hInt
  have hNN := ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall hfnn)
  refine ⟨hInt, hNNfin, ?_, integral_nonneg hfnn⟩
  rw [← hNN, ENNReal.toReal_ofReal (integral_nonneg hfnn)]
  rfl

open scoped FourierTransform ContDiff Topology

private def neutralSharpWindowSchwartz
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hsm : ContDiff ℝ ∞ χ) :
    SchwartzMap (Rd d) ℂ := by
  have hcs : HasCompactSupport (Complex.ofRealCLM ∘ (χ : Rd d → ℝ)) :=
    χ.hasCompactSupport.comp_left rfl
  exact hcs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hsm)

private theorem neutralSharp_frequency
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hsm : ContDiff ℝ ∞ χ) (ξ : Rd d) :
    compactAngularAmplitude d χ ((2 * Real.pi) • ξ) =
      (𝓕 (neutralSharpWindowSchwartz d χ hsm)) (-ξ) := by
  rw [compactAngularAmplitude, SchwartzMap.fourier_coe, Real.fourier_eq']
  apply integral_congr_ae
  refine Eventually.of_forall (fun x => ?_)
  have hphase : -2 * Real.pi * inner ℝ x (-ξ) =
      inner ℝ ((2 * Real.pi) • ξ) x := by
    rw [inner_neg_right, real_inner_smul_left, real_inner_comm ξ x]
    ring
  change (χ x : ℂ) *
      Complex.exp ((inner ℝ ((2 * Real.pi) • ξ) x : ℂ) * Complex.I) =
    Complex.exp (((-2 * Real.pi * inner ℝ x (-ξ) : ℝ) : ℂ) * Complex.I) •
      (χ x : ℂ)
  rw [smul_eq_mul, hphase]
  exact mul_comm _ _

private def neutralSharpAngularSchwartz
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hsm : ContDiff ℝ ∞ χ) :
    SchwartzMap (Rd d) ℂ := by
  let e : Rd d ≃L[ℝ] Rd d :=
    (LinearEquiv.smulOfNeZero ℝ (Rd d) (-(2 * Real.pi)⁻¹)
      (neg_ne_zero.mpr (inv_ne_zero (by positivity)))).toContinuousLinearEquiv
  exact SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
    (𝓕 (neutralSharpWindowSchwartz d χ hsm))

private theorem neutralSharpAngularSchwartz_apply
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hsm : ContDiff ℝ ∞ χ) (k : Rd d) :
    neutralSharpAngularSchwartz d χ hsm k = compactAngularAmplitude d χ k := by
  have hτ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  change (𝓕 (neutralSharpWindowSchwartz d χ hsm))
    ((-(2 * Real.pi)⁻¹) • k) = compactAngularAmplitude d χ k
  simpa only [neg_smul, smul_smul, mul_inv_cancel₀ hτ, one_smul] using
    (neutralSharp_frequency d χ hsm ((2 * Real.pi)⁻¹ • k)).symm

private theorem neutralSharp_weighted_value_derivative
    (d N : ℕ) (a : SchwartzMap (Rd d) ℂ) :
    ∃ A : ℝ, 0 < A ∧ ∀ x,
      (1 + ‖x‖)^N * ‖a x‖ ≤ A ∧
      (1 + ‖x‖)^N * ‖fderiv ℝ a x‖ ≤ A := by
  let B : ℝ := (2 : ℝ)^N *
    (Finset.Iic (N, 1)).sup (fun j => SchwartzMap.seminorm ℂ j.1 j.2) a
  have h0 (x : Rd d) : (1 + ‖x‖)^N * ‖a x‖ ≤ B := by
    simpa only [B, norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℂ) (m := (N, 1)) (k := N) (n := 0)
        le_rfl (by norm_num) a x)
  have h1 (x : Rd d) : (1 + ‖x‖)^N * ‖fderiv ℝ a x‖ ≤ B := by
    simpa only [B, norm_iteratedFDeriv_one] using
      (SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℂ) (m := (N, 1)) (k := N) (n := 1) le_rfl le_rfl a x)
  refine ⟨max B 1, zero_lt_one.trans_le (le_max_right _ _), fun x => ?_⟩
  exact ⟨(h0 x).trans (le_max_left _ _), (h1 x).trans (le_max_left _ _)⟩

private theorem neutralSharp_weighted_on_near_ball
    (d N : ℕ) (g : Rd d → ℝ) (hg : ∀ x, 0 ≤ g x) (A : ℝ)
    (hA : ∀ x, (1 + ‖x‖)^N * g x ≤ A)
    (t v : Rd d) (hv : ‖v‖ ≤ ‖t‖ / 2) :
    ∀ z ∈ Metric.closedBall (-t) ‖v‖,
      g z ≤ ((2 : ℝ)^N * A) * (1 + ‖t‖)^(-(N : ℝ)) := by
  intro z hz
  have hz' : ‖z + t‖ ≤ ‖v‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hz
  have ht : ‖t‖ ≤ ‖z + t‖ + ‖z‖ := by
    simpa using norm_sub_le (z + t) z
  have hrad : 1 + ‖t‖ ≤ 2 * (1 + ‖z‖) := by linarith
  have hpow : (1 + ‖t‖)^N ≤ (2 : ℝ)^N * (1 + ‖z‖)^N := by
    simpa only [mul_pow] using
      (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖t‖) hrad N)
  have hmul : (1 + ‖t‖)^N * g z ≤ (2 : ℝ)^N * A := by
    calc
      _ ≤ ((2 : ℝ)^N * (1 + ‖z‖)^N) * g z :=
        mul_le_mul_of_nonneg_right hpow (hg z)
      _ = (2 : ℝ)^N * ((1 + ‖z‖)^N * g z) := by ring
      _ ≤ (2 : ℝ)^N * A :=
        mul_le_mul_of_nonneg_left (hA z) (by positivity)
  have hdiv : g z ≤ ((2 : ℝ)^N * A) / (1 + ‖t‖)^N :=
    (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t‖) N)).2
      (by simpa only [mul_comm] using hmul)
  simpa only [div_eq_mul_inv, ← Real.rpow_natCast,
    ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖t‖)] using hdiv

private theorem neutralSharp_weighted_near_cancellation
    (d N : ℕ) (χ h : C_c(Rd d, ℝ)) (hsm : ContDiff ℝ ∞ χ)
    (hh : (∫ x : Rd d, h x) = 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ t v : Rd d, ‖v‖ ≤ ‖t‖ / 2 →
      (‖neutralizedAngularAmplitude d χ h t v‖ ≤
        K * (1 + ‖t‖)^(-(N : ℝ)) * ‖v‖) ∧
      (‖neutralizedAngularAmplitude d χ h t v‖ ≤
        K * (1 + ‖t‖)^(-(N : ℝ))) := by
  let a := neutralSharpAngularSchwartz d χ hsm
  rcases neutralSharp_weighted_value_derivative d N a with ⟨A, hApos, hA⟩
  let C : ℝ := (2 : ℝ)^N * A
  let M₁ : ℝ := angularFirstAbsoluteMoment d h
  let M₀ : ℝ := angularAbsoluteMass d h
  let K₁ : ℝ := C * (1 + M₁)
  let K₀ : ℝ := C * (1 + M₀)
  let K : ℝ := K₁ + K₀
  have hM₁ : 0 ≤ M₁ := angularFirstAbsoluteMoment_nonneg d h
  have hM₀ : 0 ≤ M₀ := angularAbsoluteMass_nonneg d h
  have hC : 0 < C := mul_pos (by positivity) hApos
  have hK₁ : 0 < K₁ := mul_pos hC (by linarith)
  have hK₀ : 0 < K₀ := mul_pos hC (by linarith)
  refine ⟨K, add_pos hK₁ hK₀, fun t v hv => ?_⟩
  let w : ℝ := (1 + ‖t‖)^(-(N : ℝ))
  have hw : 0 ≤ w := Real.rpow_nonneg (by positivity) _
  have hbase : -t ∈ Metric.closedBall (-t) ‖v‖ :=
    Metric.mem_closedBall_self (norm_nonneg _)
  have hend : v - t ∈ Metric.closedBall (-t) ‖v‖ := by
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add, sub_add_cancel, le_refl]
  have ha₀ : ‖a (-t)‖ ≤ C * w :=
    neutralSharp_weighted_on_near_ball d N (fun x => ‖a x‖)
      (fun x => norm_nonneg _) A (fun x => (hA x).1) t v hv (-t) hbase
  have ha₁ : ‖a (v - t)‖ ≤ C * w :=
    neutralSharp_weighted_on_near_ball d N (fun x => ‖a x‖)
      (fun x => norm_nonneg _) A (fun x => (hA x).1) t v hv (v - t) hend
  have hdif : ∀ x : Rd d, DifferentiableAt ℝ a x :=
    (a.smooth 1).differentiable (by simp)
  have hdiff : ‖a (v - t) - a (-t)‖ ≤ (C * w) * ‖v‖ := by
    simpa only [sub_neg_eq_add, sub_add_cancel] using
      (Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
        (f := (a : Rd d → ℂ)) (x := -t) (y := v-t)
        (fun z _ => hdif z)
        (neutralSharp_weighted_on_near_ball d N (fun x => ‖fderiv ℝ a x‖)
          (fun x => norm_nonneg _) A (fun x => (hA x).2) t v hv)
        (convex_closedBall (-t) ‖v‖) hbase hend)
  have heq (x : Rd d) : a x = compactAngularAmplitude d χ x :=
    neutralSharpAngularSchwartz_apply d χ hsm x
  have hb0 : compactAngularAmplitude d h 0 = 1 := by
    simpa only [hh, Complex.ofReal_one] using compactAngularAmplitude_zero_integral d h
  have hbLip : ‖1 - compactAngularAmplitude d h v‖ ≤ ‖v‖ * M₁ := by
    calc
      _ = ‖compactAngularAmplitude d h v - compactAngularAmplitude d h 0‖ := by
        rw [hb0, norm_sub_rev]
      _ ≤ _ := by
        simpa only [sub_zero] using compactAngularAmplitude_sub_norm_le_firstMoment d h v 0
  have hb : ‖compactAngularAmplitude d h v‖ ≤ M₀ :=
    compactAngularAmplitude_norm_le_absoluteMass d h v
  have hz : neutralizedAngularAmplitude d χ h t v =
      (a (v-t)-a (-t)) + a (-t)*(1-compactAngularAmplitude d h v) := by
    simp only [neutralizedAngularAmplitude, heq]
    ring
  have hLip : ‖neutralizedAngularAmplitude d χ h t v‖ ≤ K₁ * w * ‖v‖ := by
    rw [hz]
    calc
      _ ≤ ‖a (v-t)-a (-t)‖ + ‖a (-t)‖ * ‖1-compactAngularAmplitude d h v‖ := by
        simpa only [norm_mul] using
          norm_add_le (a (v-t)-a (-t)) (a (-t)*(1-compactAngularAmplitude d h v))
      _ ≤ (C*w)*‖v‖ + (C*w)*(‖v‖*M₁) :=
        add_le_add hdiff (mul_le_mul ha₀ hbLip (norm_nonneg _) (mul_nonneg hC.le hw))
      _ = _ := by dsimp only [K₁]; ring
  have hBound : ‖neutralizedAngularAmplitude d χ h t v‖ ≤ K₀ * w := by
    have hz' : neutralizedAngularAmplitude d χ h t v =
        a (v-t)-a (-t)*compactAngularAmplitude d h v := by
      simp only [neutralizedAngularAmplitude, heq]
    rw [hz']
    calc
      _ ≤ ‖a (v-t)‖ + ‖a (-t)‖ * ‖compactAngularAmplitude d h v‖ := by
        simpa only [norm_mul] using norm_sub_le (a (v-t))
          (a (-t)*compactAngularAmplitude d h v)
      _ ≤ C*w + (C*w)*M₀ :=
        add_le_add ha₁ (mul_le_mul ha₀ hb (norm_nonneg _) (mul_nonneg hC.le hw))
      _ = _ := by dsimp only [K₀]; ring
  have h₁ : K₁ ≤ K := by dsimp only [K]; linarith
  have h₀ : K₀ ≤ K := by dsimp only [K]; linarith
  exact ⟨hLip.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h₁ hw) (norm_nonneg _)),
    hBound.trans (mul_le_mul_of_nonneg_right h₀ hw)⟩

private def neutralSharpRadialEnvelope (d : ℕ) (q : ℝ) (v : Rd d) : ℝ :=
  (Metric.ball (0 : Rd d) 1).indicator
      (fun v : Rd d => ‖v‖^(2-((d : ℝ)+q))) v +
    (2 : ℝ)^((d : ℝ)+q) * (1+‖v‖)^(-((d : ℝ)+q))

private theorem neutralSharpRadialEnvelope_nonneg
    (d : ℕ) (q : ℝ) (v : Rd d) : 0 ≤ neutralSharpRadialEnvelope d q v := by
  apply add_nonneg
  · exact Set.indicator_nonneg (fun x _ => Real.rpow_nonneg (norm_nonneg x) _) v
  · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by positivity) _)

private theorem neutralSharpRadialEnvelope_integrable
    (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2) :
    Integrable (neutralSharpRadialEnvelope d q) volume := by
  let p : ℝ := (d : ℝ)+q
  have hnear : IntegrableOn (fun v : Rd d => ‖v‖^(2-p))
      (Metric.ball 0 1) volume := by
    apply integrableOn_ball_of_norm_le_rpow
      (μ := volume) (f := fun v : Rd d => ‖v‖^(2-p))
      (C := 1) (α := p-2)
      (by simpa only [Rd, finrank_euclideanSpace_fin] using hd)
      (by simp only [Rd, finrank_euclideanSpace_fin]; dsimp only [p]; linarith)
    · refine Eventually.of_forall (fun v => ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg v) _), one_mul]
      exact le_of_eq (congrArg (fun e : ℝ => ‖v‖^e) (by ring))
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  have htail : Integrable (fun v : Rd d => (1+‖v‖)^(-p)) volume :=
    integrable_one_add_norm (E := Rd d) (μ := volume) (r := p) (by
      simp only [Rd, finrank_euclideanSpace_fin]; dsimp only [p]; linarith)
  exact (hnear.integrable_indicator Metric.isOpen_ball.measurableSet).add
    (htail.const_mul ((2 : ℝ)^p))

private theorem neutralSharp_near_integral_bound
    (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (χ h : C_c(Rd d, ℝ)) (hsm : ContDiff ℝ ∞ χ)
    (hh : (∫ x : Rd d, h x) = 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : Rd d,
      0 ≤ (∫ v in Metric.closedBall (0 : Rd d) (‖t‖/2),
        neutralizedFourierProfile d q χ h t v) ∧
      (∫ v in Metric.closedBall (0 : Rd d) (‖t‖/2),
        neutralizedFourierProfile d q χ h t v) ≤
          B * (1+‖t‖)^(-((2*d+2 : ℕ) : ℝ)) := by
  let p : ℝ := (d : ℝ)+q
  let N : ℕ := d+1
  let m : ℝ := ((2*d+2 : ℕ) : ℝ)
  let G : Rd d → ℝ := neutralSharpRadialEnvelope d q
  have hG := neutralSharpRadialEnvelope_integrable d hd q hq hqTwo
  have hG0 (v : Rd d) : 0 ≤ G v := neutralSharpRadialEnvelope_nonneg d q v
  rcases neutralSharp_weighted_near_cancellation d N χ h hsm hh with ⟨K, hK, hcancel⟩
  let J : ℝ := ∫ v : Rd d, G v
  have hJ : 0 ≤ J := integral_nonneg hG0
  refine ⟨K^2*J, mul_nonneg (sq_nonneg _) hJ, fun t => ?_⟩
  let E : Set (Rd d) := Metric.closedBall 0 (‖t‖/2)
  let w : ℝ := (1+‖t‖)^(-(N : ℝ))
  let b : ℝ := K^2*w^2
  have hw : 0 ≤ w := Real.rpow_nonneg (by positivity) _
  have hb : 0 ≤ b := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have heq : w^2 = (1+‖t‖)^(-m) := by
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 1+‖t‖)]
    congr 1
    dsimp only [N, m]
    push_cast
    ring
  have hfnn (v : Rd d) : 0 ≤ neutralizedFourierProfile d q χ h t v :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg v) _) (Complex.normSq_nonneg _)
  have hInt := (neutralizedFourierProfile_integrable d hd q hq hqTwo χ h hh t).1
  have hpoint (v : Rd d) (hv : v ∈ E) :
      neutralizedFourierProfile d q χ h t v ≤ b*G v := by
    have hv' : ‖v‖ ≤ ‖t‖/2 := by
      simpa only [E, Metric.mem_closedBall, dist_zero_right] using hv
    have hs₁ := pow_le_pow_left₀ (norm_nonneg _)
      (hcancel t v hv').1 2
    have hs₀ := pow_le_pow_left₀ (norm_nonneg _)
      (hcancel t v hv').2 2
    by_cases hball : v ∈ Metric.ball (0 : Rd d) 1
    · have hnear : neutralizedFourierProfile d q χ h t v ≤ b*‖v‖^(2-p) := by
        by_cases hv0 : v = 0
        · rw [hv0]
          simp only [neutralizedFourierProfile,
            neutralizedAngularAmplitude_zero d χ h hh t, Complex.normSq_zero, mul_zero]
          exact mul_nonneg hb (Real.rpow_nonneg (norm_nonneg _) _)
        · have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv0
          have hpow : ‖v‖^(-p)*‖v‖^2 = ‖v‖^(2-p) := by
            rw [← Real.rpow_two, ← Real.rpow_add hr]
            congr 1
            ring
          calc
            _ = ‖v‖^(-p)*‖neutralizedAngularAmplitude d χ h t v‖^2 := by
              simp only [neutralizedFourierProfile, p, Complex.normSq_eq_norm_sq]
            _ ≤ ‖v‖^(-p)*(K*w*‖v‖)^2 :=
              mul_le_mul_of_nonneg_left hs₁ (Real.rpow_nonneg hr.le _)
            _ = b*(‖v‖^(-p)*‖v‖^2) := by dsimp only [b]; ring
            _ = _ := congrArg (b * ·) hpow
      have hGnear : ‖v‖^(2-p) ≤ G v := by
        dsimp only [G, neutralSharpRadialEnvelope]
        rw [Set.indicator_of_mem hball]
        exact le_add_of_nonneg_right (mul_nonneg
          (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by positivity) _))
      exact hnear.trans (mul_le_mul_of_nonneg_left hGnear hb)
    · have hr : 1 ≤ ‖v‖ := le_of_not_gt (by
        simpa only [Metric.mem_ball, dist_zero_right] using hball)
      have hpower := neutralized_rpow_outside_one p ‖v‖
        (add_nonneg (Nat.cast_nonneg d) hq.le) hr
      calc
        _ = ‖v‖^(-p)*‖neutralizedAngularAmplitude d χ h t v‖^2 := by
          simp only [neutralizedFourierProfile, p, Complex.normSq_eq_norm_sq]
        _ ≤ ((2 : ℝ)^p*(1+‖v‖)^(-p))*(K*w)^2 :=
          mul_le_mul hpower hs₀ (sq_nonneg _)
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
              (Real.rpow_nonneg (by positivity) _))
        _ = b*G v := by
          simp only [G, neutralSharpRadialEnvelope, Set.indicator_of_notMem hball,
            zero_add, p, b]
          ring
  have hE : MeasurableSet E := Metric.isClosed_closedBall.measurableSet
  have hbound : (∫ v in E, neutralizedFourierProfile d q χ h t v) ≤ b*J := by
    calc
      _ ≤ ∫ v in E, b*G v :=
        integral_mono_ae hInt.restrict (hG.const_mul b).restrict (by
          filter_upwards [ae_restrict_mem hE] with v hv
          exact hpoint v hv)
      _ = b*(∫ v in E, G v) := integral_const_mul b G
      _ ≤ b*J := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hG (Eventually.of_forall hG0)) hb
  refine ⟨integral_nonneg hfnn, ?_⟩
  calc
    _ ≤ b*J := hbound
    _ = (K^2*J)*(1+‖t‖)^(-m) := by simp only [b, heq]; ring

private def neutralSharpTranslated
    (d : ℕ) (q : ℝ) (χ h : C_c(Rd d, ℝ)) (t z : Rd d) : ℝ :=
  {z : Rd d | ‖t‖/2 < ‖z+t‖}.indicator
    (fun z => (‖t‖/‖z+t‖)^((d : ℝ)+q) *
      Complex.normSq (compactAngularAmplitude d χ z -
        compactAngularAmplitude d χ (-t) * compactAngularAmplitude d h (z+t))) z

private theorem neutralSharpTranslated_measurable
    (d : ℕ) (q : ℝ) (χ h : C_c(Rd d, ℝ)) (t : Rd d) :
    Measurable (neutralSharpTranslated d q χ h t) := by
  have hset : MeasurableSet {z : Rd d | ‖t‖/2 < ‖z+t‖} :=
    measurableSet_lt measurable_const ((measurable_id.add measurable_const).norm)
  have hz : Measurable (fun z : Rd d => compactAngularAmplitude d χ z -
      compactAngularAmplitude d χ (-t) * compactAngularAmplitude d h (z+t)) :=
    (measurable_compactAngularAmplitude d χ).sub
      (measurable_const.mul ((measurable_compactAngularAmplitude d h).comp
        (measurable_id.add measurable_const)))
  exact (((measurable_const.div ((measurable_id.add measurable_const).norm)).pow_const _).mul
    (Complex.continuous_normSq.measurable.comp hz)).indicator hset

private theorem neutralSharpTranslated_nonneg
    (d : ℕ) (q : ℝ) (χ h : C_c(Rd d, ℝ)) (t z : Rd d) :
    0 ≤ neutralSharpTranslated d q χ h t z := by
  exact Set.indicator_nonneg (fun z _ => mul_nonneg
    (Real.rpow_nonneg (div_nonneg (norm_nonneg t) (norm_nonneg (z+t))) _)
    (Complex.normSq_nonneg _)) z

private theorem neutralSharp_peetre (d : ℕ) (t z : Rd d) :
    1+‖z‖ ≤ (1+‖t‖)*(1+‖z+t‖) := by
  have hz : ‖z‖ ≤ ‖z+t‖+‖t‖ := by
    simpa using norm_sub_le (z+t) t
  nlinarith [mul_nonneg (norm_nonneg t) (norm_nonneg (z+t))]

private theorem neutralSharp_peetre_rpow
    (d : ℕ) (t z : Rd d) (m : ℝ) (hm : 0 ≤ m) :
    (1+‖t‖)^(-m)*(1+‖z+t‖)^(-m) ≤ (1+‖z‖)^(-m) := by
  calc
    _ = ((1+‖t‖)*(1+‖z+t‖))^(-m) :=
      (Real.mul_rpow (by positivity) (by positivity)).symm
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity)
      (neutralSharp_peetre d t z) (neg_nonpos.mpr hm)

private theorem neutralSharp_normSq_sub (x y : ℂ) :
    Complex.normSq (x-y) ≤ 2*Complex.normSq x+2*Complex.normSq y := by
  simp only [Complex.normSq_eq_norm_sq]
  have h := pow_le_pow_left₀ (norm_nonneg (x-y)) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

private theorem neutralSharpTranslated_majorant
    (d : ℕ) (q : ℝ) (hq : 0 < q) (χ h : C_c(Rd d, ℝ))
    (hχsm : ContDiff ℝ ∞ χ) (hhsm : ContDiff ℝ ∞ h) :
    ∃ D : ℝ, 0 < D ∧ ∀ t z : Rd d,
      neutralSharpTranslated d q χ h t z ≤
        D*(1+‖z‖)^(-((2*d+2 : ℕ) : ℝ)) := by
  let p : ℝ := (d : ℝ)+q
  let m : ℝ := ((2*d+2 : ℕ) : ℝ)
  have hp : 0 ≤ p := add_nonneg (Nat.cast_nonneg d) hq.le
  have hm : 0 ≤ m := Nat.cast_nonneg _
  rcases compactSmoothWindow_angular_density_decay d χ hχsm with ⟨A, hA, hdecA⟩
  rcases compactSmoothWindow_angular_density_decay d h hhsm with ⟨B, hB, hdecB⟩
  let D : ℝ := (2 : ℝ)^p*(2*A+2*A*B)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, fun t z => ?_⟩
  have hprod : Complex.normSq
      (compactAngularAmplitude d χ (-t)*compactAngularAmplitude d h (z+t)) ≤
        A*B*(1+‖z‖)^(-m) := by
    rw [Complex.normSq_mul]
    have ht : Complex.normSq (compactAngularAmplitude d χ (-t)) ≤
        A*(1+‖t‖)^(-m) := by simpa only [norm_neg] using hdecA (-t)
    calc
      _ ≤ (A*(1+‖t‖)^(-m))*(B*(1+‖z+t‖)^(-m)) :=
        mul_le_mul ht (hdecB (z+t)) (Complex.normSq_nonneg _)
          (mul_nonneg hA.le (Real.rpow_nonneg (by positivity) _))
      _ = A*B*((1+‖t‖)^(-m)*(1+‖z+t‖)^(-m)) := by ring
      _ ≤ A*B*(1+‖z‖)^(-m) := mul_le_mul_of_nonneg_left
        (neutralSharp_peetre_rpow d t z m hm) (mul_nonneg hA.le hB.le)
  have hsq : Complex.normSq (compactAngularAmplitude d χ z -
      compactAngularAmplitude d χ (-t)*compactAngularAmplitude d h (z+t)) ≤
        (2*A+2*A*B)*(1+‖z‖)^(-m) := by
    have hh := neutralSharp_normSq_sub (compactAngularAmplitude d χ z)
      (compactAngularAmplitude d χ (-t)*compactAngularAmplitude d h (z+t))
    nlinarith [hdecA z, hprod]
  by_cases hfar : ‖t‖/2 < ‖z+t‖
  · rw [neutralSharpTranslated, Set.indicator_of_mem
      (show z ∈ {z : Rd d | ‖t‖/2 < ‖z+t‖} from hfar)]
    have hden : 0 < ‖z+t‖ := lt_of_le_of_lt (div_nonneg (norm_nonneg _) (by norm_num)) hfar
    have hratio0 : 0 ≤ ‖t‖/‖z+t‖ := div_nonneg (norm_nonneg _) hden.le
    have hratio2 : ‖t‖/‖z+t‖ ≤ 2 :=
      (div_le_iff₀ hden).2 (by linarith)
    calc
      _ ≤ (2 : ℝ)^p*((2*A+2*A*B)*(1+‖z‖)^(-m)) :=
        mul_le_mul (Real.rpow_le_rpow hratio0 hratio2 hp) hsq
          (Complex.normSq_nonneg _) (Real.rpow_nonneg (by norm_num) _)
      _ = _ := by dsimp only [D]; ring
  · rw [neutralSharpTranslated, Set.indicator_of_notMem
      (show z ∉ {z : Rd d | ‖t‖/2 < ‖z+t‖} from hfar)]
    exact mul_nonneg hD.le (Real.rpow_nonneg (by positivity) _)

private theorem neutralSharpTranslated_integral_eq
    (d : ℕ) (q : ℝ) (χ h : C_c(Rd d, ℝ)) (t : Rd d) :
    (∫ z : Rd d, neutralSharpTranslated d q χ h t z) =
      ‖t‖^((d : ℝ)+q) *
        (∫ v in (Metric.closedBall (0 : Rd d) (‖t‖/2))ᶜ,
          neutralizedFourierProfile d q χ h t v) := by
  let p : ℝ := (d : ℝ)+q
  let E : Set (Rd d) := Metric.closedBall 0 (‖t‖/2)
  let g : Rd d → ℝ := Eᶜ.indicator (neutralizedFourierProfile d q χ h t)
  have hpoint (z : Rd d) : neutralSharpTranslated d q χ h t z = ‖t‖^p*g (z+t) := by
    by_cases hfar : ‖t‖/2 < ‖z+t‖
    · have hz : z+t ∈ Eᶜ := by
        simpa only [E, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
          not_le] using hfar
      simp only [neutralSharpTranslated, Set.indicator_of_mem
          (show z ∈ {z : Rd d | ‖t‖/2 < ‖z+t‖} from hfar),
        g, Set.indicator_of_mem hz, neutralizedFourierProfile,
        neutralizedAngularAmplitude, add_sub_cancel_right]
      rw [Real.div_rpow (norm_nonneg _) (norm_nonneg _) p,
        div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg _)]
      ring
    · have hz : z+t ∉ Eᶜ := by
        simpa only [E, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
          not_not] using le_of_not_gt hfar
      simp only [neutralSharpTranslated, Set.indicator_of_notMem
          (show z ∉ {z : Rd d | ‖t‖/2 < ‖z+t‖} from hfar),
        g, Set.indicator_of_notMem hz, mul_zero]
  calc
    _ = ∫ z : Rd d, ‖t‖^p*g (z+t) :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = ‖t‖^p*(∫ z : Rd d, g (z+t)) :=
      integral_const_mul (‖t‖^p) (fun z : Rd d => g (z+t))
    _ = ‖t‖^p*(∫ v : Rd d, g v) := congrArg (‖t‖^p * ·)
      (integral_add_right_eq_self g t)
    _ = _ := congrArg (‖t‖^p * ·)
      (integral_indicator Metric.isClosed_closedBall.measurableSet.compl)

private theorem neutralSharpTranslated_pointwise_tendsto
    (d : ℕ) (q : ℝ) (χ h : C_c(Rd d, ℝ)) (hχsm : ContDiff ℝ ∞ χ)
    (t : ℕ → Rd d) (ht : Tendsto (fun n => ‖t n‖) atTop atTop) (z : Rd d) :
    Tendsto (fun n => neutralSharpTranslated d q χ h (t n) z) atTop
      (𝓝 (Complex.normSq (compactAngularAmplitude d χ z))) := by
  let p : ℝ := (d : ℝ)+q
  let T : ℕ → ℝ := fun n => ‖t n‖
  let R : ℕ → ℝ := fun n => ‖z+t n‖
  have hT : Tendsto T atTop atTop := ht
  have hreverse (n : ℕ) : |R n-T n| ≤ ‖z‖ := by
    simpa only [R, T, add_sub_cancel_right] using abs_norm_sub_norm_le (z+t n) (t n)
  have hpos : ∀ᶠ n in atTop, 0 < T n := hT.eventually (eventually_gt_atTop 0)
  have habs : Tendsto (fun n => |R n/T n-1|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _))
      _ (hT.const_div_atTop ‖z‖)
    filter_upwards [hpos] with n hn
    have heq : R n/T n-1 = (R n-T n)/T n := by rw [sub_div, div_self hn.ne']
    rw [heq, abs_div, abs_of_pos hn]
    exact div_le_div_of_nonneg_right (hreverse n) hn.le
  have hratio : Tendsto (fun n => R n/T n) atTop (𝓝 1) :=
    tendsto_iff_dist_tendsto_zero.2 (by simpa only [Real.dist_eq] using habs)
  have hinverse : Tendsto (fun n => T n/R n) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using hratio.inv₀ one_ne_zero
  have hpower : Tendsto (fun n => (T n/R n)^p) atTop (𝓝 1) := by
    simpa only [Real.one_rpow] using hinverse.rpow_const (.inl one_ne_zero)
  have hfar : ∀ᶠ n in atTop, T n/2 < R n := by
    filter_upwards [hT.eventually (eventually_gt_atTop (2*‖z‖))] with n hn
    have hlower := (abs_le.mp (hreverse n)).1
    linarith
  have hneg : Tendsto (fun n => -t n) atTop (cocompact (Rd d)) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.1 (by simpa only [norm_neg] using ht)
  have hat : Tendsto (fun n => compactAngularAmplitude d χ (-t n)) atTop (𝓝 0) :=
    Filter.Tendsto.congr'
      (Eventually.of_forall (fun n => neutralSharpAngularSchwartz_apply d χ hχsm (-t n)))
      ((neutralSharpAngularSchwartz d χ hχsm).tendsto_cocompact.comp hneg)
  have hcorNorm : Tendsto (fun n => ‖compactAngularAmplitude d χ (-t n)*
      compactAngularAmplitude d h (z+t n)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => ?_) (by simpa only [norm_zero, zero_mul] using
        hat.norm.mul_const (angularAbsoluteMass d h))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (compactAngularAmplitude_norm_le_absoluteMass d h (z+t n)) (norm_nonneg _)
  have hcor : Tendsto (fun n => compactAngularAmplitude d χ (-t n)*
      compactAngularAmplitude d h (z+t n)) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.2 (by simpa only [dist_zero_right] using hcorNorm)
  have hz : Tendsto (fun n => compactAngularAmplitude d χ z -
      compactAngularAmplitude d χ (-t n)*compactAngularAmplitude d h (z+t n))
      atTop (𝓝 (compactAngularAmplitude d χ z)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hcor
  have hsq := (Complex.continuous_normSq.tendsto _).comp hz
  have hbody := hpower.mul hsq
  exact Filter.Tendsto.congr'
    (f₁ := fun n => (T n / R n)^p * Complex.normSq
      (compactAngularAmplitude d χ z - compactAngularAmplitude d χ (-t n) *
        compactAngularAmplitude d h (z+t n)))
    (hfar.mono (fun n hn => by
      simp only [neutralSharpTranslated, Set.indicator_of_mem
        (show z ∈ {z : Rd d | ‖t n‖/2 < ‖z+t n‖} from hn), T, R, p]))
    (by simpa only [Function.comp_def, one_mul] using hbody)

private theorem neutralSharp_far_integral_control
    (d : ℕ) (q : ℝ) (hq : 0 < q) (χ h : C_c(Rd d, ℝ))
    (hχsm : ContDiff ℝ ∞ χ) (hhsm : ContDiff ℝ ∞ h) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ t : Rd d, (∫ z : Rd d, neutralSharpTranslated d q χ h t z) ≤ B) ∧
      ∀ t : ℕ → Rd d, Tendsto (fun n => ‖t n‖) atTop atTop →
        Tendsto (fun n => ∫ z : Rd d, neutralSharpTranslated d q χ h (t n) z) atTop
          (𝓝 ((2*Real.pi)^d*(∫ x : Rd d, (χ x)^2))) := by
  let m : ℝ := ((2*d+2 : ℕ) : ℝ)
  rcases neutralSharpTranslated_majorant d q hq χ h hχsm hhsm with ⟨D, hD, hbound⟩
  let g : Rd d → ℝ := fun z => D*(1+‖z‖)^(-m)
  have hgm : Integrable g volume :=
    (integrable_one_add_norm (E := Rd d) (μ := volume) (r := m) (by
      simp only [Rd, finrank_euclideanSpace_fin]
      dsimp only [m]
      push_cast
      linarith)).const_mul D
  have hg0 (z : Rd d) : 0 ≤ g z := mul_nonneg hD.le
    (Real.rpow_nonneg (by positivity) _)
  have hInt (t : Rd d) : Integrable (neutralSharpTranslated d q χ h t) volume :=
    hgm.mono' (neutralSharpTranslated_measurable d q χ h t).aestronglyMeasurable
      (Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (neutralSharpTranslated_nonneg d q χ h t z)]
        exact hbound t z))
  refine ⟨∫ z : Rd d, g z, integral_nonneg hg0, fun t => ?_, fun t ht => ?_⟩
  · exact integral_mono_ae (hInt t) hgm (Eventually.of_forall (hbound t))
  · have hlim := tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure (Rd d)))
      (F := fun n z => neutralSharpTranslated d q χ h (t n) z)
      (f := fun z => Complex.normSq (compactAngularAmplitude d χ z)) g
      (fun n => (neutralSharpTranslated_measurable d q χ h (t n)).aestronglyMeasurable)
      hgm (fun n => Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (neutralSharpTranslated_nonneg d q χ h (t n) z)]
        exact hbound (t n) z))
      (Eventually.of_forall (neutralSharpTranslated_pointwise_tendsto d q χ h hχsm t ht))
    rw [compactSmoothWindow_angular_plancherel d χ hχsm] at hlim
    exact hlim

private theorem neutralSharp_scaled_near_control
    (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (χ h : C_c(Rd d, ℝ)) (hχsm : ContDiff ℝ ∞ χ)
    (hh : (∫ x : Rd d, h x) = 1) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ t : Rd d, ‖t‖^((d : ℝ)+q) *
        (∫ v in Metric.closedBall (0 : Rd d) (‖t‖/2),
          neutralizedFourierProfile d q χ h t v) ≤ B) ∧
      ∀ t : ℕ → Rd d, Tendsto (fun n => ‖t n‖) atTop atTop →
        Tendsto (fun n => ‖t n‖^((d : ℝ)+q) *
          (∫ v in Metric.closedBall (0 : Rd d) (‖t n‖/2),
            neutralizedFourierProfile d q χ h (t n) v)) atTop (𝓝 0) := by
  let p : ℝ := (d : ℝ)+q
  let m : ℝ := ((2*d+2 : ℕ) : ℝ)
  have hp : 0 ≤ p := add_nonneg (Nat.cast_nonneg d) hq.le
  have hpm : p < m := by
    dsimp only [p, m]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) d]
  rcases neutralSharp_near_integral_bound d hd q hq hqTwo χ h hχsm hh with
    ⟨B, hB, hnear⟩
  have hscaled (t : Rd d) : ‖t‖^p *
      (∫ v in Metric.closedBall (0 : Rd d) (‖t‖/2),
        neutralizedFourierProfile d q χ h t v) ≤ B*(1+‖t‖)^(p-m) := by
    calc
      _ ≤ ‖t‖^p*(B*(1+‖t‖)^(-m)) :=
        mul_le_mul_of_nonneg_left (hnear t).2 (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ (1+‖t‖)^p*(B*(1+‖t‖)^(-m)) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (norm_nonneg _) (by linarith) hp)
          (mul_nonneg hB (Real.rpow_nonneg (by positivity) _))
      _ = B*(1+‖t‖)^(p-m) := by
        rw [show p-m = p+(-m) by ring, Real.rpow_add (by positivity) p (-m)]
        ring
  refine ⟨B, hB, fun t => ?_, fun t ht => ?_⟩
  · have hpow : (1+‖t‖)^(p-m) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_le
          (show 1 ≤ 1+‖t‖ by linarith [norm_nonneg t]) (sub_nonpos.mpr hpm.le))
    exact (hscaled t).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hB)
  · have hlarge : Tendsto (fun n => 1+‖t n‖) atTop atTop :=
      tendsto_atTop_mono (fun n => by linarith) ht
    have hpow : Tendsto (fun n => B*(1+‖t n‖)^(p-m)) atTop (𝓝 0) := by
      have hdecay := (tendsto_rpow_neg_atTop (sub_pos.mpr hpm)).comp hlarge
      simpa only [Function.comp_def, show p-m = -(m-p) by ring, mul_zero] using hdecay.const_mul B
    exact squeeze_zero (fun n => mul_nonneg
      (Real.rpow_nonneg (norm_nonneg _) _) (hnear (t n)).1)
      (fun n => hscaled (t n)) hpow

private theorem neutralSharp_full_split
    (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (χ h : C_c(Rd d, ℝ)) (hh : (∫ x : Rd d, h x) = 1) (t : Rd d) :
    ‖t‖^((d : ℝ)+q)*neutralizedFourierF d q χ h t =
      ‖t‖^((d : ℝ)+q)*
        (∫ v in Metric.closedBall (0 : Rd d) (‖t‖/2),
          neutralizedFourierProfile d q χ h t v) +
      (∫ z : Rd d, neutralSharpTranslated d q χ h t z) := by
  have hInt := (neutralizedFourierProfile_integrable d hd q hq hqTwo χ h hh t).1
  rw [neutralSharpTranslated_integral_eq, neutralizedFourierF,
    ← integral_add_compl (μ := (volume : Measure (Rd d)))
      (f := neutralizedFourierProfile d q χ h t)
      (s := Metric.closedBall (0 : Rd d) (‖t‖/2))
      Metric.isClosed_closedBall.measurableSet hInt]
  ring

theorem neutralizedFourierF_scaled_bound_and_sharp_limit
    (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (χ h : C_c(Rd d, ℝ)) (hχsm : ContDiff ℝ ∞ χ) (hhsm : ContDiff ℝ ∞ h)
    (hh : (∫ x : Rd d, h x) = 1) :
    ∃ C : ℝ, 0 < C ∧
      (∀ t : Rd d, ‖t‖^((d : ℝ)+q)*neutralizedFourierF d q χ h t ≤ C) ∧
      ∀ t : ℕ → Rd d, Tendsto (fun n => ‖t n‖) atTop atTop →
        Tendsto (fun n => ‖t n‖^((d : ℝ)+q)*neutralizedFourierF d q χ h (t n))
          atTop (𝓝 ((2*Real.pi)^d*(∫ x : Rd d, (χ x)^2))) := by
  rcases neutralSharp_scaled_near_control d hd q hq hqTwo χ h hχsm hh with
    ⟨Bnear, hBnear, hnearBound, hnearLimit⟩
  rcases neutralSharp_far_integral_control d q hq χ h hχsm hhsm with
    ⟨Bfar, hBfar, hfarBound, hfarLimit⟩
  refine ⟨Bnear+Bfar+1, by linarith, fun t => ?_, fun t ht => ?_⟩
  · rw [neutralSharp_full_split d hd q hq hqTwo χ h hh t]
    linarith [hnearBound t, hfarBound t]
  · have hsum := (hnearLimit t ht).add (hfarLimit t ht)
    have heq : (fun n => ‖t n‖^((d : ℝ)+q)*neutralizedFourierF d q χ h (t n)) =
        (fun n => ‖t n‖^((d : ℝ)+q)*
          (∫ v in Metric.closedBall (0 : Rd d) (‖t n‖/2),
            neutralizedFourierProfile d q χ h (t n) v) +
          (∫ z : Rd d, neutralSharpTranslated d q χ h (t n) z)) :=
      funext (fun n => neutralSharp_full_split d hd q hq hqTwo χ h hh (t n))
    rw [heq]
    simpa only [zero_add] using hsum

end Riesz.Stationary
