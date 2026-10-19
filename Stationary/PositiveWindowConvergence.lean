import Riesz.Stationary.AngularMellinEstimates
import Riesz.Stationary.AngularSpectrumPolynomialTail
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Riesz.Stationary.GridEnergyPositive

/-! Actual compact-window convolution identities and positive energy limits. -/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Configuration Filter
open scoped ENNReal Topology CompactlySupported RealInnerProductSpace FourierTransform

namespace Riesz.Stationary

def compactAngularDensity (d : ℕ) (χ : C_c(Rd d, ℝ)) (k : Rd d) : ℝ :=
  Complex.normSq (compactAngularAmplitude d χ k)

def angularDilatedDensity (d : ℕ) (R : Rd d → ℝ) (L : ℝ) (z : Rd d) : ℝ :=
  L ^ d * R (L • z)

def angularScaledCompactWindow
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) : C_c(Rd d, ℝ) :=
  ⟨⟨fun x => χ (L⁻¹ • x),
      χ.continuous.comp (continuous_const_smul _)⟩,
    χ.hasCompactSupport.comp_smul (inv_ne_zero hL.ne')⟩

theorem compactAngularDensity_nonneg
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (k : Rd d) :
    0 ≤ compactAngularDensity d χ k := by
  exact Complex.normSq_nonneg _

theorem measurable_compactAngularDensity
    (d : ℕ) (χ : C_c(Rd d, ℝ)) :
    Measurable (compactAngularDensity d χ) := by
  exact Complex.continuous_normSq.measurable.comp (measurable_compactAngularAmplitude d χ)

@[simp] theorem angularScaledCompactWindow_apply
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) (x : Rd d) :
    angularScaledCompactWindow d χ L hL x = χ (L⁻¹ • x) := by
  rfl

theorem angularScaledCompactWindow_nonneg
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℝ) (hL : 0 < L) :
    ∀ x, 0 ≤ angularScaledCompactWindow d χ L hL x := by
  exact fun x => hχ (L⁻¹ • x)

theorem compactAngularAmplitude_comp_inv_smul
    (d : ℕ) (χ : Rd d → ℝ) (L : ℝ) (hL : 0 < L) (k : Rd d) :
    compactAngularAmplitude d (fun x => χ (L⁻¹ • x)) k =
      ((L ^ d : ℝ) : ℂ) * compactAngularAmplitude d χ (L • k) := by
  let f : Rd d → ℂ := fun x =>
    (χ x : ℂ) * Complex.exp ((inner ℝ (L • k) x : ℂ) * Complex.I)
  have hi (x : Rd d) : inner ℝ (L • k) (L⁻¹ • x) = inner ℝ k x := by
    rw [real_inner_smul_left, real_inner_smul_right,
      ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  have hcv : (∫ x : Rd d, f (L⁻¹ • x)) = (L ^ d : ℝ) • ∫ x : Rd d, f x := by
    simpa only [Rd, finrank_euclideanSpace_fin] using
      (Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Rd d)) f hL.le)
  refine Eq.trans ?_ hcv
  refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
  change (χ (L⁻¹ • x) : ℂ) * Complex.exp ((inner ℝ k x : ℂ) * Complex.I) =
    (χ (L⁻¹ • x) : ℂ) *
      Complex.exp ((inner ℝ (L • k) (L⁻¹ • x) : ℂ) * Complex.I)
  rw [hi x]

theorem compactAngularDensity_scaled
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) (k : Rd d) :
    compactAngularDensity d (angularScaledCompactWindow d χ L hL) k =
      L ^ d * angularDilatedDensity d (compactAngularDensity d χ) L k := by
  change Complex.normSq
      (compactAngularAmplitude d (fun x => χ (L⁻¹ • x)) k) =
    L ^ d * (L ^ d * Complex.normSq (compactAngularAmplitude d χ (L • k)))
  rw [compactAngularAmplitude_comp_inv_smul d χ L hL k,
    Complex.normSq_mul, Complex.normSq_ofReal]
  exact mul_assoc _ _ _

theorem compactAngularHeadJ_eq_mellinConvolution
    (d : ℕ) (s : ℝ) (χ : C_c(Rd d, ℝ)) (k : Rd d) :
    compactAngularHeadJ d s χ k =
      ∫⁻ y : Rd d, angularMellinKernel d s y *
        ENNReal.ofReal (compactAngularDensity d χ (k - y)) := by
  refine (lintegral_lintegral_swap
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (ν := (volume : Measure (Rd d)))
    (f := fun u y => angularHeadBaseNN d s (u, y) *
      ENNReal.ofReal (compactAngularDensity d χ (k - y)))
    (measurable_compactAngularHeadJ_integrand d s χ k).aemeasurable).trans ?_
  exact lintegral_congr (fun y => lintegral_mul_const'
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (ENNReal.ofReal (compactAngularDensity d χ (k - y)))
    (fun u => angularHeadBaseNN d s (u, y)) ENNReal.ofReal_ne_top)

theorem compactAngularHeadJ_scaled_eq_mellinConvolution
    (d : ℕ) (s : ℝ) (χ : C_c(Rd d, ℝ))
    (L : ℝ) (hL : 0 < L) (k : Rd d) :
    (ENNReal.ofReal (L ^ d))⁻¹ *
        compactAngularHeadJ d s (angularScaledCompactWindow d χ L hL) k =
      ∫⁻ y : Rd d, angularMellinKernel d s y *
        ENNReal.ofReal (angularDilatedDensity d (compactAngularDensity d χ) L (k - y)) := by
  let r : ℝ≥0∞ := ENNReal.ofReal (L ^ d)
  let H : Rd d → ℝ≥0∞ := fun y => angularMellinKernel d s y *
    ENNReal.ofReal (angularDilatedDensity d (compactAngularDensity d χ) L (k - y))
  have hr0 : r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hL d))
  have hrT : r ≠ ∞ := ENNReal.ofReal_ne_top
  have hscale (y : Rd d) : ENNReal.ofReal
      (compactAngularDensity d (angularScaledCompactWindow d χ L hL) (k - y)) =
      r * ENNReal.ofReal (angularDilatedDensity d (compactAngularDensity d χ) L (k - y)) := by
    rw [compactAngularDensity_scaled d χ L hL (k - y),
      ENNReal.ofReal_mul (pow_nonneg hL.le d)]
  have hJ : compactAngularHeadJ d s (angularScaledCompactWindow d χ L hL) k =
      r * ∫⁻ y : Rd d, H y := by
    rw [compactAngularHeadJ_eq_mellinConvolution]
    refine (lintegral_congr (fun y => ?_)).trans (lintegral_const_mul' r H hrT)
    rw [hscale y]
    exact mul_left_comm _ _ _
  exact (congrArg (fun z : ℝ≥0∞ => r⁻¹ * z) hJ).trans
    (ENNReal.inv_mul_cancel_left hr0 hrT)

theorem compactAngularHeadJ_scaled_mellin_real
    (d : ℕ) (s : ℝ) (hs : 0 < s)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℝ) (hL : 0 < L) (k : Rd d) :
    (∫⁻ y : Rd d, angularMellinKernel d s y *
        ENNReal.ofReal (angularDilatedDensity d (compactAngularDensity d χ) L (k - y))) ≠ ∞ ∧
    Integrable (fun y : Rd d => (angularMellinKernel d s y).toReal *
      angularDilatedDensity d (compactAngularDensity d χ) L (k - y)) volume ∧
    (L ^ d)⁻¹ * (compactAngularHeadJ d s (angularScaledCompactWindow d χ L hL) k).toReal =
      ∫ y : Rd d, (angularMellinKernel d s y).toReal *
        angularDilatedDensity d (compactAngularDensity d χ) L (k - y) := by
  let φ := angularScaledCompactWindow d χ L hL
  let r : ℝ≥0∞ := ENNReal.ofReal (L ^ d)
  let D : Rd d → ℝ := angularDilatedDensity d (compactAngularDensity d χ) L
  let H : Rd d → ℝ≥0∞ := fun y => angularMellinKernel d s y * ENNReal.ofReal (D (k - y))
  have hφ : ∀ x, 0 ≤ φ x := fun x => hχ (L⁻¹ • x)
  have hr0 : r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hL d))
  have hDm : Measurable D := measurable_const.mul
    ((measurable_compactAngularDensity d χ).comp (measurable_const_smul L))
  have hDn (z : Rd d) : 0 ≤ D z :=
    mul_nonneg (pow_nonneg hL.le d) (compactAngularDensity_nonneg d χ _)
  have hHm : Measurable H := (measurable_angularMellinKernel d s).mul
    ((hDm.comp (measurable_const.sub measurable_id)).ennreal_ofReal)
  have hnn : r⁻¹ * compactAngularHeadJ d s φ k = ∫⁻ y : Rd d, H y :=
    compactAngularHeadJ_scaled_eq_mellinConvolution d s χ L hL k
  have hfin : (∫⁻ y : Rd d, H y) ≠ ∞ :=
    hnn.symm.trans_ne (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hr0)
      (compactAngularHeadJ_ne_top d s hs φ hφ k))
  have heq (y : Rd d) : (H y).toReal = (angularMellinKernel d s y).toReal * D (k - y) := by
    simp only [H, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hDn (k - y))]
  have hint : Integrable
      (fun y : Rd d => (angularMellinKernel d s y).toReal * D (k - y)) volume :=
    (integrable_toReal_of_lintegral_ne_top hHm.aemeasurable hfin).congr
      (Eventually.of_forall heq)
  have hvalue : (∫ y : Rd d, (angularMellinKernel d s y).toReal * D (k - y)) =
      (∫⁻ y : Rd d, H y).toReal :=
    (integral_congr_ae (Eventually.of_forall heq)).symm.trans
      (integral_toReal hHm.aemeasurable (ae_lt_top hHm hfin))
  have hconvert : (L ^ d)⁻¹ * (compactAngularHeadJ d s φ k).toReal =
      (∫⁻ y : Rd d, H y).toReal := by
    simpa only [r, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (pow_nonneg hL.le d)] using congrArg ENNReal.toReal hnn
  exact ⟨hfin, hint, hconvert.trans hvalue.symm⟩

section SmoothWindows

open scoped ContDiff

private def compactSmoothWindowComplexSchwartz
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hsm : ContDiff ℝ ∞ χ) : SchwartzMap (Rd d) ℂ := by
  have hcs : HasCompactSupport (Complex.ofRealCLM ∘ (χ : Rd d → ℝ)) :=
    χ.hasCompactSupport.comp_left rfl
  exact hcs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hsm)

private theorem compactSmoothWindow_angular_fourier_frequency
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hsm : ContDiff ℝ ∞ χ) (ξ : Rd d) :
    compactAngularAmplitude d χ ((2 * Real.pi) • ξ) =
      (𝓕 (compactSmoothWindowComplexSchwartz d χ hsm)) (-ξ) := by
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

theorem compactSmoothWindow_angular_plancherel
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hsm : ContDiff ℝ ∞ χ) :
    (∫ k : Rd d, Complex.normSq (compactAngularAmplitude d χ k)) =
      (2 * Real.pi)^d * (∫ x : Rd d, (χ x)^2) := by
  let f : SchwartzMap (Rd d) ℂ := compactSmoothWindowComplexSchwartz d χ hsm
  have hτ : 0 < 2 * Real.pi := by positivity
  have hA (k : Rd d) : compactAngularAmplitude d χ k =
      (𝓕 f) (-((2 * Real.pi)⁻¹ • k)) := by
    simpa only [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul] using
      compactSmoothWindow_angular_fourier_frequency d χ hsm ((2 * Real.pi)⁻¹ • k)
  have hPlancherel : (∫ ξ : Rd d, Complex.normSq ((𝓕 f) ξ)) =
      ∫ x : Rd d, (χ x)^2 := by
    calc
      _ = ∫ ξ : Rd d, ‖(𝓕 f) ξ‖^2 := integral_congr_ae
        (Eventually.of_forall (fun ξ => Complex.normSq_eq_norm_sq ((𝓕 f) ξ)))
      _ = ∫ x : Rd d, ‖f x‖^2 := SchwartzMap.integral_norm_sq_fourier f
      _ = _ := by
        apply integral_congr_ae
        refine Eventually.of_forall (fun x => ?_)
        change ‖(χ x : ℂ)‖^2 = (χ x)^2
        simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ = ∫ k : Rd d, Complex.normSq ((𝓕 f) (-((2 * Real.pi)⁻¹ • k))) :=
      integral_congr_ae (Eventually.of_forall (fun k => congrArg Complex.normSq (hA k)))
    _ = (2 * Real.pi)^d * (∫ ξ : Rd d, Complex.normSq ((𝓕 f) (-ξ))) := by
      simpa only [Rd, finrank_euclideanSpace_fin, smul_eq_mul] using
        (Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Rd d))
          (fun ξ : Rd d => Complex.normSq ((𝓕 f) (-ξ))) (R := 2 * Real.pi) hτ.le)
    _ = (2 * Real.pi)^d * (∫ ξ : Rd d, Complex.normSq ((𝓕 f) ξ)) :=
      congrArg (fun a : ℝ => (2 * Real.pi)^d * a)
        (integral_neg_eq_self (fun ξ : Rd d => Complex.normSq ((𝓕 f) ξ)) volume)
    _ = _ := congrArg (fun a : ℝ => (2 * Real.pi)^d * a) hPlancherel

theorem compactSmoothWindow_angular_density_decay
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hsm : ContDiff ℝ ∞ χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : Rd d,
      Complex.normSq (compactAngularAmplitude d χ k) ≤
        C * (1 + ‖k‖)^(-((2*d+2 : ℕ) : ℝ)) := by
  let f : SchwartzMap (Rd d) ℂ := compactSmoothWindowComplexSchwartz d χ hsm
  let G : SchwartzMap (Rd d) ℂ := 𝓕 f
  let n : ℕ := d + 1
  let τ : ℝ := 2 * Real.pi
  have hτ : 0 < τ := by positivity
  let B : ℝ := (2 : ℝ)^n *
    (Finset.Iic (n,0)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) G
  have hB (q : Rd d) : (1 + ‖q‖)^n * ‖G q‖ ≤ B := by
    simpa only [B, norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℂ) (m := (n,0)) (k := n) (n := 0) le_rfl le_rfl G q)
  let b : ℝ := max 1 τ
  let D : ℝ := b^n * max B 1
  have hb : 0 < b := zero_lt_one.trans_le (le_max_left 1 τ)
  have hD : 0 < D := mul_pos (pow_pos hb n)
    (zero_lt_one.trans_le (le_max_right B 1))
  refine ⟨D^2, sq_pos_of_pos hD, fun k => ?_⟩
  let q : Rd d := -(τ⁻¹ • k)
  have hA : compactAngularAmplitude d χ k = G q := by
    simpa only [τ, G, f, q, smul_smul,
      mul_inv_cancel₀ (show 2 * Real.pi ≠ 0 from hτ.ne'), one_smul] using
      compactSmoothWindow_angular_fourier_frequency d χ hsm (τ⁻¹ • k)
  have hk : τ • (-q) = k := by
    dsimp only [q]
    rw [neg_neg, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  have hnorm : ‖k‖ = τ * ‖q‖ := by
    calc
      ‖k‖ = ‖τ • (-q)‖ := congrArg norm hk.symm
      _ = τ * ‖q‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ, norm_neg]
  have hrad : 1 + ‖k‖ ≤ b * (1 + ‖q‖) := by
    rw [hnorm]
    have h1 : 1 ≤ b := le_max_left 1 τ
    nlinarith [mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) τ) (norm_nonneg q)]
  have hweighted : (1 + ‖k‖)^n * ‖compactAngularAmplitude d χ k‖ ≤ D := by
    rw [hA]
    calc
      _ ≤ (b * (1 + ‖q‖))^n * ‖G q‖ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hrad n) (norm_nonneg _)
      _ = b^n * ((1 + ‖q‖)^n * ‖G q‖) := by simp only [mul_pow, mul_assoc]
      _ ≤ D := mul_le_mul_of_nonneg_left
        ((hB q).trans (le_max_left B 1)) (pow_nonneg hb.le n)
  have hdec : ‖compactAngularAmplitude d χ k‖ ≤ D * (1 + ‖k‖)^(-(n : ℝ)) := by
    have hh : ‖compactAngularAmplitude d χ k‖ ≤ D / (1 + ‖k‖)^n :=
      (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖k‖) n)).2
        (by simpa only [mul_comm] using hweighted)
    simpa only [div_eq_mul_inv, ← Real.rpow_natCast,
      ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖k‖)] using hh
  rw [Complex.normSq_eq_norm_sq]
  calc
    _ ≤ (D * (1 + ‖k‖)^(-(n : ℝ)))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hdec 2
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 1 + ‖k‖)]
      congr 2
      norm_num [n]
      ring

end SmoothWindows

private def angularPolyTail {d : ℕ} (m : ℕ) (x : Rd d) : ℝ := (1+‖x‖)^(-(m:ℝ))

private def angularUnitRiesz {d : ℕ} (α : ℝ) (x : Rd d) : ℝ :=
  (Metric.ball (0 : Rd d) 1).indicator (fun z => ‖z‖^(-α)) x

private theorem weighted_density_decay
    (d m : ℕ) {α C r f : ℝ} (hr : 1 ≤ r) (hα : α ≤ (d:ℝ))
    (hf : 0 ≤ f) (hdec : f ≤ C*r^(-((d+m:ℕ):ℝ))) :
    r^α*f ≤ C*r^(-(m:ℝ)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  calc
    _ ≤ r^(d:ℝ)*f := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hr hα) hf
    _ ≤ r^(d:ℝ)*(C*r^(-((d+m:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_left hdec (Real.rpow_nonneg hr0.le _)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hr0]
      simp [Nat.cast_add]

private theorem one_add_norm_sub_bound {d : ℕ} (x y : Rd d) :
    1+‖x‖ ≤ (1+‖x-y‖)*(1+‖y‖) := by
  have hn : ‖x‖ ≤ ‖x-y‖+‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-y) y
  nlinarith [mul_nonneg (norm_nonneg (x-y)) (norm_nonneg y)]

private theorem weighted_riesz_outside_one {α r : ℝ} (hα : 0 ≤ α) (hr : 1 ≤ r) :
    (1+r)^α*r^(-α) ≤ (2:ℝ)^α := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  calc
    _ = ((1+r)/r)^α := by
      rw [Real.div_rpow (by positivity : (0:ℝ)≤1+r) hr0.le,
        Real.rpow_neg hr0.le, div_eq_mul_inv]
    _ ≤ _ := Real.rpow_le_rpow (div_nonneg (by positivity) hr0.le)
      ((div_le_iff₀ hr0).2 (by linarith)) hα

private theorem weighted_riesz_single_majorant
    (d m : ℕ) (α : ℝ) (hα : 0 ≤ α) (hαd : α ≤ (d:ℝ))
    (R : Rd d → ℝ) (hR : ∀ y, 0 ≤ R y) (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ y, R y ≤ C*(1+‖y‖)^(-((d+m:ℕ):ℝ))) (x y : Rd d) :
    (1+‖x‖)^α*(‖x-y‖^(-α)*R y) ≤
      ((2:ℝ)^α*C)*(angularUnitRiesz α (x-y)+angularPolyTail m y) := by
  have hpow : (1+‖x‖)^α ≤ (1+‖x-y‖)^α*(1+‖y‖)^α :=
    (Real.rpow_le_rpow (by positivity : (0:ℝ)≤1+‖x‖)
      (one_add_norm_sub_bound x y) hα).trans_eq
        (Real.mul_rpow (by positivity) (by positivity))
  have hcore : (1+‖x‖)^α*(‖x-y‖^(-α)*R y) ≤
      ((1+‖x-y‖)^α*‖x-y‖^(-α))*((1+‖y‖)^α*R y) := by
    calc
      _ ≤ ((1+‖x-y‖)^α*(1+‖y‖)^α)*(‖x-y‖^(-α)*R y) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg
          (Real.rpow_nonneg (norm_nonneg _) _) (hR y))
      _ = _ := by ring
  have hy : (1+‖y‖)^α*R y ≤ C*angularPolyTail m y :=
    weighted_density_decay d m (le_add_of_nonneg_right (norm_nonneg y)) hαd (hR y) (hdec y)
  have hyC : (1+‖y‖)^α*R y ≤ C := hy.trans
    (mul_le_of_le_one_right hC (Real.rpow_le_one_of_one_le_of_nonpos
      (le_add_of_nonneg_right (norm_nonneg y)) (neg_nonpos.mpr (Nat.cast_nonneg m))))
  have hRn : 0 ≤ ‖x-y‖^(-α) := Real.rpow_nonneg (norm_nonneg _) _
  have hyn : 0 ≤ (1+‖y‖)^α*R y := mul_nonneg (Real.rpow_nonneg (by positivity) _) (hR y)
  have h2 : 0 ≤ (2:ℝ)^α := Real.rpow_nonneg (by norm_num) _
  by_cases hz : ‖x-y‖ < 1
  · simp only [angularUnitRiesz, Set.indicator_of_mem
      (show x-y ∈ Metric.ball (0 : Rd d) 1 by
        simpa only [Metric.mem_ball, dist_zero_right] using hz)]
    have hnear : (1+‖x-y‖)^α ≤ (2:ℝ)^α :=
      Real.rpow_le_rpow (by positivity) (by linarith) hα
    have hh := hcore.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hnear hRn) hyC hyn (mul_nonneg h2 hRn))
    nlinarith [mul_nonneg (mul_nonneg h2 hC)
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤1+‖y‖) (-(m:ℝ)))]
  · simp only [angularUnitRiesz, Set.indicator_of_notMem
      (show x-y ∉ Metric.ball (0 : Rd d) 1 by
        simpa only [Metric.mem_ball, dist_zero_right] using hz), zero_add]
    have hh := hcore.trans (mul_le_mul
      (weighted_riesz_outside_one hα (le_of_not_gt hz)) hy hyn h2)
    simpa only [mul_assoc] using hh

private theorem angularRieszConvolution_integrable_bound
    (d m : ℕ) (hd : 1 ≤ d) (hm : d < m)
    (α : ℝ) (hα : 0 ≤ α) (hαd : α < (d:ℝ))
    (R : Rd d → ℝ) (hRm : Measurable R) (hR : ∀ y, 0 ≤ R y)
    (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ y, R y ≤ C*(1+‖y‖)^(-((d+m:ℕ):ℝ))) (x : Rd d) :
    Integrable (fun y => ‖x-y‖^(-α)*R y) volume ∧
    (∫ y, ‖x-y‖^(-α)*R y) ≤ ((2:ℝ)^α*C)*
      ((∫ z in Metric.ball (0:Rd d) 1, ‖z‖^(-α))+
        ∫ z : Rd d, angularPolyTail m z)*(1+‖x‖)^(-α) := by
  let W : ℝ := (1+‖x‖)^α
  let H : Rd d → ℝ := fun y => ((2:ℝ)^α*C)*
    (angularUnitRiesz α (x-y)+angularPolyTail m y)
  have hWp : 0 < W := Real.rpow_pos_of_pos (by positivity) _
  have hball : IntegrableOn (fun z : Rd d => ‖z‖^(-α)) (Metric.ball 0 1) volume :=
    integrableOn_ball_of_norm_le_rpow
      (by simpa only [Rd, finrank_euclideanSpace_fin] using hd)
      (by simpa only [Rd, finrank_euclideanSpace_fin] using hαd) (C := 1)
      (Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), one_mul]))
      (measurable_norm.pow_const (-α)).aestronglyMeasurable
  have hshift : Integrable (fun y => angularUnitRiesz α (x-y)) volume :=
    (hball.integrable_indicator Metric.isOpen_ball.measurableSet).comp_sub_left x
  have hq : Integrable (angularPolyTail m : Rd d → ℝ) volume :=
    integrable_one_add_norm (by
      simpa only [Rd, finrank_euclideanSpace_fin] using
        (show (d:ℝ) < (m:ℝ) by exact_mod_cast hm))
  have hH : Integrable H volume := (hshift.add hq).const_mul _
  have hp (y : Rd d) : W*(‖x-y‖^(-α)*R y) ≤ H y :=
    weighted_riesz_single_majorant d m α hα hαd.le R hR C hC hdec x y
  have hF : Integrable (fun y => W*(‖x-y‖^(-α)*R y)) volume := hH.mono'
    (measurable_const.mul
      (((measurable_const.sub measurable_id).norm.pow_const (-α)).mul hRm)).aestronglyMeasurable
    (Eventually.of_forall (fun y => by
      simpa only [Real.norm_of_nonneg (mul_nonneg hWp.le
        (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hR y)))] using hp y))
  refine ⟨(integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hWp.ne') _).mp hF, ?_⟩
  have hb := integral_mono_ae hF hH (Eventually.of_forall hp)
  change (∫ y, W*(‖x-y‖^(-α)*R y)) ≤
    ∫ y, ((2:ℝ)^α*C)*(angularUnitRiesz α (x-y)+angularPolyTail m y) at hb
  rw [integral_const_mul, integral_const_mul, integral_add hshift hq,
    integral_sub_left_eq_self (angularUnitRiesz α : Rd d → ℝ) volume x] at hb
  simp only [angularUnitRiesz, integral_indicator Metric.isOpen_ball.measurableSet] at hb
  have hdiv : (∫ y, ‖x-y‖^(-α)*R y) ≤ ((2:ℝ)^α*C)*
      ((∫ z in Metric.ball (0:Rd d) 1, ‖z‖^(-α))+
        ∫ z : Rd d, angularPolyTail m z) / W :=
    (le_div_iff₀ hWp).2 (by simpa only [mul_comm] using hb)
  simpa only [W, div_eq_mul_inv, ← Real.rpow_neg
    (by positivity : (0:ℝ) ≤ 1+‖x‖)] using hdiv

private theorem angularRiesz_inv_smul
    (d : ℕ) {L α : ℝ} (hL : 0 < L) (z : Rd d) :
    ‖L⁻¹ • z‖^(-α) = L^α*‖z‖^(-α) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL),
    Real.mul_rpow (inv_pos.mpr hL).le (norm_nonneg z),
    Real.inv_rpow hL.le, Real.rpow_neg hL.le, inv_inv]

private theorem angularRiesz_weight_cancel
    {L r α : ℝ} (hL : 0 < L) (hr : 0 < r) (hα : 0 ≤ α) :
    L^α*(1+L*r)^(-α) ≤ r^(-α) := by
  have hh : (1+L*r)^(-α) ≤ (L*r)^(-α) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hL hr)
      (le_add_of_nonneg_left zero_le_one) (neg_nonpos.mpr hα)
  calc
    _ ≤ L^α*(L*r)^(-α) := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hL.le _)
    _ = _ := by
      rw [Real.mul_rpow hL.le hr.le, ← mul_assoc, ← Real.rpow_add hL,
        add_neg_cancel, Real.rpow_zero, one_mul]

private theorem angularRieszConvolution_scale
    (d : ℕ) (R : Rd d → ℝ) (α L : ℝ) (hL : 0 < L) (k : Rd d)
    (hint : Integrable (fun z => ‖L • k-z‖^(-α)*R z) volume) :
    Integrable (fun t => ‖k-t‖^(-α)*(L^d*R (L • t))) volume ∧
      (∫ t, ‖k-t‖^(-α)*(L^d*R (L • t))) =
        L^α*∫ z, ‖L • k-z‖^(-α)*R z := by
  let f : Rd d → ℝ := fun z => ‖L • k-z‖^(-α)*R z
  have hp (t : Rd d) : ‖k-t‖^(-α)*(L^d*R (L • t)) = (L^d*L^α)*f (L • t) := by
    have hv : L⁻¹ • (L • k-L • t) = k-t := by
      rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hL.ne', one_smul, one_smul]
    have hh : ‖k-t‖^(-α) = L^α*‖L • k-L • t‖^(-α) :=
      (congrArg (fun z : Rd d => ‖z‖^(-α)) hv).symm.trans (angularRiesz_inv_smul d hL _)
    rw [hh]
    simp only [f, mul_assoc, mul_left_comm]
  refine ⟨((hint.comp_smul hL.ne').const_mul (L^d*L^α)).congr
    (Eventually.of_forall (fun t => (hp t).symm)), ?_⟩
  rw [integral_congr_ae (Eventually.of_forall hp), integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume f L (hR := hL.le)]
  simp only [Rd, finrank_euclideanSpace_fin, smul_eq_mul, f]
  field_simp [pow_ne_zero d hL.ne']

private theorem dilated_poly_tail_le (d m : ℕ) {L r : ℝ} (hL : 1 ≤ L) (hr : 1 ≤ r) :
    L^d*(1+L*r)^(-((d+m:ℕ):ℝ)) ≤ (1+r)^(-(m:ℝ)) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hb : 0 < 1+L*r := by positivity
  have hpow : (L/(1+L*r))^d ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (div_nonneg hL0.le hb.le)
      ((div_le_one₀ hb).2 (by nlinarith [mul_le_mul_of_nonneg_left hr hL0.le])) d
  have hweight : (1+L*r)^(-(m:ℝ)) ≤ (1+r)^(-(m:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (add_le_add le_rfl (by nlinarith [mul_le_mul_of_nonneg_right hL hr0.le]))
      (neg_nonpos.mpr (Nat.cast_nonneg m))
  have hid : L^d*(1+L*r)^(-((d+m:ℕ):ℝ)) =
      (L/(1+L*r))^d*(1+L*r)^(-(m:ℝ)) := by
    rw [Nat.cast_add, neg_add, Real.rpow_add hb, Real.rpow_neg hb.le,
      Real.rpow_natCast, div_pow, div_eq_mul_inv]
    exact (mul_assoc _ _ _).symm
  exact hid.trans_le ((mul_le_mul hpow hweight (Real.rpow_nonneg hb.le _)
    zero_le_one).trans_eq (one_mul _))

private theorem half_radius_tail_le (m : ℕ) {r t : ℝ} (hr : 0 ≤ r) (ht : r/2 ≤ t) :
    (1+t)^(-(m:ℝ)) ≤ (2:ℝ)^m*(1+r)^(-(m:ℝ)) := by
  calc
    _ ≤ ((1+r)/2)^(-(m:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith)
        (neg_nonpos.mpr (Nat.cast_nonneg m))
    _ = _ := by
      simp only [Real.div_rpow (by positivity : (0:ℝ)≤1+r) zero_le_two,
        Real.rpow_neg zero_le_two, Real.rpow_natCast, div_inv_eq_mul, mul_comm]

private theorem angularDilatedDensity_tail
    (d m : ℕ) (R : Rd d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ z, R z ≤ C*(1+‖z‖)^(-((d+m:ℕ):ℝ)))
    {L : ℝ} (hL : 1 ≤ L) {z : Rd d} (hz : 1 ≤ ‖z‖) :
    angularDilatedDensity d R L z ≤ C*angularPolyTail m z := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  calc
    _ ≤ L^d*(C*(1+‖L • z‖)^(-((d+m:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_left (hdec _) (pow_nonneg hL0.le d)
    _ = C*(L^d*(1+L*‖z‖)^(-((d+m:ℕ):ℝ))) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hL0, mul_left_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (dilated_poly_tail_le d m hL hz) hC

private theorem angularDilatedDensity_integral
    (d : ℕ) (R : Rd d → ℝ) (L : ℝ) (hL : 0 < L) :
    (∫ z, angularDilatedDensity d R L z) = ∫ z, R z := by
  change (∫ z, L^d*R (L • z)) = ∫ z, R z
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume R L (hR := hL.le)]
  simp only [Rd, finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero d hL.ne'), one_mul]

private theorem angularConvolution_far_pointwise
    (d m : ℕ) (K R : Rd d → ℝ) (hK : ∀ y, 0 ≤ K y) (hR : ∀ y, 0 ≤ R y)
    (C b : ℝ) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hdec : ∀ z, R z ≤ C*(1+‖z‖)^(-((d+m:ℕ):ℝ)))
    (hKtail : ∀ z, 1 ≤ ‖z‖ → K z ≤ b*angularPolyTail m z)
    (L : ℝ) (hL : 1 ≤ L) (k : Rd d) (hk : 2 < ‖k‖) (y : Rd d) :
    K y*angularDilatedDensity d R L (k-y) ≤
      ((2:ℝ)^m*angularPolyTail m k)*(C*K y+b*angularDilatedDensity d R L (k-y)) := by
  have hD : 0 ≤ angularDilatedDensity d R L (k-y) :=
    mul_nonneg (pow_nonneg (zero_lt_one.trans_le hL).le d) (hR _)
  have hweight : 0 ≤ (2:ℝ)^m*angularPolyTail m k :=
    mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (by positivity) _)
  by_cases hy : ‖y‖ ≤ ‖k‖/2
  · have hhalf : ‖k‖/2 ≤ ‖k-y‖ := by
      linarith [show ‖k‖ ≤ ‖k-y‖+‖y‖ from
        (by simpa only [sub_add_cancel] using norm_add_le (k-y) y)]
    have hDb : angularDilatedDensity d R L (k-y) ≤ C*((2:ℝ)^m*angularPolyTail m k) :=
      (angularDilatedDensity_tail d m R C hC hdec hL (by linarith)).trans
        (mul_le_mul_of_nonneg_left (half_radius_tail_le m (norm_nonneg k) hhalf) hC)
    nlinarith [mul_le_mul_of_nonneg_left hDb (hK y),
      mul_nonneg hweight (mul_nonneg hb hD)]
  · have hhalf : ‖k‖/2 ≤ ‖y‖ := (lt_of_not_ge hy).le
    have hKb : K y ≤ b*((2:ℝ)^m*angularPolyTail m k) :=
      (hKtail y (by linarith)).trans
        (mul_le_mul_of_nonneg_left (half_radius_tail_le m (norm_nonneg k) hhalf) hb)
    nlinarith [mul_le_mul_of_nonneg_right hKb hD,
      mul_nonneg hweight (mul_nonneg hC (hK y))]

private theorem angularConvolution_far_bound
    (d m : ℕ) (K R : Rd d → ℝ)
    (hKint : Integrable K volume) (hRint : Integrable R volume)
    (hK : ∀ y, 0 ≤ K y) (hR : ∀ y, 0 ≤ R y)
    (C b : ℝ) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hdec : ∀ z, R z ≤ C*(1+‖z‖)^(-((d+m:ℕ):ℝ)))
    (hKtail : ∀ z, 1 ≤ ‖z‖ → K z ≤ b*angularPolyTail m z)
    (L : ℝ) (hL : 1 ≤ L) (k : Rd d) (hk : 2 < ‖k‖) :
    (∫ y, K y*angularDilatedDensity d R L (k-y)) ≤
      ((2:ℝ)^m*(C*(∫ y, K y)+b*(∫ y, R y)))*angularPolyTail m k := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hDshift : Integrable (fun y => angularDilatedDensity d R L (k-y)) volume :=
    ((hRint.comp_smul hL0.ne').const_mul (L^d)).comp_sub_left k
  have hH : Integrable (fun y => ((2:ℝ)^m*angularPolyTail m k)*
      (C*K y+b*angularDilatedDensity d R L (k-y))) volume :=
    ((hKint.const_mul C).add (hDshift.const_mul b)).const_mul _
  have hbnd := integral_mono_of_nonneg
    (Eventually.of_forall (fun y => mul_nonneg (hK y)
      (mul_nonneg (pow_nonneg hL0.le d) (hR _)))) hH
    (Eventually.of_forall (angularConvolution_far_pointwise d m K R hK hR C b hC hb
      hdec hKtail L hL k hk))
  rw [integral_const_mul, integral_add (hKint.const_mul C) (hDshift.const_mul b),
    integral_const_mul, integral_const_mul,
    integral_sub_left_eq_self (angularDilatedDensity d R L) volume k,
    angularDilatedDensity_integral d R L hL0] at hbnd
  simpa only [angularDilatedDensity, mul_assoc, mul_comm, mul_left_comm] using hbnd

private def angularRieszBoundConstant (d m : ℕ) (α C : ℝ) : ℝ :=
  ((2:ℝ)^α*C)*((∫ z in Metric.ball (0:Rd d) 1, ‖z‖^(-α))+
    ∫ z : Rd d, angularPolyTail m z)

private theorem angularConvolution_near_bound
    (d m : ℕ) (hd : 1 ≤ d) (hm : d < m)
    (α : ℝ) (hα : 0 ≤ α) (hαd : α < (d:ℝ))
    (K R : Rd d → ℝ) (hRm : Measurable R)
    (hK : ∀ y, 0 ≤ K y) (hR : ∀ y, 0 ≤ R y)
    (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ z, R z ≤ C*(1+‖z‖)^(-((d+m:ℕ):ℝ)))
    (b c : ℝ) (hb : 0 ≤ b) (hc : 0 < c)
    (hupper : ∀ z, K z ≤ b*‖z‖^(-α))
    (hlower : ∀ z, 0 < ‖z‖ → ‖z‖ ≤ 2 → c*‖z‖^(-α) ≤ K z)
    (L : ℝ) (hL : 1 ≤ L) (k : Rd d) (hk : k ≠ 0) (hkNear : ‖k‖ ≤ 2) :
    (∫ y, K y*angularDilatedDensity d R L (k-y)) ≤
      (b*angularRieszBoundConstant d m α C/c)*K k := by
  let CR : ℝ := angularRieszBoundConstant d m α C
  have hCR : 0 ≤ CR :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hC)
      (add_nonneg (integral_nonneg (fun z => Real.rpow_nonneg (norm_nonneg z) _))
        (integral_nonneg (fun z => Real.rpow_nonneg (by positivity) _)))
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  obtain ⟨hRbase, hRbound⟩ := angularRieszConvolution_integrable_bound
    d m hd hm α hα hαd R hRm hR C hC hdec (L • k)
  change (∫ z, ‖L • k-z‖^(-α)*R z) ≤ CR*(1+‖L • k‖)^(-α) at hRbound
  obtain ⟨hRscaled, hscale⟩ := angularRieszConvolution_scale d R α L hL0 k hRbase
  have hnonnegD (t : Rd d) : 0 ≤ angularDilatedDensity d R L t :=
    mul_nonneg (pow_nonneg hL0.le d) (hR _)
  have hcompare : (∫ t, K (k-t)*angularDilatedDensity d R L t) ≤
      b*(∫ t, ‖k-t‖^(-α)*angularDilatedDensity d R L t) := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg
      (Eventually.of_forall (fun t => mul_nonneg (hK (k-t)) (hnonnegD t)))
      (hRscaled.const_mul b) (Eventually.of_forall (fun t => by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (hupper (k-t)) (hnonnegD t)))
  have hnormalized : (∫ t, ‖k-t‖^(-α)*angularDilatedDensity d R L t) ≤ CR*‖k‖^(-α) := by
    calc
      _ = L^α*∫ z, ‖L • k-z‖^(-α)*R z := hscale
      _ ≤ L^α*(CR*(1+‖L • k‖)^(-α)) :=
        mul_le_mul_of_nonneg_left hRbound (Real.rpow_nonneg hL0.le _)
      _ = CR*(L^α*(1+L*‖k‖)^(-α)) := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hL0, mul_left_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (angularRiesz_weight_cancel hL0 (norm_pos_iff.mpr hk) hα) hCR
  have hRlower : ‖k‖^(-α) ≤ K k/c :=
    (le_div_iff₀ hc).2 (by
      simpa only [mul_comm] using hlower k (norm_pos_iff.mpr hk) hkNear)
  have hnear : (∫ t, K (k-t)*angularDilatedDensity d R L t) ≤ (b*CR/c)*K k :=
    hcompare.trans ((mul_le_mul_of_nonneg_left hnormalized hb).trans (by
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left hRlower (mul_nonneg hb hCR)))
  have horient : (∫ y, K y*angularDilatedDensity d R L (k-y)) =
      ∫ t, K (k-t)*angularDilatedDensity d R L t := by
    simpa only [sub_sub_cancel] using (integral_sub_left_eq_self
      (fun y => K y*angularDilatedDensity d R L (k-y)) volume k).symm
  exact horient.trans_le hnear

private theorem angularConvolution_uniform_bound
    (d m : ℕ) (hd : 1 ≤ d) (hm : d < m)
    (α : ℝ) (hα : 0 ≤ α) (hαd : α < (d:ℝ))
    (K R : Rd d → ℝ) (hRm : Measurable R)
    (hKint : Integrable K volume) (hRint : Integrable R volume)
    (hK : ∀ y, 0 ≤ K y) (hR : ∀ y, 0 ≤ R y)
    (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ z, R z ≤ C*(1+‖z‖)^(-((d+m:ℕ):ℝ)))
    (b c bt : ℝ) (hb : 0 ≤ b) (hc : 0 < c) (hbt : 0 ≤ bt)
    (hupper : ∀ z, K z ≤ b*‖z‖^(-α))
    (hlower : ∀ z, 0 < ‖z‖ → ‖z‖ ≤ 2 → c*‖z‖^(-α) ≤ K z)
    (htail : ∀ z, 1 ≤ ‖z‖ → K z ≤ bt*angularPolyTail m z) :
    ∃ Cstar : ℝ, 0 ≤ Cstar ∧ ∀ L : ℝ, 1 ≤ L → ∀ k : Rd d, k ≠ 0 →
      0 ≤ (∫ y, K y*angularDilatedDensity d R L (k-y)) ∧
      (∫ y, K y*angularDilatedDensity d R L (k-y)) ≤
        Cstar*(K k+angularPolyTail m k) := by
  let Cnear : ℝ := b*angularRieszBoundConstant d m α C/c
  let Cfar : ℝ := (2:ℝ)^m*(C*(∫ y, K y)+bt*(∫ y, R y))
  refine ⟨max 0 (max Cnear Cfar), le_max_left _ _, fun L hL k hk => ?_⟩
  refine ⟨integral_nonneg (fun y => mul_nonneg (hK y)
    (mul_nonneg (pow_nonneg (zero_lt_one.trans_le hL).le d) (hR _))), ?_⟩
  by_cases hn : ‖k‖ ≤ 2
  · exact (angularConvolution_near_bound d m hd hm α hα hαd K R hRm hK hR C hC
      hdec b c hb hc hupper hlower L hL k hk hn).trans
        ((mul_le_mul_of_nonneg_right
          ((le_max_left Cnear Cfar).trans (le_max_right 0 _)) (hK k)).trans
            (mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)) (le_max_left 0 _)))
  · exact (angularConvolution_far_bound d m K R hKint hRint hK hR C bt hC hbt
      hdec htail L hL k (lt_of_not_ge hn)).trans
        ((mul_le_mul_of_nonneg_right
          ((le_max_right Cnear Cfar).trans (le_max_right 0 _))
          (Real.rpow_nonneg (by positivity) _)).trans
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hK k)) (le_max_left 0 _)))

private theorem angularDensity_peak_decay
    (d m : ℕ) (hm : 0 < m) (R : Rd d → ℝ) (hR : ∀ y, 0 ≤ R y)
    (C : ℝ) (hdec : ∀ z, R z ≤ C*(1+‖z‖)^(-((d+m:ℕ):ℝ))) :
    Tendsto (fun x => ‖x‖^d*R x) (Bornology.cobounded (Rd d)) (𝓝 0) := by
  have hbound (x : Rd d) : ‖x‖^d*R x ≤ C*angularPolyTail m x := by
    calc
      _ ≤ (1+‖x‖)^d*R x := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg x) (by linarith) d) (hR x)
      _ ≤ _ := by
        simpa only [angularPolyTail, Real.rpow_natCast] using weighted_density_decay d m
          (le_add_of_nonneg_right (norm_nonneg x)) le_rfl (hR x) (hdec x)
  have hnorm : Tendsto (fun x : Rd d => 1+‖x‖) (Bornology.cobounded (Rd d)) atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_norm_cobounded_atTop
  exact squeeze_zero
    (fun x => mul_nonneg (pow_nonneg (norm_nonneg x) d) (hR x)) hbound
    (by simpa only [angularPolyTail, Function.comp_def, mul_zero] using
      (((tendsto_rpow_neg_atTop (show (0:ℝ) < (m:ℝ) by exact_mod_cast hm)).comp hnorm).const_mul C))

private theorem angularConvolution_pointwise_tendsto
    (d m : ℕ) (hm : 0 < m) (K R : Rd d → ℝ)
    (hKint : Integrable K volume) (hR : ∀ y, 0 ≤ R y)
    (C : ℝ) (hdec : ∀ z, R z ≤ C*(1+‖z‖)^(-((d+m:ℕ):ℝ)))
    (hA : 0 < ∫ y, R y) (k : Rd d) (hKk : ContinuousAt K k) :
    Tendsto (fun n : ℕ => ∫ y, K y*angularDilatedDensity d R ((n:ℝ)+1) (k-y)) atTop
      (𝓝 ((∫ y, R y)*K k)) := by
  let A : ℝ := ∫ y, R y
  let φ : Rd d → ℝ := fun x => A⁻¹*R x
  have hφ : ∀ x, 0 ≤ φ x := fun x => mul_nonneg (inv_nonneg.mpr hA.le) (hR x)
  have hmass : (∫ x, φ x) = 1 := by
    simpa only [φ, integral_const_mul, A] using inv_mul_cancel₀ hA.ne'
  have hpeak : Tendsto (fun x : Rd d => ‖x‖^Module.finrank ℝ (Rd d)*φ x)
      (Bornology.cobounded (Rd d)) (𝓝 0) := by
    simpa only [Rd, finrank_euclideanSpace_fin, φ, mul_zero, mul_left_comm] using
      (angularDensity_peak_decay d m hm R hR C hdec).const_mul A⁻¹
  have ht := tendsto_integral_comp_smul_smul_of_integrable'
    (μ := (volume : Measure (Rd d))) hφ hmass hpeak hKint hKk
  have hseq : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq (L : ℝ) : (∫ y, K y*angularDilatedDensity d R L (k-y)) =
      A*(∫ y, (L^Module.finrank ℝ (Rd d)*φ (L • (k-y))) • K y) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine Eventually.of_forall (fun y => ?_)
    simp [angularDilatedDensity, Rd, φ, smul_eq_mul, mul_left_comm, mul_comm, A, hA.ne']
  simpa only [A] using ((ht.const_mul A).comp hseq).congr (fun n => (heq _).symm)

section SmoothConvolution

open scoped ContDiff

theorem compactSmoothWindow_mellinConvolution_integral_tendsto
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hsm : ContDiff ℝ ∞ χ)
    (ha : 0 < compactAnchorSquareMass d χ) :
    Tendsto (fun n : ℕ => ∫ k,
      (∫ y : Rd d, angularMellinReal d s y *
        angularDilatedDensity d (compactAngularDensity d χ) ((n : ℝ)+1) (k-y))
      ∂originalAngularSpectrum d s hs P hP hW) atTop
      (𝓝 (((2 * Real.pi)^d * compactAnchorSquareMass d χ) *
        ∫ k, angularMellinReal d s k ∂originalAngularSpectrum d s hs P hP hW)) := by
  let ρ := originalAngularSpectrum d s hs P hP hW
  let K : Rd d → ℝ := angularMellinReal d s
  let R : Rd d → ℝ := compactAngularDensity d χ
  let p : ℝ := angularMellinOrder d s
  let b : ℝ := angularMellinPrefactor d * (4 : ℝ)^p * Real.Gamma p
  let c : ℝ := angularMellinPrefactor d * (4 : ℝ)^(p+1) / 8 * Real.exp (-2)
  let bt : ℝ := (angularMellinPrefactor d * (8 : ℝ)^p * Real.Gamma p) *
    ((2 : ℝ)^(d+2) * (((d+2).factorial : ℝ) / (1/8 : ℝ)^(d+2)))
  have hd0 : 0 < d := by exact_mod_cast (hs.trans hsd)
  have hd : 1 ≤ d := by omega
  have hp : 0 < p := by
    dsimp only [p, angularMellinOrder]
    linarith
  have hAp := angularMellinPrefactor_pos d
  have hGp := Real.Gamma_pos_of_pos hp
  have hb : 0 ≤ b := by
    dsimp only [b]
    positivity
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hbt : 0 ≤ bt := by
    dsimp only [bt]
    positivity
  have hKvol : Integrable K volume := integrable_angularMellinReal d hs
  have hKrho : Integrable K ρ :=
    integrable_angularMellinReal_originalAngularSpectrum d s hs P hP hW
  have hKm : Measurable K := (measurable_angularMellinKernel d s).ennreal_toReal
  have hK : ∀ k, 0 ≤ K k := fun _ => ENNReal.toReal_nonneg
  have hRm : Measurable R := measurable_compactAngularDensity d χ
  have hR : ∀ k, 0 ≤ R k := compactAngularDensity_nonneg d χ
  have hkAE : ∀ᵐ k ∂ρ, k ≠ 0 :=
    ae_ne_zero_originalAngularSpectrum_of_finite_W d s hs hsd P hP hW
  have hqrho : Integrable (angularPolyTail (d+2) : Rd d → ℝ) ρ := by
    exact integrable_originalAngularSpectrum_polynomialTail d s hs P hP hW
  have hmass : (∫ k, R k) = (2 * Real.pi)^d * compactAnchorSquareMass d χ := by
    simpa only [R, compactAngularDensity, compactAnchorSquareMass] using
      compactSmoothWindow_angular_plancherel d χ hsm
  have hRmass : 0 < ∫ k, R k := by
    rw [hmass]
    positivity
  have hRint : Integrable R volume := Integrable.of_integral_ne_zero hRmass.ne'
  obtain ⟨C, hCpos, hCraw⟩ := compactSmoothWindow_angular_density_decay d χ hsm
  have hdec (k) : R k ≤ C*(1+‖k‖)^(-((d+(d+2):ℕ):ℝ)) := by
    simpa only [R, compactAngularDensity, show d+(d+2) = 2*d+2 by omega] using hCraw k
  have hupper (k) : K k ≤ b*‖k‖^(-((d:ℝ)-s)) := by
    simpa only [K, b, p] using angularMellinReal_le_riesz d hsd k
  have hlower (k) (hk : 0 < ‖k‖) (hk2 : ‖k‖ ≤ 2) : c*‖k‖^(-((d:ℝ)-s)) ≤ K k := by
    simpa only [K, c, p] using angularMellinReal_ge_riesz_near d hsd (norm_pos_iff.mp hk) hk2
  have htail (k) (hk : 1 ≤ ‖k‖) : K k ≤ bt*angularPolyTail (d+2) k := by
    simpa only [K, bt, p, angularPolyTail] using
      angularMellinReal_le_polynomial_tail d (d+2) hsd hk
  obtain ⟨Cstar, _hCstar, huniform⟩ := angularConvolution_uniform_bound
    d (d+2) hd (by omega) ((d:ℝ)-s) (sub_nonneg.mpr hsd.le) (by linarith)
    K R hRm hKvol hRint hK hR C hCpos.le hdec b c bt hb hc hbt hupper hlower htail
  let F : ℕ → Rd d → ℝ := fun n k => ∫ y, K y *
    angularDilatedDensity d R ((n:ℝ)+1) (k-y)
  have hFm (n) : AEStronglyMeasurable (F n) ρ := by
    have hGm : StronglyMeasurable (fun q : Rd d × Rd d =>
        K q.2 * angularDilatedDensity d R ((n:ℝ)+1) (q.1-q.2)) := by
      dsimp only [angularDilatedDensity]
      have hsub : Measurable (fun q : Rd d × Rd d => ((n:ℝ)+1) • (q.1-q.2)) :=
        (measurable_fst.sub measurable_snd).const_smul ((n:ℝ)+1)
      exact ((hKm.comp measurable_snd).mul ((hRm.comp hsub).const_mul (((n:ℝ)+1)^d))).stronglyMeasurable
    exact hGm.integral_prod_right'.aestronglyMeasurable
  have hboundInt : Integrable (fun k => Cstar*(K k + angularPolyTail (d+2) k)) ρ :=
    (hKrho.add hqrho).const_mul Cstar
  have hnorm (n) : ∀ᵐ k ∂ρ, ‖F n k‖ ≤ Cstar*(K k + angularPolyTail (d+2) k) := by
    filter_upwards [hkAE] with k hk
    have hL : (1:ℝ) ≤ (n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    change ‖∫ y, K y * angularDilatedDensity d R ((n:ℝ)+1) (k-y)‖ ≤ _
    rw [Real.norm_of_nonneg (huniform _ hL k hk).1]
    exact (huniform _ hL k hk).2
  have hlim : ∀ᵐ k ∂ρ, Tendsto (fun n => F n k) atTop (𝓝 ((∫ y, R y)*K k)) := by
    filter_upwards [hkAE] with k hk
    exact angularConvolution_pointwise_tendsto d (d+2) (by omega) K R hKvol hR C hdec
      hRmass k (continuousAt_angularMellinReal d hsd hk)
  have ht := tendsto_integral_of_dominated_convergence
    (fun k => Cstar*(K k + angularPolyTail (d+2) k)) hFm hboundInt hnorm hlim
  rw [integral_const_mul] at ht
  rw [hmass] at ht
  simpa only [F, K, R, ρ] using ht

end SmoothConvolution

theorem angularMellinReal_originalAngularSpectrum_head_integral
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    IntegrableOn (fun u : ℝ => u^(s/2-1) *
      ((Q d P u).toReal + 1 - B d u)) (Set.Ioc 0 1) ∧
    (2 * Real.pi)^d * (∫ k, (angularMellinKernel d s k).toReal
      ∂originalAngularSpectrum d s hs P hP hW) =
        ∫ u : ℝ in Set.Ioc 0 1, u^(s/2-1) *
          ((Q d P u).toReal + 1 - B d u) := by
  let ρ := originalAngularSpectrum d s hs P hP hW
  let τ : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)
  let A : ℝ := (2 * Real.pi)^d
  let w : ℝ → ℝ := fun u => u^(s/2-1)
  let H : ℝ → ℝ := fun u => (Q d P u).toReal + 1 - B d u
  let S : ℝ → ℝ≥0∞ := fun u => ∫⁻ k, angularHeadBaseNN d s (u,k) ∂ρ
  have hA : 0 < A := pow_pos (by positivity) d
  have hMm := measurable_angularMellinKernel d s
  have hMfin : (∫⁻ k, angularMellinKernel d s k ∂ρ) ≠ ∞ :=
    lintegral_angularMellinKernel_originalAngularSpectrum_ne_top d s hs P hP hW
  have hSm : Measurable S := (measurable_angularHeadBaseNN d s).lintegral_prod_right'
  have hswap : (∫⁻ u, S u ∂τ) = ∫⁻ k, angularMellinKernel d s k ∂ρ := by
    simpa only [S, angularMellinKernel, angularHeadBaseNN] using
      (lintegral_lintegral_swap (μ := τ) (ν := ρ)
        (f := fun u k => angularHeadBaseNN d s (u,k))
        (measurable_angularHeadBaseNN d s).aemeasurable)
  have hSfin : (∫⁻ u, S u ∂τ) ≠ ∞ := hswap.trans_ne hMfin
  have hSint : Integrable (fun u => (S u).toReal) τ :=
    integrable_toReal_of_lintegral_ne_top hSm.aemeasurable hSfin
  have hKvalue : (∫ k, (angularMellinKernel d s k).toReal ∂ρ) =
      (∫⁻ k, angularMellinKernel d s k ∂ρ).toReal :=
    integral_toReal hMm.aemeasurable (ae_lt_top hMm hMfin)
  have hSvalue : (∫ u, (S u).toReal ∂τ) = (∫⁻ u, S u ∂τ).toReal :=
    integral_toReal hSm.aemeasurable (ae_lt_top hSm hSfin)
  have hHnonneg (u : ℝ) (hu : 0 < u) : 0 ≤ H u := by
    have hQ := Q_ne_top_of_W_ne_top_pos d s hs P hW u hu
    have hlow : max (B d u - 1) 0 ≤ (Q d P u).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hQ).mp
        (gaussian_covariance_lower_bound_of_admissible d P hP u hu)
    have hb : B d u - 1 ≤ (Q d P u).toReal := (le_max_left (B d u - 1) 0).trans hlow
    dsimp only [H]
    linarith
  have hSNN (u : ℝ) (hu : 0 < u) :
      S u = ENNReal.ofReal A⁻¹ * ENNReal.ofReal (w u * H u) := by
    change (∫⁻ k, ENNReal.ofReal (w u) *
      ENNReal.ofReal (originalHeatGaussian d u k) ∂ρ) = _
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_originalAngularSpectrum_originalHeatGaussian d s hs P hP hW hu,
      ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _)]
    rw [ENNReal.ofReal_inv_of_pos hA]
    simp only [w, H, mul_left_comm]
  have hSreal (u : ℝ) (hu : 0 < u) : (S u).toReal = A⁻¹ * (w u * H u) := by
    rw [hSNN u hu, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hA.le),
      ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hu.le _) (hHnonneg u hu))]
  have hscale : (fun u => A * (S u).toReal) =ᵐ[τ] (fun u => w u * H u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [hSreal u hu.1, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]
  have hHint : Integrable (fun u => w u * H u) τ := (hSint.const_mul A).congr hscale
  have hreal : (∫ k, (angularMellinKernel d s k).toReal ∂ρ) = ∫ u, (S u).toReal ∂τ :=
    hKvalue.trans ((congrArg ENNReal.toReal hswap).symm.trans hSvalue.symm)
  exact ⟨hHint, (congrArg (fun t : ℝ => A*t) hreal).trans
    ((integral_const_mul A _).symm.trans (integral_congr_ae hscale))⟩

theorem positiveHead_centered_profile_integrable_and_integral
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    IntegrableOn (fun u : ℝ => u^(s/2-1) *
      ((Q d P u).toReal - B d u)) (Set.Ioc 0 1) ∧
    (∫ u : ℝ in Set.Ioc 0 1, u^(s/2-1) * ((Q d P u).toReal - B d u)) =
      (2 * Real.pi)^d * (∫ k, (angularMellinKernel d s k).toReal
        ∂originalAngularSpectrum d s hs P hP hW) - 2/s := by
  obtain ⟨hH, hvalue⟩ := angularMellinReal_originalAngularSpectrum_head_integral d s hs P hP hW
  obtain ⟨hw, hwmass⟩ := positiveHeadWeight_integrable_and_integral s hs
  have heq : (fun u : ℝ => u^(s/2-1) * ((Q d P u).toReal + 1 - B d u) - u^(s/2-1)) =
      (fun u : ℝ => u^(s/2-1) * ((Q d P u).toReal - B d u)) := by
    funext u
    ring
  refine ⟨(hH.sub hw).congr (Eventually.of_forall (fun u => congrFun heq u)), ?_⟩
  rw [← heq, integral_sub hH hw, hwmass, ← hvalue]

def centeredPositiveHeadWindowCost
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d) (hP : Admissible d P)
    (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) : ℝ :=
  (L^d)⁻¹ * ((∫ q, compactPositiveHeadPairTest d s hs
      (angularScaledCompactWindow d χ L hL) q ∂originalAdmissibleFactorialMeasure d P hP) -
    ∫ q : Rd d × Rd d, compactPositiveHeadPairTest d s hs
      (angularScaledCompactWindow d χ L hL) q ∂(volume : Measure (Rd d)).prod volume)

private theorem angularScaledCompactWindow_normalized_square
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) :
    (L^d)⁻¹ * (∫ x : Rd d, (angularScaledCompactWindow d χ L hL x)^2) =
      compactAnchorSquareMass d χ := by
  have hscale : (∫ x : Rd d, (angularScaledCompactWindow d χ L hL x)^2) =
      L^d * compactAnchorSquareMass d χ := by
    simpa only [angularScaledCompactWindow_apply, compactAnchorSquareMass,
      Rd, finrank_euclideanSpace_fin, smul_eq_mul] using
      (Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Rd d))
        (fun x => (χ x)^2) (R := L) hL.le)
  rw [hscale, ← mul_assoc, inv_mul_cancel₀ (pow_pos hL d).ne', one_mul]

private theorem compactSmoothWindow_scaled_head_centered
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) (hL : 0 < L) :
    (∫⁻ k, (ENNReal.ofReal (L^d))⁻¹ *
      compactAngularHeadJ d s (angularScaledCompactWindow d χ L hL) k
      ∂originalAngularSpectrum d s hs P hP hW) ≠ ∞ ∧
    Integrable (fun k => ∫ y : Rd d, angularMellinReal d s y *
      angularDilatedDensity d (compactAngularDensity d χ) L (k-y))
      (originalAngularSpectrum d s hs P hP hW) ∧
    (∫ k, (∫ y : Rd d, angularMellinReal d s y *
      angularDilatedDensity d (compactAngularDensity d χ) L (k-y))
      ∂originalAngularSpectrum d s hs P hP hW) =
      centeredPositiveHeadWindowCost d s hs P hP χ L hL +
        (2/s) * compactAnchorSquareMass d χ := by
  let ρ := originalAngularSpectrum d s hs P hP hW
  let φ := angularScaledCompactWindow d χ L hL
  let r : ℝ≥0∞ := ENNReal.ofReal (L^d)
  let F : Rd d → ℝ := fun k => ∫ y, angularMellinReal d s y *
    angularDilatedDensity d (compactAngularDensity d χ) L (k-y)
  have hφ : ∀ x, 0 ≤ φ x := fun x => hχ (L⁻¹ • x)
  obtain ⟨hJNN, hJint, hphysical⟩ :=
    compactPositiveHeadPairTest_angularSpectrum_identity d s hs P hP hW φ hφ
  have hr0 : r ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hL d)).ne'
  have hnormalizedNN : (∫⁻ k, r⁻¹ * compactAngularHeadJ d s φ k ∂ρ) ≠ ∞ := by
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hr0)]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hr0) hJNN
  have hpoint (k : Rd d) : (L^d)⁻¹ * (compactAngularHeadJ d s φ k).toReal = F k :=
    (compactAngularHeadJ_scaled_mellin_real d s hs χ hχ L hL k).2.2
  have hFint : Integrable F ρ :=
    (hJint.const_mul ((L^d)⁻¹)).congr (Eventually.of_forall hpoint)
  have hFvalue : (∫ k, F k ∂ρ) = (L^d)⁻¹ * ∫ k, (compactAngularHeadJ d s φ k).toReal ∂ρ :=
    (integral_congr_ae (Eventually.of_forall hpoint)).symm.trans (integral_const_mul _ _)
  refine ⟨hnormalizedNN, hFint, hFvalue.trans ?_⟩
  rw [hphysical]
  rw [← angularScaledCompactWindow_normalized_square d χ L hL]
  dsimp only [centeredPositiveHeadWindowCost, φ]
  ring

section SmoothHeadLimit

open scoped ContDiff

theorem compactSmoothWindow_centered_head_tendsto
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d:ℝ))
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (hsm : ContDiff ℝ ∞ χ)
    (ha : 0 < compactAnchorSquareMass d χ) :
    IntegrableOn (fun u : ℝ => u^(s/2-1) * ((Q d P u).toReal - B d u)) (Set.Ioc 0 1) ∧
    Tendsto (fun n : ℕ => centeredPositiveHeadWindowCost d s hs P hP χ ((n:ℝ)+1)
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)) atTop
      (𝓝 (compactAnchorSquareMass d χ * ∫ u : ℝ in Set.Ioc 0 1,
        u^(s/2-1) * ((Q d P u).toReal - B d u))) := by
  obtain ⟨hcenterInt, hcenterValue⟩ :=
    positiveHead_centered_profile_integrable_and_integral d s hs P hP hW
  let a := compactAnchorSquareMass d χ
  let L : ℕ → ℝ := fun n => (n:ℝ)+1
  have hL (n : ℕ) : 0 < L n := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  let F : ℕ → Rd d → ℝ := fun n k => ∫ y : Rd d, angularMellinReal d s y *
    angularDilatedDensity d (compactAngularDensity d χ) (L n) (k-y)
  have hfixed (n : ℕ) : (∫ k, F n k ∂originalAngularSpectrum d s hs P hP hW) =
      centeredPositiveHeadWindowCost d s hs P hP χ (L n) (hL n) + (2/s)*a :=
    (compactSmoothWindow_scaled_head_centered d s hs P hP hW χ hχ (L n) (hL n)).2.2
  have hDCT : Tendsto (fun n => ∫ k, F n k ∂originalAngularSpectrum d s hs P hP hW)
      atTop (𝓝 ((2*Real.pi)^d*a *
        ∫ k, angularMellinReal d s k ∂originalAngularSpectrum d s hs P hP hW)) :=
    compactSmoothWindow_mellinConvolution_integral_tendsto d s hs hsd P hP hW χ hsm ha
  have hlim : Tendsto (fun n : ℕ => centeredPositiveHeadWindowCost d s hs P hP χ
      (L n) (hL n)) atTop (𝓝 ((2*Real.pi)^d*a *
        (∫ k, angularMellinReal d s k ∂originalAngularSpectrum d s hs P hP hW) - (2/s)*a)) := by
    refine (hDCT.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2/s)*a)
      atTop (𝓝 ((2/s)*a)))).congr (fun n => ?_)
    rw [hfixed n, add_sub_cancel_right]
  have htarget : (2*Real.pi)^d*a *
      (∫ k, angularMellinReal d s k ∂originalAngularSpectrum d s hs P hP hW) - (2/s)*a =
      a * ∫ u : ℝ in Set.Ioc 0 1, u^(s/2-1) * ((Q d P u).toReal - B d u) := by
    rw [hcenterValue]
    dsimp only [angularMellinReal]
    ring
  exact ⟨hcenterInt, htarget ▸ hlim⟩

end SmoothHeadLimit

theorem compactPositiveHeadPairTest_head_lintegral
    (d : ℕ) (s : ℝ) (hs : 0 < s) (μ : Measure (Rd d × Rd d)) [SFinite μ]
    (φ : C_c(Rd d, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
    (hψ : Integrable (compactPositiveHeadPairTest d s hs φ) μ) :
    (∫⁻ u in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (u^(s/2-1)) *
      (∫⁻ p, compactGaussianWindowKernel d φ u p ∂μ)) ≠ ∞ ∧
    (∫⁻ u in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (u^(s/2-1)) *
      (∫⁻ p, compactGaussianWindowKernel d φ u p ∂μ)).toReal =
        ∫ p, compactPositiveHeadPairTest d s hs φ p ∂μ := by
  let τ : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)
  let ψ := compactPositiveHeadPairTest d s hs φ
  have hψnn (p : Rd d × Rd d) : 0 ≤ ψ p :=
    (compactPositiveHeadPairTest_nonneg_and_bound d s hs φ hφ p).1
  have hscalar (p : Rd d × Rd d) :
      (∫⁻ u, ENNReal.ofReal (u^(s/2-1)) * compactGaussianWindowKernel d φ u p ∂τ) =
        ENNReal.ofReal (ψ p) := by
    let c : ℝ := φ p.1 * φ p.2
    let f : ℝ → ℝ := fun u => u^(s/2-1) * Real.exp (-(u * ‖p.2-p.1‖^2))
    have hc : 0 ≤ c := mul_nonneg (hφ p.1) (hφ p.2)
    have hfint : Integrable f τ := by
      refine (positiveHeadWeight_integrable_and_integral s hs).1.mono' ?_ ?_
      · exact ((measurable_id.pow_const _).mul
          ((measurable_id.mul_const _).neg.exp)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        simpa only [f, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg hu.1.le (s/2-1)), abs_of_pos (Real.exp_pos _)] using
          mul_le_of_le_one_right (Real.rpow_nonneg hu.1.le (s/2-1))
            (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hu.1.le (sq_nonneg ‖p.2-p.1‖))))
    have hcnn : ∀ᵐ u ∂τ, 0 ≤ c * f u := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact mul_nonneg hc (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.exp_pos _).le)
    have hpoint : (fun u => ENNReal.ofReal (u^(s/2-1)) * compactGaussianWindowKernel d φ u p)
        =ᵐ[τ] (fun u => ENNReal.ofReal (c*f u)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      dsimp only [compactGaussianWindowKernel, c, f]
      rw [ENNReal.ofReal_mul (mul_nonneg (hφ p.1) (hφ p.2)),
        ENNReal.ofReal_mul (hφ p.1), ENNReal.ofReal_mul (Real.rpow_nonneg hu.1.le _), neg_mul]
      ac_rfl
    rw [lintegral_congr_ae hpoint, ← ofReal_integral_eq_lintegral_ofReal (hfint.const_mul c) hcnn,
      integral_const_mul]
    rfl
  have hmeas : Measurable (fun q : ℝ × (Rd d × Rd d) =>
      ENNReal.ofReal (q.1^(s/2-1)) * compactGaussianWindowKernel d φ q.1 q.2) := by
    have h1 : Measurable (fun q : ℝ × (Rd d × Rd d) => ENNReal.ofReal (φ q.2.1)) :=
      φ.continuous.measurable.ennreal_ofReal.comp
      (measurable_fst.comp measurable_snd)
    have h2 : Measurable (fun q : ℝ × (Rd d × Rd d) => ENNReal.ofReal (φ q.2.2)) :=
      φ.continuous.measurable.ennreal_ofReal.comp (measurable_snd.comp measurable_snd)
    have he : Measurable (fun q : ℝ × (Rd d × Rd d) =>
        ENNReal.ofReal (Real.exp (-q.1 * ‖q.2.2-q.2.1‖^2))) :=
      ((measurable_fst.neg.mul (((measurable_snd.comp measurable_snd).sub
        (measurable_fst.comp measurable_snd)).norm.pow_const 2)).exp).ennreal_ofReal
    exact (measurable_fst.pow_const (s/2-1)).ennreal_ofReal.mul ((h1.mul h2).mul he)
  have hvalue : (∫⁻ u, ENNReal.ofReal (u^(s/2-1)) *
      (∫⁻ p, compactGaussianWindowKernel d φ u p ∂μ) ∂τ) = ENNReal.ofReal (∫ p, ψ p ∂μ) := by
    calc
      _ = ∫⁻ u, ∫⁻ p, ENNReal.ofReal (u^(s/2-1)) * compactGaussianWindowKernel d φ u p ∂μ ∂τ :=
        lintegral_congr (fun u => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm)
      _ = ∫⁻ p, ∫⁻ u, ENNReal.ofReal (u^(s/2-1)) * compactGaussianWindowKernel d φ u p ∂τ ∂μ :=
        lintegral_lintegral_swap (μ := τ) (ν := μ)
          (f := fun u p => ENNReal.ofReal (u^(s/2-1)) * compactGaussianWindowKernel d φ u p)
          hmeas.aemeasurable
      _ = ∫⁻ p, ENNReal.ofReal (ψ p) ∂μ := lintegral_congr hscalar
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hψ (Eventually.of_forall hψnn)).symm
  exact ⟨hvalue.trans_ne ENNReal.ofReal_ne_top,
    (congrArg ENNReal.toReal hvalue).trans (ENNReal.toReal_ofReal (integral_nonneg hψnn))⟩

theorem compactPositiveHeadPairTest_normalized_head_lintegral
    (d : ℕ) (s : ℝ) (hs : 0 < s) (μ : Measure (Rd d × Rd d)) [SFinite μ]
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) (hL : 0 < L)
    (hψ : Integrable (compactPositiveHeadPairTest d s hs
      (angularScaledCompactWindow d χ L hL)) μ) :
    (∫⁻ u in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (u^(s/2-1)) *
      ((ENNReal.ofReal (L^d))⁻¹ *
        ∫⁻ p, compactGaussianWindowKernel d (angularScaledCompactWindow d χ L hL) u p ∂μ)) ≠ ∞ ∧
    (∫⁻ u in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (u^(s/2-1)) *
      ((ENNReal.ofReal (L^d))⁻¹ *
        ∫⁻ p, compactGaussianWindowKernel d (angularScaledCompactWindow d χ L hL) u p ∂μ)).toReal =
      (L^d)⁻¹ * ∫ p, compactPositiveHeadPairTest d s hs
        (angularScaledCompactWindow d χ L hL) p ∂μ := by
  let φ := angularScaledCompactWindow d χ L hL
  have hφ : ∀ x, 0 ≤ φ x := fun x => hχ (L⁻¹ • x)
  let r : ℝ≥0∞ := ENNReal.ofReal (L^d)
  have hr0 : r ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hL d)).ne'
  obtain ⟨hfin, hreal⟩ := compactPositiveHeadPairTest_head_lintegral d s hs μ φ hφ hψ
  have hfactor : (∫⁻ u in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (u^(s/2-1)) *
      (r⁻¹ * ∫⁻ p, compactGaussianWindowKernel d φ u p ∂μ)) =
      r⁻¹ * ∫⁻ u in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (u^(s/2-1)) *
        (∫⁻ p, compactGaussianWindowKernel d φ u p ∂μ) := by
    calc
      _ = ∫⁻ u in Set.Ioc (0:ℝ) 1, r⁻¹ *
          (ENNReal.ofReal (u^(s/2-1)) * ∫⁻ p, compactGaussianWindowKernel d φ u p ∂μ) :=
        lintegral_congr (fun u => mul_left_comm _ _ _)
      _ = _ := lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hr0)
  refine ⟨hfactor.trans_ne (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hr0) hfin), ?_⟩
  rw [hfactor, ENNReal.toReal_mul, hreal]
  simp only [r, φ, ENNReal.toReal_inv, ENNReal.toReal_ofReal (pow_nonneg hL.le d)]

def positiveTailWeight (s u : ℝ) : ℝ≥0∞ := ENNReal.ofReal (u^(s/2-1))

theorem measurable_positiveTailWeight (s : ℝ) : Measurable (positiveTailWeight s) :=
  (measurable_id.pow_const (s/2-1)).ennreal_ofReal

theorem measurable_positiveTailBackground (d : ℕ) (s : ℝ) :
    Measurable (fun u => positiveTailWeight s u * ENNReal.ofReal (B d u)) := by
  exact (measurable_positiveTailWeight s).mul
    ((measurable_const.div measurable_id).pow_const ((d:ℝ)/2)).ennreal_ofReal

theorem positiveTailWeight_mul_B (d : ℕ) (s u : ℝ) (hu : 0 < u) :
    u^(s/2-1) * B d u = Real.pi^((d:ℝ)/2) * u^((s-(d:ℝ))/2-1) := by
  rw [B, Real.div_rpow Real.pi_pos.le hu.le,
    div_eq_mul_inv (Real.pi^((d:ℝ)/2)) (u^((d:ℝ)/2)), ← Real.rpow_neg hu.le]
  rw [mul_left_comm, ← Real.rpow_add hu]
  rw [show s/2-1 + -((d:ℝ)/2) = (s-(d:ℝ))/2-1 by ring]

theorem positiveTailBackground_lintegral_ne_top
    (d : ℕ) (s : ℝ) (hsd : s < (d:ℝ)) :
    (∫⁻ u in Set.Ioi (1:ℝ), positiveTailWeight s u * ENNReal.ofReal (B d u)) ≠ ∞ := by
  have hi : IntegrableOn (fun u : ℝ => Real.pi^((d:ℝ)/2) *
      u^((s-(d:ℝ))/2-1)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt
      (by linarith : (s-(d:ℝ))/2-1 < -1) zero_lt_one).const_mul _
  have heq : (fun u => positiveTailWeight s u * ENNReal.ofReal (B d u))
      =ᵐ[volume.restrict (Set.Ioi (1:ℝ))]
        (fun u => ENNReal.ofReal (Real.pi^((d:ℝ)/2) * u^((s-(d:ℝ))/2-1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [positiveTailWeight, ← ENNReal.ofReal_mul (Real.rpow_nonneg (zero_lt_one.trans hu).le _),
      positiveTailWeight_mul_B d s u (zero_lt_one.trans hu)]
  have hn : ∀ᵐ u ∂volume.restrict (Set.Ioi (1:ℝ)),
      0 ≤ Real.pi^((d:ℝ)/2) * u^((s-(d:ℝ))/2-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.rpow_nonneg (zero_lt_one.trans hu).le _)
  rw [lintegral_congr_ae heq, ← ofReal_integral_eq_lintegral_ofReal hi hn]
  exact ENNReal.ofReal_ne_top

theorem Q_le_gaussianRemainder_add_B
    (d : ℕ) (P : ConfigurationLaw d) (u : ℝ) (hu : 0 < u) :
    Q d P u ≤ gaussianRemainder d P u + ENNReal.ofReal (B d u) := by
  have hB : 0 ≤ B d u := Real.rpow_nonneg (div_pos Real.pi_pos hu).le _
  have hc : max (B d u - 1) 0 ≤ B d u := max_le (sub_le_self _ zero_le_one) hB
  exact (le_tsub_add : Q d P u ≤ Q d P u - ENNReal.ofReal (max (B d u - 1) 0) +
    ENNReal.ofReal (max (B d u - 1) 0)).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hc))

theorem positiveTailQ_lintegral_ne_top_of_W_ne_top
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d:ℝ))
    (P : ConfigurationLaw d) (hW : W d s P ≠ ⊤) :
    (∫⁻ u in Set.Ioi (1:ℝ), positiveTailWeight s u * Q d P u) ≠ ∞ := by
  have hr : (∫⁻ u in Set.Ioi (1:ℝ), positiveTailWeight s u * gaussianRemainder d P u) ≠ ∞ :=
    ne_top_of_le_ne_top
      (weighted_gaussianRemainder_lintegral_ne_top_of_W_ne_top_pos d s hs P hW)
      (lintegral_mono_set (show Set.Ioi (1:ℝ) ⊆ Set.Ioi 0 from fun _ hu =>
        lt_trans (show (0:ℝ) < 1 from zero_lt_one) hu))
  have hb := positiveTailBackground_lintegral_ne_top d s hsd
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hr, hb⟩)
  rw [← lintegral_add_right _ (measurable_positiveTailBackground d s)]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa only [mul_add] using mul_le_mul_right
    (Q_le_gaussianRemainder_add_B d P u (zero_lt_one.trans hu)) (positiveTailWeight s u)

theorem measurable_anchoredGaussianKernel_prod (d : ℕ) :
    Measurable (fun q : ℝ × (Rd d × Rd d) => anchoredGaussianKernel d q.1 q.2) := by
  have he : Measurable (fun q : ℝ × (Rd d × Rd d) =>
      ENNReal.ofReal (Real.exp (-(q.1 * ‖q.2.2-q.2.1‖^2)))) :=
    ((measurable_fst.mul (((measurable_snd.comp measurable_snd).sub
      (measurable_fst.comp measurable_snd)).norm.pow_const 2)).neg.exp).ennreal_ofReal
  exact Measurable.ite
    ((Riesz.Negative.measurableSet_cube d 1).preimage (measurable_fst.comp measurable_snd))
    he measurable_const

def compactWindowTailBound (d : ℕ) (χ : C_c(Rd d, ℝ)) : ℝ :=
  ‖χ.toBoundedContinuousFunction‖ * ∫ x, χ x

theorem compactWindowOverlap_le_tailBound
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) (z : Rd d) :
    compactWindowOverlap d χ L z ≤ compactWindowTailBound d χ := by
  let M : ℝ := ‖χ.toBoundedContinuousFunction‖
  have hbound (t : Rd d) : χ t * χ (t + L⁻¹ • z) ≤ M * χ t :=
    (mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans
      (χ.toBoundedContinuousFunction.norm_coe_le_norm (t + L⁻¹ • z))) (hχ t)).trans_eq (mul_comm _ _)
  exact (integral_mono_of_nonneg
    (Eventually.of_forall (fun t => mul_nonneg (hχ t) (hχ (t + L⁻¹ • z))))
    (χ.integrable.const_mul M) (Eventually.of_forall hbound)).trans_eq
      (integral_const_mul M (fun t => χ t))

theorem measurable_ofReal_compactWindowOverlap_pair
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) :
    Measurable (fun p : Rd d × Rd d => ENNReal.ofReal (compactWindowOverlap d χ L (p.2-p.1))) := by
  have heq : (fun p : Rd d × Rd d => ENNReal.ofReal (compactWindowOverlap d χ L (p.2-p.1))) =
      fun p : Rd d × Rd d => nonnegativeWindowOverlap d (fun x => ENNReal.ofReal (χ x))
        (L⁻¹ • (p.2-p.1)) :=
    funext (fun p => (nonnegativeWindowOverlap_ofReal d χ hχ _).symm)
  rw [heq]
  exact (measurable_nonnegativeWindowOverlap d _ χ.continuous.measurable.ennreal_ofReal).comp
    ((measurable_const_smul L⁻¹).comp (measurable_snd.sub measurable_fst))

theorem weightedGaussian_overlap_lintegral_tendsto
    (d : ℕ) (s : ℝ) (Γ : Measure (Rd d × Rd d)) [SFinite Γ]
    (τ : Measure ℝ) [SFinite τ]
    (hfin : (∫⁻ u, positiveTailWeight s u * (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) ∂τ) ≠ ∞)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℕ → ℝ) (hLinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ u, positiveTailWeight s u *
      (∫⁻ p, ENNReal.ofReal (compactWindowOverlap d χ (L n) (p.2-p.1)) *
        anchoredGaussianKernel d u p ∂Γ) ∂τ) atTop
      (𝓝 (ENNReal.ofReal (compactAnchorSquareMass d χ) *
        (∫⁻ u, positiveTailWeight s u * (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) ∂τ))) := by
  let H : ℝ × (Rd d × Rd d) → ℝ≥0∞ := fun q =>
    positiveTailWeight s q.1 * anchoredGaussianKernel d q.1 q.2
  let ν : Measure (ℝ × (Rd d × Rd d)) := (τ.prod Γ).withDensity H
  let F : ℕ → ℝ × (Rd d × Rd d) → ℝ≥0∞ := fun n q =>
    ENNReal.ofReal (compactWindowOverlap d χ (L n) (q.2.2-q.2.1))
  have hH : Measurable H := ((measurable_positiveTailWeight s).comp measurable_fst).mul
    (measurable_anchoredGaussianKernel_prod d)
  have hF (n : ℕ) : Measurable (F n) :=
    (measurable_ofReal_compactWindowOverlap_pair d χ hχ (L n)).comp measurable_snd
  have hmass : ν Set.univ = ∫⁻ u, positiveTailWeight s u *
      (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) ∂τ := by
    rw [withDensity_apply H MeasurableSet.univ, Measure.restrict_univ,
      lintegral_prod _ hH.aemeasurable]
    exact lintegral_congr (fun u => lintegral_const_mul (μ := Γ)
      (positiveTailWeight s u) (measurable_anchoredGaussianKernel d u))
  have hbound (n : ℕ) : F n ≤ᵐ[ν] (fun _ => ENNReal.ofReal (compactWindowTailBound d χ)) :=
    Eventually.of_forall (fun q => ENNReal.ofReal_le_ofReal
      (compactWindowOverlap_le_tailBound d χ hχ (L n) (q.2.2-q.2.1)))
  have hdom : (∫⁻ q, ENNReal.ofReal (compactWindowTailBound d χ) ∂ν) ≠ ∞ := by
    rw [lintegral_const, hmass]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hpoint : ∀ᵐ q ∂ν, Tendsto (fun n => F n q) atTop
      (𝓝 (ENNReal.ofReal (compactAnchorSquareMass d χ))) :=
    Eventually.of_forall (fun q => ENNReal.tendsto_ofReal
      (compactWindowOverlap_tendsto_of_inv_tendsto_zero d χ hχ L hLinv (q.2.2-q.2.1)))
  have hdct := tendsto_lintegral_of_dominated_convergence (μ := ν)
    (fun _ => ENNReal.ofReal (compactWindowTailBound d χ)) hF hbound hdom hpoint
  have htransport (n : ℕ) : (∫⁻ q, F n q ∂ν) =
      ∫⁻ u, positiveTailWeight s u * (∫⁻ p,
        ENNReal.ofReal (compactWindowOverlap d χ (L n) (p.2-p.1)) *
          anchoredGaussianKernel d u p ∂Γ) ∂τ := by
    rw [lintegral_withDensity_eq_lintegral_mul (τ.prod Γ) hH (hF n),
      lintegral_prod _ (hH.mul (hF n)).aemeasurable]
    refine lintegral_congr (fun u => ?_)
    refine (lintegral_congr ?_).trans (lintegral_const_mul (μ := Γ)
      (positiveTailWeight s u)
      ((measurable_ofReal_compactWindowOverlap_pair d χ hχ (L n)).mul
        (measurable_anchoredGaussianKernel d u)))
    intro p
    simp only [H, F, Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm]
  have htarget : (∫⁻ q, ENNReal.ofReal (compactAnchorSquareMass d χ) ∂ν) =
      ENNReal.ofReal (compactAnchorSquareMass d χ) * (∫⁻ u, positiveTailWeight s u *
        (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) ∂τ) := by
    rw [lintegral_const, hmass]
  simpa only [htransport, htarget] using hdct

theorem weightedGaussian_overlap_lintegral_le
    (d : ℕ) (s : ℝ) (Γ : Measure (Rd d × Rd d))
    (τ : Measure ℝ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) :
    (∫⁻ u, positiveTailWeight s u *
      (∫⁻ p, ENNReal.ofReal (compactWindowOverlap d χ L (p.2-p.1)) *
        anchoredGaussianKernel d u p ∂Γ) ∂τ) ≤
      ENNReal.ofReal (compactWindowTailBound d χ) *
        (∫⁻ u, positiveTailWeight s u *
          (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) ∂τ) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (compactWindowTailBound d χ)
  have hi (u : ℝ) : (∫⁻ p,
      ENNReal.ofReal (compactWindowOverlap d χ L (p.2-p.1)) *
        anchoredGaussianKernel d u p ∂Γ) ≤
      C * (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) := by
    refine (lintegral_mono (fun p => mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (compactWindowOverlap_le_tailBound d χ hχ L _))
      (anchoredGaussianKernel d u p))).trans_eq ?_
    exact lintegral_const_mul C (measurable_anchoredGaussianKernel d u)
  refine (lintegral_mono (fun u => mul_le_mul_right (hi u)
    (positiveTailWeight s u))).trans_eq ?_
  simpa only [mul_left_comm] using lintegral_const_mul' (μ := τ) C
    (fun u => positiveTailWeight s u * (∫⁻ p, anchoredGaussianKernel d u p ∂Γ))
    ENNReal.ofReal_ne_top

theorem weightedGaussian_overlap_lintegral_toReal_tendsto
    (d : ℕ) (s : ℝ) (Γ : Measure (Rd d × Rd d)) [SFinite Γ]
    (τ : Measure ℝ) [SFinite τ]
    (hfin : (∫⁻ u, positiveTailWeight s u *
      (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) ∂τ) ≠ ∞)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℕ → ℝ) (hLinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun n => (∫⁻ u, positiveTailWeight s u *
      (∫⁻ p, ENNReal.ofReal (compactWindowOverlap d χ (L n) (p.2-p.1)) *
        anchoredGaussianKernel d u p ∂Γ) ∂τ).toReal) atTop
      (𝓝 (compactAnchorSquareMass d χ *
        (∫⁻ u, positiveTailWeight s u *
          (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) ∂τ).toReal)) := by
  have h := weightedGaussian_overlap_lintegral_tendsto d s Γ τ hfin χ hχ L hLinv
  have ht : ENNReal.ofReal (compactAnchorSquareMass d χ) *
      (∫⁻ u, positiveTailWeight s u *
        (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) ∂τ) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have ha : 0 ≤ compactAnchorSquareMass d χ :=
    integral_nonneg (fun x => sq_nonneg (χ x))
  simpa only [Function.comp_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha] using
    (ENNReal.continuousAt_toReal ht).tendsto.comp h

def originalPositiveHighUFactorialWindow
    (d : ℕ) (s : ℝ) (P : ConfigurationLaw d)
    (χ : C_c(Rd d, ℝ)) (L : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u *
    ((ENNReal.ofReal (L^d))⁻¹ *
      (∫⁻ μ, ∫⁻ x, ∫⁻ y, if x = y then 0 else
        ENNReal.ofReal (χ (L⁻¹ • x) * χ (L⁻¹ • y) *
          Real.exp (-(u * ‖y-x‖^(2:ℕ)))) ∂μ ∂μ ∂P))

def positiveHighUBackgroundWindow
    (d : ℕ) (s : ℝ) (χ : C_c(Rd d, ℝ)) (L : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u *
    ((ENNReal.ofReal (L^d))⁻¹ *
      (∫⁻ p : Rd d × Rd d,
        ENNReal.ofReal (χ (L⁻¹ • p.1)) * ENNReal.ofReal (χ (L⁻¹ • p.2)) *
          ENNReal.ofReal (Real.exp (-(u * ‖p.2-p.1‖^(2:ℕ))))
          ∂(volume : Measure (Rd d)).prod volume))

theorem originalPositiveHighUFactorialWindow_eq_overlap
    (d : ℕ) (s : ℝ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) (hL : 0 < L) :
    originalPositiveHighUFactorialWindow d s P χ L =
      ∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u *
        (∫⁻ p, ENNReal.ofReal (compactWindowOverlap d χ L (p.2-p.1)) *
          anchoredGaussianKernel d u p
            ∂originalAdmissibleFactorialMeasure d P hP) := by
  unfold originalPositiveHighUFactorialWindow
  exact lintegral_congr (fun u => congrArg (fun v => positiveTailWeight s u * v)
    (originalAdmissible_scaled_compactGaussian_factorial_eq_cube_overlap
      d P hP χ hχ L hL u))

theorem scaled_compactGaussian_background_eq_overlap
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℝ) (hL : 0 < L) (u : ℝ) :
    (ENNReal.ofReal (L^d))⁻¹ *
      (∫⁻ p : Rd d × Rd d,
        ENNReal.ofReal (χ (L⁻¹ • p.1)) * ENNReal.ofReal (χ (L⁻¹ • p.2)) *
          ENNReal.ofReal (Real.exp (-(u * ‖p.2-p.1‖^(2:ℕ))))
          ∂(volume : Measure (Rd d)).prod volume) =
      ∫⁻ p, ENNReal.ofReal (compactWindowOverlap d χ L (p.2-p.1)) *
        anchoredGaussianKernel d u p ∂(volume : Measure (Rd d)).prod volume := by
  let Δ : Measure (Rd d × Rd d) := (volume : Measure (Rd d)).prod volume
  have hΔ (v : Rd d) :
      Δ.map (fun p : Rd d × Rd d => (v+p.1, v+p.2)) = Δ :=
    map_add_left_eq_self Δ (v,v)
  have hc : Measurable (fun x : Rd d => ENNReal.ofReal (χ x)) :=
    χ.continuous.measurable.ennreal_ofReal
  have hg : Measurable (fun z : Rd d =>
      ENNReal.ofReal (Real.exp (-(u * ‖z‖^(2:ℕ))))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
      ((continuous_const.mul (continuous_id.norm.pow 2)).neg)).measurable
  have heq := lintegral_stationaryPair_scaled_window_eq_cube_overlap
    d Δ hΔ _ _ hc hg L hL
  simp_rw [nonnegativeWindowOverlap_ofReal d χ hχ] at heq
  simpa only [Δ, compactWindowOverlap, anchoredGaussianKernel, Set.indicator,
    ite_mul, mul_ite, one_mul, zero_mul, mul_comm] using heq

theorem positiveHighUBackgroundWindow_eq_overlap
    (d : ℕ) (s : ℝ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℝ) (hL : 0 < L) :
    positiveHighUBackgroundWindow d s χ L =
      ∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u *
        (∫⁻ p, ENNReal.ofReal (compactWindowOverlap d χ L (p.2-p.1)) *
          anchoredGaussianKernel d u p ∂(volume : Measure (Rd d)).prod volume) := by
  exact lintegral_congr (fun u => congrArg (fun v => positiveTailWeight s u * v)
    (scaled_compactGaussian_background_eq_overlap d χ hχ L hL u))

theorem positiveTailBackground_mass_eq (d : ℕ) (s : ℝ) :
    (∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u *
      (∫⁻ p, anchoredGaussianKernel d u p ∂(volume : Measure (Rd d)).prod volume)) =
      ∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u * ENNReal.ofReal (B d u) := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [anchoredGaussian_background_lintegral d u (zero_lt_one.trans hu)]

theorem positiveTailFactorial_mass_eq
    (d : ℕ) (s : ℝ) (P : ConfigurationLaw d) (hP : Admissible d P) :
    (∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u *
      (∫⁻ p, anchoredGaussianKernel d u p ∂originalAdmissibleFactorialMeasure d P hP)) =
      ∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u * Q d P u := by
  exact lintegral_congr (fun u => congrArg (fun v => positiveTailWeight s u * v)
    (Q_eq_originalAdmissibleFactorialMeasure d P hP u).symm)

theorem originalPositiveHighU_windows_ne_top
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) (hL : 0 < L) :
    originalPositiveHighUFactorialWindow d s P χ L ≠ ∞ ∧
      positiveHighUBackgroundWindow d s χ L ≠ ∞ := by
  constructor
  · rw [originalPositiveHighUFactorialWindow_eq_overlap d s P hP χ hχ L hL]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ((positiveTailFactorial_mass_eq d s P hP).trans_ne
          (positiveTailQ_lintegral_ne_top_of_W_ne_top d s hs hsd P hW)))
      (weightedGaussian_overlap_lintegral_le d s
        (originalAdmissibleFactorialMeasure d P hP)
        (volume.restrict (Set.Ioi 1)) χ hχ L)
  · rw [positiveHighUBackgroundWindow_eq_overlap d s χ hχ L hL]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ((positiveTailBackground_mass_eq d s).trans_ne
          (positiveTailBackground_lintegral_ne_top d s hsd)))
      (weightedGaussian_overlap_lintegral_le d s
        ((volume : Measure (Rd d)).prod volume)
        (volume.restrict (Set.Ioi 1)) χ hχ L)

theorem originalPositiveHighU_centered_window_tendsto
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (hLinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun n => (originalPositiveHighUFactorialWindow d s P χ (L n)).toReal -
        (positiveHighUBackgroundWindow d s χ (L n)).toReal) atTop
      (𝓝 (compactAnchorSquareMass d χ *
        ((∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u * Q d P u).toReal -
          (∫⁻ u in Set.Ioi (1 : ℝ),
            positiveTailWeight s u * ENNReal.ofReal (B d u)).toReal))) := by
  have hA0 := weightedGaussian_overlap_lintegral_toReal_tendsto d s
    (originalAdmissibleFactorialMeasure d P hP) (volume.restrict (Set.Ioi 1))
    ((positiveTailFactorial_mass_eq d s P hP).trans_ne
      (positiveTailQ_lintegral_ne_top_of_W_ne_top d s hs hsd P hW)) χ hχ L hLinv
  have hA : Tendsto (fun n => (originalPositiveHighUFactorialWindow d s P χ (L n)).toReal)
      atTop (𝓝 (compactAnchorSquareMass d χ *
        (∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u * Q d P u).toReal)) := by
    simpa only [positiveTailFactorial_mass_eq] using hA0.congr (fun n =>
      congrArg ENNReal.toReal
        (originalPositiveHighUFactorialWindow_eq_overlap d s P hP χ hχ (L n) (hL n)).symm)
  have hB0 := weightedGaussian_overlap_lintegral_toReal_tendsto d s
    ((volume : Measure (Rd d)).prod volume) (volume.restrict (Set.Ioi 1))
    ((positiveTailBackground_mass_eq d s).trans_ne
      (positiveTailBackground_lintegral_ne_top d s hsd)) χ hχ L hLinv
  have hB : Tendsto (fun n => (positiveHighUBackgroundWindow d s χ (L n)).toReal)
      atTop (𝓝 (compactAnchorSquareMass d χ *
        (∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u * ENNReal.ofReal (B d u)).toReal)) := by
    simpa only [positiveTailBackground_mass_eq] using hB0.congr (fun n =>
      congrArg ENNReal.toReal
        (positiveHighUBackgroundWindow_eq_overlap d s χ hχ (L n) (hL n)).symm)
  simpa only [mul_sub] using hA.sub hB

theorem finite_lintegral_toReal_sub_eq_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfint : (∫⁻ x, f x ∂μ) ≠ ∞) (hgint : (∫⁻ x, g x ∂μ) ≠ ∞) :
    (∫⁻ x, f x ∂μ).toReal - (∫⁻ x, g x ∂μ).toReal =
      ∫ x, (f x).toReal - (g x).toReal ∂μ := by
  have hfi := integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfint
  have hgi := integrable_toReal_of_lintegral_ne_top hg.aemeasurable hgint
  rw [integral_sub hfi hgi, integral_toReal hf.aemeasurable (ae_lt_top hf hfint),
    integral_toReal hg.aemeasurable (ae_lt_top hg hgint)]

theorem measurable_Q_positiveTail (d : ℕ) (P : ConfigurationLaw d) :
    Measurable (Q d P) :=
  (antitone_Q d P).measurable

theorem measurable_gaussianRemainder_positiveTail (d : ℕ) (P : ConfigurationLaw d) :
    Measurable (gaussianRemainder d P) :=
  (measurable_Q_positiveTail d P).sub
    ((((measurable_const.div measurable_id).pow_const ((d : ℝ)/2)).sub_const 1).max
      measurable_const).ennreal_ofReal

theorem gaussianRemainder_toReal_sub_B
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (u : ℝ) (hu : 0 < u) (hQ : Q d P u ≠ ∞) :
    (Q d P u).toReal - B d u =
      (gaussianRemainder d P u).toReal - min 1 (B d u) := by
  have hB : 0 ≤ B d u := Real.rpow_nonneg (div_pos Real.pi_pos hu).le _
  have hc : 0 ≤ max (B d u - 1) 0 := le_max_right _ _
  rw [gaussianRemainder,
    ENNReal.toReal_sub_of_le (gaussian_covariance_lower_bound_of_admissible d P hP u hu) hQ,
    ENNReal.toReal_ofReal hc]
  rcases le_total (B d u) 1 with h | h
  · simp only [max_eq_right (sub_nonpos.mpr h), min_eq_right h, sub_zero]
  · rw [max_eq_left (sub_nonneg.mpr h), min_eq_left h]
    ring

theorem positiveTail_centered_mass_eq_integral
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (P : ConfigurationLaw d) (hW : W d s P ≠ ⊤) :
    (∫⁻ u in Set.Ioi (1 : ℝ), positiveTailWeight s u * Q d P u).toReal -
        (∫⁻ u in Set.Ioi (1 : ℝ),
          positiveTailWeight s u * ENNReal.ofReal (B d u)).toReal =
      ∫ u : ℝ in Set.Ioi 1, u ^ (s/2-1) * ((Q d P u).toReal - B d u) := by
  rw [finite_lintegral_toReal_sub_eq_integral (volume.restrict (Set.Ioi (1 : ℝ)))
    (fun u => positiveTailWeight s u * Q d P u)
    (fun u => positiveTailWeight s u * ENNReal.ofReal (B d u))
    ((measurable_positiveTailWeight s).mul (measurable_Q_positiveTail d P))
    (measurable_positiveTailBackground d s)
    (positiveTailQ_lintegral_ne_top_of_W_ne_top d s hs hsd P hW)
    (positiveTailBackground_lintegral_ne_top d s hsd)]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [positiveTailWeight, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (zero_lt_one.trans hu).le _),
    ENNReal.toReal_ofReal (show 0 ≤ B d u from
      Real.rpow_nonneg (div_pos Real.pi_pos (zero_lt_one.trans hu)).le _), mul_sub]

theorem positiveSignedGaussian_integrable_and_W_toReal
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    IntegrableOn (fun u : ℝ => u ^ (s/2-1) *
      ((Q d P u).toReal - B d u)) (Set.Ioi 0) ∧
    gamma_s s * (∫ u : ℝ in Set.Ioi 0,
      u ^ (s/2-1) * ((Q d P u).toReal - B d u)) = (W d s P).toReal := by
  let R : ℝ → ℝ≥0∞ := fun u => positiveTailWeight s u * gaussianRemainder d P u
  let I : ℝ≥0∞ := ∫⁻ u in Set.Ioi (0 : ℝ), R u
  have hI : I ≠ ∞ :=
    weighted_gaussianRemainder_lintegral_ne_top_of_W_ne_top_pos d s hs P hW
  have hRm : Measurable R := (measurable_positiveTailWeight s).mul
    (measurable_gaussianRemainder_positiveTail d P)
  have hiR : IntegrableOn (fun u => (R u).toReal) (Set.Ioi 0) :=
    integrable_toReal_of_lintegral_ne_top hRm.aemeasurable hI
  have hiRef := weightedPositiveReference_integrable d s hs hsd
  have heq : (fun u : ℝ => u ^ (s/2-1) * ((Q d P u).toReal - B d u))
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun u => (R u).toReal - weightedPositiveReference d s u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [gaussianRemainder_toReal_sub_B d P hP u hu
      (Q_ne_top_of_W_ne_top_pos d s hs P hW u hu)]
    simp only [R, positiveTailWeight, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hu.le _), weightedPositiveReference, mul_sub]
  refine ⟨(hiR.sub hiRef).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_sub hiR hiRef,
    integral_toReal hRm.aemeasurable (ae_lt_top hRm hI), mul_sub,
    gamma_positive_reference_eq_neg_c0 d s hs hsd]
  have hg : 0 ≤ gamma_s s := (Riesz.Analysis.gamma_s_pos s (by linarith)).le
  have hprod : ENNReal.ofReal (gamma_s s) * I ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI
  have hWrepr : W d s P = ((c0 d s + gamma_s s * I.toReal : ℝ) : EReal) := by
    change (c0 d s : EReal) + ((ENNReal.ofReal (gamma_s s) * I : ℝ≥0∞) : EReal) = _
    rw [← EReal.coe_ennreal_toReal hprod, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hg, ← EReal.coe_add]
  rw [hWrepr, EReal.toReal_coe, sub_neg_eq_add, add_comm]

theorem integrable_positiveGaussian_scalar (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    IntegrableOn (fun u : ℝ => u ^ (s/2-1) *
      Real.exp (-(u * r^(2:ℕ)))) (Set.Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  exact right_ne_zero_of_mul ((Riesz.Analysis.gamma_kernel_pos s r hs hr).symm.trans_ne
    (ne_of_gt (div_pos (Real.rpow_pos_of_pos hr _) hs)))

theorem ofReal_K_s_eq_gaussian_lintegral
    (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    ENNReal.ofReal (K_s s r) = ENNReal.ofReal (gamma_s s) *
      (∫⁻ u in Set.Ioi (0 : ℝ), positiveTailWeight s u *
        ENNReal.ofReal (Real.exp (-(u * r^(2:ℕ))))) := by
  have hg := (Riesz.Analysis.gamma_s_pos s (by linarith)).le
  have hn : ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      0 ≤ u ^ (s/2-1) * Real.exp (-(u * r^(2:ℕ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le
  rw [Riesz.Analysis.gamma_kernel_pos s r hs hr, ENNReal.ofReal_mul hg,
    ofReal_integral_eq_lintegral_ofReal (integrable_positiveGaussian_scalar s r hs hr) hn]
  refine congrArg (fun v => ENNReal.ofReal (gamma_s s) * v) (lintegral_congr_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _)

def offSitePositiveWindowKernel (d : ℕ) (s : ℝ) (φ : C_c(Rd d, ℝ))
    (p : Rd d × Rd d) : ℝ≥0∞ :=
  if p.1 = p.2 then 0 else
    ENNReal.ofReal (φ p.1) * ENNReal.ofReal (φ p.2) * ENNReal.ofReal (K_s s ‖p.2-p.1‖)

def offSiteGaussianWindowKernel (d : ℕ) (φ : C_c(Rd d, ℝ)) (u : ℝ)
    (p : Rd d × Rd d) : ℝ≥0∞ :=
  if p.1 = p.2 then 0 else compactGaussianWindowKernel d φ u p

theorem measurable_offSiteGaussianWindowKernel_joint
    (d : ℕ) (φ : C_c(Rd d, ℝ)) :
    Measurable (fun q : ℝ × (Rd d × Rd d) => offSiteGaussianWindowKernel d φ q.1 q.2) := by
  exact Measurable.ite
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd)) measurable_const
    (((φ.continuous.measurable.ennreal_ofReal.comp (measurable_fst.comp measurable_snd)).mul
      (φ.continuous.measurable.ennreal_ofReal.comp (measurable_snd.comp measurable_snd))).mul
      ((measurable_fst.neg.mul (((measurable_snd.comp measurable_snd).sub
        (measurable_fst.comp measurable_snd)).norm.pow_const 2)).exp).ennreal_ofReal)

theorem offSitePositiveWindowKernel_eq_gaussian_lintegral
    (d : ℕ) (s : ℝ) (hs : 0 < s) (φ : C_c(Rd d, ℝ))
    (p : Rd d × Rd d) :
    offSitePositiveWindowKernel d s φ p = ENNReal.ofReal (gamma_s s) *
      ∫⁻ u in Set.Ioi (0 : ℝ), positiveTailWeight s u *
        offSiteGaussianWindowKernel d φ u p := by
  by_cases hp : p.1 = p.2
  · simp only [offSitePositiveWindowKernel, offSiteGaussianWindowKernel,
      if_pos hp, mul_zero, lintegral_zero]
  · have hr : 0 < ‖p.2-p.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hp))
    simp only [offSitePositiveWindowKernel, offSiteGaussianWindowKernel, if_neg hp,
      compactGaussianWindowKernel, ofReal_K_s_eq_gaussian_lintegral s _ hs hr, neg_mul]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun v => ENNReal.ofReal (gamma_s s) * v)
        (lintegral_const_mul' (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          (ENNReal.ofReal (φ p.1) * ENNReal.ofReal (φ p.2))
          (fun u => positiveTailWeight s u *
            ENNReal.ofReal (Real.exp (-(u * ‖p.2-p.1‖^(2:ℕ)))))
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).symm

theorem lintegral_offSitePositiveWindowKernel_eq_gaussian
    (d : ℕ) (s : ℝ) (hs : 0 < s) (Γ : Measure (Rd d × Rd d)) [SFinite Γ]
    (φ : C_c(Rd d, ℝ)) :
    (∫⁻ p, offSitePositiveWindowKernel d s φ p ∂Γ) =
      ENNReal.ofReal (gamma_s s) * ∫⁻ u in Set.Ioi (0 : ℝ),
        positiveTailWeight s u * (∫⁻ p, offSiteGaussianWindowKernel d φ u p ∂Γ) := by
  simp_rw [offSitePositiveWindowKernel_eq_gaussian_lintegral d s hs φ]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine congrArg (fun v => ENNReal.ofReal (gamma_s s) * v) ?_
  have hm : Measurable (fun q : ℝ × (Rd d × Rd d) =>
      positiveTailWeight s q.1 * offSiteGaussianWindowKernel d φ q.1 q.2) :=
    ((measurable_positiveTailWeight s).comp measurable_fst).mul
      (measurable_offSiteGaussianWindowKernel_joint d φ)
  exact (lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := Γ)
    (f := fun (u : ℝ) (p : Rd d × Rd d) =>
      positiveTailWeight s u * offSiteGaussianWindowKernel d φ u p) hm.aemeasurable).symm.trans
    (lintegral_congr (fun u => lintegral_const_mul' (μ := Γ) (positiveTailWeight s u)
      (fun p => offSiteGaussianWindowKernel d φ u p) ENNReal.ofReal_ne_top))

theorem original_gaussianWindow_offSite_eq
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (φ : C_c(Rd d, ℝ)) (u : ℝ) :
    (∫⁻ p, offSiteGaussianWindowKernel d φ u p
      ∂originalAdmissibleFactorialMeasure d P hP) =
      ∫⁻ p, compactGaussianWindowKernel d φ u p
        ∂originalAdmissibleFactorialMeasure d P hP := by
  have hk := measurable_compactGaussianWindowKernel d φ u
  rw [lintegral_originalAdmissibleFactorialMeasure_eq_pair_lintegral d P hP
      (offSiteGaussianWindowKernel d φ u)
      (Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd)
        measurable_const hk),
    lintegral_originalAdmissibleFactorialMeasure_eq_pair_lintegral d P hP _ hk]
  simp +contextual [offSiteGaussianWindowKernel]

theorem volume_product_ae_ne (d : ℕ) (hd : 0 < d) :
    ∀ᵐ p : Rd d × Rd d ∂(volume : Measure (Rd d)).prod volume, p.1 ≠ p.2 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun measurable_fst measurable_snd).compl).2
  exact Eventually.of_forall (fun x => ((volume : Measure (Rd d)).ae_ne x).mono
    (fun _ hy => Ne.symm hy))

theorem background_gaussianWindow_offSite_eq
    (d : ℕ) (hd : 0 < d) (φ : C_c(Rd d, ℝ)) (u : ℝ) :
    (∫⁻ p, offSiteGaussianWindowKernel d φ u p
      ∂(volume : Measure (Rd d)).prod volume) =
      ∫⁻ p, compactGaussianWindowKernel d φ u p
        ∂(volume : Measure (Rd d)).prod volume := by
  exact lintegral_congr_ae ((volume_product_ae_ne d hd).mono (fun _ hp => if_neg hp))

def normalizedCompactGaussianWindowMass
    (d : ℕ) (s : ℝ) (μ : Measure (Rd d × Rd d))
    (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) (I : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ u in I, positiveTailWeight s u *
    ((ENNReal.ofReal (L^d))⁻¹ *
      ∫⁻ p, compactGaussianWindowKernel d (angularScaledCompactWindow d χ L hL) u p ∂μ)

def normalizedCompactPositiveWindowMass
    (d : ℕ) (s : ℝ) (μ : Measure (Rd d × Rd d))
    (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) : ℝ≥0∞ :=
  (ENNReal.ofReal (L^d))⁻¹ *
    ∫⁻ p, offSitePositiveWindowKernel d s (angularScaledCompactWindow d χ L hL) p ∂μ

theorem normalizedCompactPositiveWindowMass_eq_head_tail
    (d : ℕ) (s : ℝ) (hs : 0 < s) (μ : Measure (Rd d × Rd d)) [SFinite μ]
    (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L)
    (hoff : ∀ u : ℝ,
      (∫⁻ p, offSiteGaussianWindowKernel d (angularScaledCompactWindow d χ L hL) u p ∂μ) =
        ∫⁻ p, compactGaussianWindowKernel d (angularScaledCompactWindow d χ L hL) u p ∂μ) :
    normalizedCompactPositiveWindowMass d s μ χ L hL = ENNReal.ofReal (gamma_s s) *
      (normalizedCompactGaussianWindowMass d s μ χ L hL (Set.Ioc 0 1) +
        normalizedCompactGaussianWindowMass d s μ χ L hL (Set.Ioi 1)) := by
  let r : ℝ≥0∞ := (ENNReal.ofReal (L^d))⁻¹
  let φ := angularScaledCompactWindow d χ L hL
  have hr : r ≠ ∞ := (ENNReal.ofReal_inv_of_pos (pow_pos hL d)).symm.trans_ne
    ENNReal.ofReal_ne_top
  have hpush : r * (∫⁻ u in Set.Ioi (0 : ℝ), positiveTailWeight s u *
      (∫⁻ p, offSiteGaussianWindowKernel d φ u p ∂μ)) =
      ∫⁻ u in Set.Ioi (0 : ℝ), positiveTailWeight s u *
        (r * ∫⁻ p, compactGaussianWindowKernel d φ u p ∂μ) := by
    simpa only [φ, hoff, mul_left_comm] using
      (lintegral_const_mul' (μ := volume.restrict (Set.Ioi (0 : ℝ))) r
        (fun u => positiveTailWeight s u *
          (∫⁻ p, offSiteGaussianWindowKernel d φ u p ∂μ)) hr).symm
  have hsplit : (∫⁻ u in Set.Ioi (0 : ℝ), positiveTailWeight s u *
      (r * ∫⁻ p, compactGaussianWindowKernel d φ u p ∂μ)) =
      normalizedCompactGaussianWindowMass d s μ χ L hL (Set.Ioc 0 1) +
        normalizedCompactGaussianWindowMass d s μ χ L hL (Set.Ioi 1) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one),
      lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
    rfl
  simpa only [normalizedCompactPositiveWindowMass,
    lintegral_offSitePositiveWindowKernel_eq_gaussian d s hs μ, φ, r, mul_left_comm] using
    congrArg (fun v => ENNReal.ofReal (gamma_s s) * v) (hpush.trans hsplit)

theorem normalizedCompactPositiveWindowMass_finite_and_toReal
    (d : ℕ) (s : ℝ) (hs : 0 < s) (μ : Measure (Rd d × Rd d)) [SFinite μ]
    (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L)
    (hoff : ∀ u : ℝ,
      (∫⁻ p, offSiteGaussianWindowKernel d (angularScaledCompactWindow d χ L hL) u p ∂μ) =
        ∫⁻ p, compactGaussianWindowKernel d (angularScaledCompactWindow d χ L hL) u p ∂μ)
    (hhead : normalizedCompactGaussianWindowMass d s μ χ L hL (Set.Ioc 0 1) ≠ ∞)
    (htail : normalizedCompactGaussianWindowMass d s μ χ L hL (Set.Ioi 1) ≠ ∞) :
    (∫⁻ p, offSitePositiveWindowKernel d s (angularScaledCompactWindow d χ L hL) p ∂μ) ≠ ∞ ∧
      normalizedCompactPositiveWindowMass d s μ χ L hL ≠ ∞ ∧
      (normalizedCompactPositiveWindowMass d s μ χ L hL).toReal = gamma_s s *
        ((normalizedCompactGaussianWindowMass d s μ χ L hL (Set.Ioc 0 1)).toReal +
          (normalizedCompactGaussianWindowMass d s μ χ L hL (Set.Ioi 1)).toReal) := by
  have heq := normalizedCompactPositiveWindowMass_eq_head_tail d s hs μ χ L hL hoff
  have hnorm : normalizedCompactPositiveWindowMass d s μ χ L hL ≠ ∞ :=
    heq.trans_ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hhead, htail⟩))
  refine ⟨(ENNReal.lt_top_of_mul_ne_top_right hnorm
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)).ne, hnorm, ?_⟩
  rw [heq, ENNReal.toReal_mul, ENNReal.toReal_add hhead htail,
    ENNReal.toReal_ofReal (Riesz.Analysis.gamma_s_pos s (by linarith)).le]

def originalPositiveFullWindow
    (d : ℕ) (s : ℝ) (P : ConfigurationLaw d) (χ : C_c(Rd d, ℝ)) (L : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (L^d))⁻¹ * ∫⁻ μ, ∫⁻ x, ∫⁻ y, if x = y then 0 else
    ENNReal.ofReal (χ (L⁻¹ • x) * χ (L⁻¹ • y) * K_s s ‖y-x‖) ∂μ ∂μ ∂P

def positiveFullBackgroundWindow
    (d : ℕ) (s : ℝ) (χ : C_c(Rd d, ℝ)) (L : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (L^d))⁻¹ * ∫⁻ p : Rd d × Rd d, if p.1 = p.2 then 0 else
    ENNReal.ofReal (χ (L⁻¹ • p.1) * χ (L⁻¹ • p.2) * K_s s ‖p.2-p.1‖)
      ∂(volume : Measure (Rd d)).prod volume

def originalPositiveFullCenteredWindow
    (d : ℕ) (s : ℝ) (P : ConfigurationLaw d) (χ : C_c(Rd d, ℝ)) (L : ℝ) : ℝ :=
  (originalPositiveFullWindow d s P χ L).toReal - (positiveFullBackgroundWindow d s χ L).toReal

theorem measurable_offSitePositiveWindowKernel
    (d : ℕ) (s : ℝ) (φ : C_c(Rd d, ℝ)) :
    Measurable (offSitePositiveWindowKernel d s φ) := by
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
    (((φ.continuous.measurable.ennreal_ofReal.comp measurable_fst).mul
      (φ.continuous.measurable.ennreal_ofReal.comp measurable_snd)).mul
      (((measurable_snd.sub measurable_fst).norm.pow_const (-s)).div_const s).ennreal_ofReal)

theorem offSitePositiveWindowKernel_eq_ofReal
    (d : ℕ) (s : ℝ) (φ : C_c(Rd d, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
    (p : Rd d × Rd d) :
    offSitePositiveWindowKernel d s φ p =
      if p.1 = p.2 then 0 else ENNReal.ofReal (φ p.1 * φ p.2 * K_s s ‖p.2-p.1‖) := by
  simp only [offSitePositiveWindowKernel,
    ENNReal.ofReal_mul (mul_nonneg (hφ p.1) (hφ p.2)), ENNReal.ofReal_mul (hφ p.1)]

theorem normalizedCompactPositiveWindowMass_background
    (d : ℕ) (s : ℝ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℝ) (hL : 0 < L) :
    normalizedCompactPositiveWindowMass d s ((volume : Measure (Rd d)).prod volume)
      χ L hL = positiveFullBackgroundWindow d s χ L := by
  simp only [normalizedCompactPositiveWindowMass, positiveFullBackgroundWindow,
    offSitePositiveWindowKernel_eq_ofReal d s (angularScaledCompactWindow d χ L hL)
      (fun z => hχ (L⁻¹ • z)), angularScaledCompactWindow_apply]

theorem normalizedCompactPositiveWindowMass_original
    (d : ℕ) (s : ℝ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) (hL : 0 < L) :
    normalizedCompactPositiveWindowMass d s (originalAdmissibleFactorialMeasure d P hP)
      χ L hL = originalPositiveFullWindow d s P χ L := by
  unfold normalizedCompactPositiveWindowMass originalPositiveFullWindow
  rw [lintegral_originalAdmissibleFactorialMeasure_eq_pair_lintegral d P hP
    (offSitePositiveWindowKernel d s (angularScaledCompactWindow d χ L hL))
    (measurable_offSitePositiveWindowKernel d s _)]
  simp +contextual [offSitePositiveWindowKernel_eq_ofReal d s
    (angularScaledCompactWindow d χ L hL) (fun z => hχ (L⁻¹ • z)),
    angularScaledCompactWindow_apply]

theorem original_scaled_compactGaussian_eq_pair
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) (hL : 0 < L) (u : ℝ) :
    (∫⁻ p, compactGaussianWindowKernel d (angularScaledCompactWindow d χ L hL) u p
      ∂originalAdmissibleFactorialMeasure d P hP) =
      ∫⁻ μ, ∫⁻ x, ∫⁻ y, if x = y then 0 else
        ENNReal.ofReal (χ (L⁻¹ • x) * χ (L⁻¹ • y) *
          Real.exp (-(u * ‖y-x‖^(2:ℕ)))) ∂μ ∂μ ∂P := by
  rw [lintegral_originalAdmissibleFactorialMeasure_eq_pair_lintegral d P hP
    (compactGaussianWindowKernel d (angularScaledCompactWindow d χ L hL) u)
    (measurable_compactGaussianWindowKernel d _ u)]
  refine lintegral_congr (fun μ => lintegral_congr (fun x => lintegral_congr (fun y => ?_)))
  simp only [compactGaussianWindowKernel, angularScaledCompactWindow_apply, neg_mul,
    ENNReal.ofReal_mul (mul_nonneg (hχ (L⁻¹ • x)) (hχ (L⁻¹ • y))),
    ENNReal.ofReal_mul (hχ (L⁻¹ • x))]

theorem normalizedCompactGaussianWindowMass_tail_original
    (d : ℕ) (s : ℝ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) (hL : 0 < L) :
    normalizedCompactGaussianWindowMass d s (originalAdmissibleFactorialMeasure d P hP)
      χ L hL (Set.Ioi 1) = originalPositiveHighUFactorialWindow d s P χ L := by
  exact lintegral_congr (fun u => congrArg
    (fun v : ℝ≥0∞ => positiveTailWeight s u * ((ENNReal.ofReal (L^d))⁻¹ * v))
    (original_scaled_compactGaussian_eq_pair d P hP χ hχ L hL u))

theorem normalizedCompactGaussianWindowMass_tail_background
    (d : ℕ) (s : ℝ) (χ : C_c(Rd d, ℝ)) (L : ℝ) (hL : 0 < L) :
    normalizedCompactGaussianWindowMass d s ((volume : Measure (Rd d)).prod volume)
      χ L hL (Set.Ioi 1) = positiveHighUBackgroundWindow d s χ L := by
  simp only [normalizedCompactGaussianWindowMass, positiveHighUBackgroundWindow,
    compactGaussianWindowKernel, angularScaledCompactWindow_apply, neg_mul]

theorem originalPositiveFullWindow_finite_and_head_tail
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) (hL : 0 < L) :
    originalPositiveFullWindow d s P χ L ≠ ∞ ∧
      positiveFullBackgroundWindow d s χ L ≠ ∞ ∧
      originalPositiveFullCenteredWindow d s P χ L = gamma_s s *
        (centeredPositiveHeadWindowCost d s hs P hP χ L hL +
          ((originalPositiveHighUFactorialWindow d s P χ L).toReal -
            (positiveHighUBackgroundWindow d s χ L).toReal)) := by
  let Γ := originalAdmissibleFactorialMeasure d P hP
  let ψ := compactPositiveHeadPairTest d s hs (angularScaledCompactWindow d χ L hL)
  have hHΓ : normalizedCompactGaussianWindowMass d s Γ χ L hL (Set.Ioc 0 1) ≠ ∞ ∧
      (normalizedCompactGaussianWindowMass d s Γ χ L hL (Set.Ioc 0 1)).toReal =
        (L^d)⁻¹ * ∫ p, ψ p ∂Γ :=
    compactPositiveHeadPairTest_normalized_head_lintegral d s hs Γ χ hχ L hL
      (ψ.integrable (μ := Γ))
  have hHΔ : normalizedCompactGaussianWindowMass d s ((volume : Measure (Rd d)).prod volume)
      χ L hL (Set.Ioc 0 1) ≠ ∞ ∧
      (normalizedCompactGaussianWindowMass d s ((volume : Measure (Rd d)).prod volume)
        χ L hL (Set.Ioc 0 1)).toReal = (L^d)⁻¹ * ∫ p, ψ p ∂volume.prod volume :=
    compactPositiveHeadPairTest_normalized_head_lintegral d s hs
      ((volume : Measure (Rd d)).prod volume) χ hχ L hL (ψ.integrable (μ := volume.prod volume))
  have hTΓ := normalizedCompactGaussianWindowMass_tail_original d s P hP χ hχ L hL
  have hTΔ := normalizedCompactGaussianWindowMass_tail_background d s χ L hL
  obtain ⟨hTF, hTB⟩ := originalPositiveHighU_windows_ne_top d s hs hsd P hP hW χ hχ L hL
  have hd : 0 < d := by exact_mod_cast (lt_trans hs hsd)
  have hEΓ := normalizedCompactPositiveWindowMass_finite_and_toReal d s hs Γ χ L hL
    (original_gaussianWindow_offSite_eq d P hP (angularScaledCompactWindow d χ L hL))
    hHΓ.1 (hTΓ.trans_ne hTF)
  have hEΔ := normalizedCompactPositiveWindowMass_finite_and_toReal d s hs
    ((volume : Measure (Rd d)).prod volume) χ L hL
    (background_gaussianWindow_offSite_eq d hd (angularScaledCompactWindow d χ L hL))
    hHΔ.1 (hTΔ.trans_ne hTB)
  have heqΓ := normalizedCompactPositiveWindowMass_original d s P hP χ hχ L hL
  have heqΔ := normalizedCompactPositiveWindowMass_background d s χ hχ L hL
  refine ⟨heqΓ.symm.trans_ne hEΓ.2.1, heqΔ.symm.trans_ne hEΔ.2.1, ?_⟩
  rw [originalPositiveFullCenteredWindow, ← heqΓ, ← heqΔ, hEΓ.2.2, hEΔ.2.2,
    hHΓ.2, hHΔ.2, hTΓ, hTΔ]
  dsimp only [centeredPositiveHeadWindowCost, ψ, Γ]
  ring

theorem originalPositiveFullWindow_raw_ne_top
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (L : ℝ) (hL : 0 < L) :
    (∫⁻ μ, ∫⁻ x, ∫⁻ y, if x = y then 0 else
      ENNReal.ofReal (χ (L⁻¹ • x) * χ (L⁻¹ • y) * K_s s ‖y-x‖) ∂μ ∂μ ∂P) ≠ ∞ ∧
    (∫⁻ p : Rd d × Rd d, if p.1 = p.2 then 0 else
      ENNReal.ofReal (χ (L⁻¹ • p.1) * χ (L⁻¹ • p.2) * K_s s ‖p.2-p.1‖)
        ∂(volume : Measure (Rd d)).prod volume) ≠ ∞ := by
  have h := originalPositiveFullWindow_finite_and_head_tail d s hs hsd P hP hW χ hχ L hL
  exact ⟨(ENNReal.lt_top_of_mul_ne_top_right h.1
      (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)).ne,
    (ENNReal.lt_top_of_mul_ne_top_right h.2.1
      (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)).ne⟩

theorem positiveFullBackgroundWindow_eq_full_volume
    (d : ℕ) (hd : 0 < d) (s : ℝ) (χ : C_c(Rd d, ℝ)) (L : ℝ) :
    positiveFullBackgroundWindow d s χ L = (ENNReal.ofReal (L^d))⁻¹ *
      ∫⁻ p : Rd d × Rd d,
        ENNReal.ofReal (χ (L⁻¹ • p.1) * χ (L⁻¹ • p.2) * K_s s ‖p.2-p.1‖)
          ∂(volume : Measure (Rd d)).prod volume := by
  exact congrArg (fun v => (ENNReal.ofReal (L^d))⁻¹ * v)
    (lintegral_congr_ae ((volume_product_ae_ne d hd).mono (fun _ hp => if_neg hp)))

theorem originalPositiveFullCenteredWindow_eq_physical
    (d : ℕ) (s : ℝ) (P : ConfigurationLaw d) (χ : C_c(Rd d, ℝ))
    (L : ℝ) (hL : 0 < L) :
    originalPositiveFullCenteredWindow d s P χ L = (L^d)⁻¹ *
      ((∫⁻ μ, ∫⁻ x, ∫⁻ y, if x = y then 0 else
        ENNReal.ofReal (χ (L⁻¹ • x) * χ (L⁻¹ • y) * K_s s ‖y-x‖) ∂μ ∂μ ∂P).toReal -
        (∫⁻ p : Rd d × Rd d, if p.1 = p.2 then 0 else
          ENNReal.ofReal (χ (L⁻¹ • p.1) * χ (L⁻¹ • p.2) * K_s s ‖p.2-p.1‖)
            ∂(volume : Measure (Rd d)).prod volume).toReal) := by
  simp only [originalPositiveFullCenteredWindow, originalPositiveFullWindow,
    positiveFullBackgroundWindow, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (pow_nonneg hL.le d), mul_sub]

section GenericFullWLimit
open scoped ContDiff

theorem compactSmoothWindow_original_full_W_tendsto
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (hsm : ContDiff ℝ ∞ χ)
    (ha : 0 < compactAnchorSquareMass d χ) :
    (∀ n : ℕ, originalPositiveFullWindow d s P χ ((n : ℝ)+1) ≠ ⊤ ∧
      positiveFullBackgroundWindow d s χ ((n : ℝ)+1) ≠ ⊤) ∧
    Tendsto (fun n : ℕ => originalPositiveFullCenteredWindow d s P χ ((n : ℝ)+1))
      atTop (𝓝 (compactAnchorSquareMass d χ * (W d s P).toReal)) := by
  let L : ℕ → ℝ := fun n => (n : ℝ)+1
  have hL : ∀ n, 0 < L n :=
    fun n => add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hLinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [L, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let f : ℝ → ℝ := fun u => u ^ (s/2-1) * ((Q d P u).toReal - B d u)
  have hfinite (n : ℕ) :=
    originalPositiveFullWindow_finite_and_head_tail d s hs hsd P hP hW χ hχ (L n) (hL n)
  refine ⟨fun n => ⟨(hfinite n).1, (hfinite n).2.1⟩, ?_⟩
  have hHead := (compactSmoothWindow_centered_head_tendsto d s hs hsd P hP hW χ hχ hsm ha).2
  have hTail := originalPositiveHighU_centered_window_tendsto d s hs hsd P hP hW χ hχ L hL hLinv
  rw [positiveTail_centered_mass_eq_integral d s hs hsd P hW] at hTail
  obtain ⟨hf, hWvalue⟩ := positiveSignedGaussian_integrable_and_W_toReal d s hs hsd P hP hW
  have hsplit : (∫ u : ℝ in Set.Ioi 0, f u) =
      (∫ u : ℝ in Set.Ioc 0 1, f u) + ∫ u : ℝ in Set.Ioi 1, f u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one)]
    exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hf.mono_set Set.Ioc_subset_Ioi_self)
      (hf.mono_set (show Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 from fun _ hu =>
        lt_trans (show (0 : ℝ) < 1 from zero_lt_one) hu))
  have hlimit := ((hHead.add hTail).const_mul (gamma_s s)).congr
    (fun n => (hfinite n).2.2.symm)
  have htarget : gamma_s s * (compactAnchorSquareMass d χ * (∫ u : ℝ in Set.Ioc 0 1, f u) +
      compactAnchorSquareMass d χ * (∫ u : ℝ in Set.Ioi 1, f u)) =
      compactAnchorSquareMass d χ * (W d s P).toReal := by
    rw [← mul_add, mul_left_comm, ← hsplit, hWvalue]
  exact htarget ▸ hlimit

end GenericFullWLimit

end Riesz.Stationary
