import Riesz.Stationary.FactorialCollisionAnchor
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Riesz.Configuration.DisplacedLawMoments
import Riesz.Configuration.FactorialPairMeasure
import Riesz.Stationary.HeatSpectrumCompatibility
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Ring.GeomSum

/-!
Actual Gaussian displacement of a stationary counting law, retaining coincident
unequal labels. The original energy of the displaced simple law approximates
finite factorial energy from above, and is strictly smaller when the input law
is not almost surely simple. All NN finiteness guards precede real identities.
-/
noncomputable section
open MeasureTheory Filter RieszShowcase Riesz.Configuration
open scoped ENNReal Topology Classical CompactlySupported
namespace Riesz.Stationary

private theorem mark_pair_ae_ne
    (d : ℕ) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (a b : Rd d) :
    ∀ᵐ q ∂ν.prod ν, a + q.1 ≠ b + q.2 := by
  have hC : MeasurableSet {q : Rd d × Rd d | q.2 = a + q.1 - b} :=
    measurableSet_eq_fun measurable_snd
      ((measurable_const.add measurable_fst).sub_const b)
  have hnull : (ν.prod ν) {q : Rd d × Rd d | q.2 = a + q.1 - b} = 0 :=
    (Measure.measure_prod_null hC).2 (Eventually.of_forall (fun u =>
      (show ν {a + u - b} = 0 from measure_singleton _)))
  have hae : ∀ᵐ q ∂ν.prod ν, q.2 ≠ a + q.1 - b := by
    simpa only [ae_iff, not_not] using hnull
  exact hae.mono (fun q hq heq =>
    hq ((eq_sub_iff_add_eq).2 ((add_comm q.2 b).trans heq.symm)))

private theorem measurable_pair_mark_average
    (d : ℕ) (ν : Measure (Rd d)) [SFinite ν]
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    Measurable (fun p : Rd d × Rd d =>
      ∫⁻ z, ∫⁻ w, k (p.1 + z, p.2 + w) ∂ν ∂ν) := by
  have h : Measurable (fun q : ((Rd d × Rd d) × Rd d) × Rd d =>
      k (q.1.1.1 + q.1.2, q.1.1.2 + q.2)) :=
    hk.comp
      ((((measurable_fst.comp measurable_fst).comp measurable_fst).add
        (measurable_snd.comp measurable_fst)).prodMk
        (((measurable_snd.comp measurable_fst).comp measurable_fst).add measurable_snd))
  exact h.lintegral_prod_right'.lintegral_prod_right'

private theorem offsite_mark_average_eq
    (d : ℕ) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (u : ℝ) (a b : Rd d) :
    (∫⁻ z, ∫⁻ w, offSiteAnchoredGaussianKernel d u (a + z,b + w) ∂ν ∂ν) =
      ∫⁻ z, ∫⁻ w, anchoredGaussianKernel d u (a + z,b + w) ∂ν ∂ν := by
  have hshift : Measurable (fun q : Rd d × Rd d => (a + q.1,b + q.2)) :=
    (measurable_const.add measurable_fst).prodMk
      (measurable_const.add measurable_snd)
  change (∫⁻ z, ∫⁻ w,
      (offSiteAnchoredGaussianKernel d u ∘ (fun q => (a + q.1,b + q.2))) (z,w) ∂ν ∂ν) =
    ∫⁻ z, ∫⁻ w,
      (anchoredGaussianKernel d u ∘ (fun q => (a + q.1,b + q.2))) (z,w) ∂ν ∂ν
  rw [← lintegral_prod _
      ((measurable_offSiteAnchoredGaussianKernel d u).comp hshift).aemeasurable,
    ← lintegral_prod _
      ((measurable_anchoredGaussianKernel d u).comp hshift).aemeasurable]
  exact lintegral_congr_ae ((mark_pair_ae_ne d ν a b).mono
    (fun q hq => by simp only [Function.comp_apply, offSiteAnchoredGaussianKernel, if_neg hq]))

private theorem displacedAmbient_isSFinite
    (d : ℕ) (p : CountingConfiguration d × DisplacementMarks d) :
    SFinite (displacedAmbient d p) := by
  let atoms : (ℕ × ℕ) → Measure (Rd d) := fun i =>
    if i.2 < countingShellCount d i.1 p.1 then
      Measure.dirac (countingShellPosition d i.1 i.2 p.1 + p.2 i) else 0
  have hrepr : displacedAmbient d p = Measure.sum atoms := rfl
  letI (i : ℕ × ℕ) : SFinite (atoms i) := by
    dsimp [atoms]
    split_ifs <;> infer_instance
  rw [hrepr]
  infer_instance

/-- Actual original-Q Campbell after independent heat marking, retaining input multiplicities. -/
theorem Q_displacedLaw_eq_factorial_mark_average
    (d : ℕ) (hd : 0 < d) (t : ℝ) (ht : 0 < t)
    (P : Measure (CountingConfiguration d)) [IsProbabilityMeasure P]
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d)))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (u : ℝ) :
    Q d (displacedLaw d t P) u =
      ∫⁻ p, ∫⁻ z, ∫⁻ w,
        anchoredGaussianKernel d u (p.1 + z,p.2 + w)
        ∂heatDisplacementLaw d t ∂heatDisplacementLaw d t
        ∂expectedFactorialMeasure d P hsecond := by
  let ν := heatDisplacementLaw d t
  letI : IsProbabilityMeasure ν := heatDisplacementLaw_probability d t ht
  letI : NullSingletonClass ν := heatDisplacementLaw_nullSingletonClass d hd t
  letI := heatDisplacementMarksLaw_probability d t ht
  let k := offSiteAnchoredGaussianKernel d u
  have hk : Measurable k := measurable_offSiteAnchoredGaussianKernel d u
  let H : Rd d × Rd d → ℝ≥0∞ := fun p =>
    ∫⁻ z, ∫⁻ w, anchoredGaussianKernel d u (p.1 + z,p.2 + w) ∂ν ∂ν
  have hH : Measurable H := measurable_pair_mark_average d ν _
    (measurable_anchoredGaussianKernel d u)
  have hAE := aemeasurable_pair_lintegral_of_simple d (displacedLaw d t P)
    (displacedLaw_ae_simple d hd t ht P hmean) k hk
  have hjoint : AEMeasurable
      (fun p : CountingConfiguration d × DisplacementMarks d =>
        ∫⁻ a, ∫⁻ b, k (a,b) ∂displacedAmbient d p ∂displacedAmbient d p)
      (P.prod (heatDisplacementMarksLaw d t)) :=
    hAE.comp_measurable (measurable_displacedAmbient d)
  have hdiag (a : Rd d) : (∫⁻ z, k (a + z,a + z) ∂ν) = 0 := by
    simp [k, offSiteAnchoredGaussianKernel]
  calc
    _ = ∫⁻ p : CountingConfiguration d × DisplacementMarks d,
        ∫⁻ a, ∫⁻ b, k (a,b) ∂displacedAmbient d p ∂displacedAmbient d p
        ∂P.prod (heatDisplacementMarksLaw d t) := by
      simp_rw [Q, anchored_offSite_pair_lintegral]
      rw [displacedLaw, lintegral_map' hAE (measurable_displacedAmbient d).aemeasurable]
    _ = ∫⁻ μ, ∫⁻ z, ∫⁻ p, k p ∂(displacedAmbient d (μ,z)).prod
        (displacedAmbient d (μ,z)) ∂heatDisplacementMarksLaw d t ∂P := by
      rw [lintegral_prod _ hjoint]
      refine lintegral_congr (fun μ => lintegral_congr (fun z => ?_))
      letI := displacedAmbient_isSFinite d (μ,z)
      exact (lintegral_prod k hk.aemeasurable).symm
    _ = ∫⁻ μ, ∑' ij : (ℕ × ℕ) × (ℕ × ℕ),
        if ij.1.2 < countingShellCount d ij.1.1 μ ∧
            ij.2.2 < countingShellCount d ij.2.1 μ ∧ ij.1 ≠ ij.2 then
          H (countingShellPosition d ij.1.1 ij.1.2 μ,
            countingShellPosition d ij.2.1 ij.2.2 μ) else 0 ∂P := by
      refine lintegral_congr (fun μ => ?_)
      rw [lintegral_displacedAmbient_prod_marks d t ht μ k hk]
      refine tsum_congr (fun ij => ?_)
      by_cases hij : ij.1 = ij.2 <;>
        by_cases hi : ij.1.2 < countingShellCount d ij.1.1 μ <;>
          by_cases hj : ij.2.2 < countingShellCount d ij.2.1 μ <;>
            simp [hi, hj, hij, H, k, ν,
              offSiteAnchoredGaussianKernel]
      exact offsite_mark_average_eq d (heatDisplacementLaw d t) u
        (countingShellPosition d ij.1.1 ij.1.2 μ)
        (countingShellPosition d ij.2.1 ij.2.2 μ)
    _ = _ := (lintegral_expectedFactorialMeasure_eq_unequalLabel_tsum
      d P hsecond H hH).symm

private theorem lintegral_heat_mark_difference
    (d : ℕ) (t : ℝ) (ht : 0 < t)
    (f : Rd d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, ∫⁻ w, f (w - z) ∂heatDisplacementLaw d t ∂heatDisplacementLaw d t) =
      ∫⁻ r, ENNReal.ofReal (originalHeatGaussian d (2*t) r) * f r ∂volume := by
  let ν := heatDisplacementLaw d t
  letI : IsProbabilityMeasure ν := heatDisplacementLaw_probability d t ht
  let G : Rd d → ℝ≥0∞ := fun z => ENNReal.ofReal (originalHeatGaussian d t z)
  have hG : Measurable G := (continuous_originalHeatGaussian d t).measurable.ennreal_ofReal
  have houter : Measurable (fun z => ∫⁻ w, f (w-z) ∂ν) :=
    (hf.comp (measurable_snd.sub measurable_fst)).lintegral_prod_right'
  have hconvolution (r : Rd d) :
      (∫⁻ z, G z * G (r+z) ∂volume) =
        ENNReal.ofReal (originalHeatGaussian d (2*t) r) := by
    have hpoint (z : Rd d) : G z * G (r+z) =
        ENNReal.ofReal (originalHeatGaussian d t ((0 : Rd d)-z)) *
          ENNReal.ofReal (originalHeatGaussian d t (-r-z)) := by
      rw [show -r-z = -(r+z) by abel, zero_sub, originalHeatGaussian_neg,
        originalHeatGaussian_neg]
    exact (lintegral_congr hpoint).trans (by
      simpa only [← two_mul, sub_zero, originalHeatGaussian_neg] using
        lintegral_originalHeatGaussian_mul d t t ht ht (0 : Rd d) (-r))
  calc
    _ = ∫⁻ z, G z * (∫⁻ w, G w * f (w-z) ∂volume) ∂volume := by
      change (∫⁻ z, ∫⁻ w, f (w-z) ∂ν ∂volume.withDensity G) = _
      rw [lintegral_withDensity_eq_lintegral_mul volume hG houter]
      refine lintegral_congr (fun z => congrArg (fun a => G z*a) ?_)
      exact lintegral_withDensity_eq_lintegral_mul volume hG
        (hf.comp (measurable_id.sub_const z))
    _ = ∫⁻ z, ∫⁻ w, G z * G w * f (w-z) ∂volume ∂volume :=
      lintegral_congr (fun z => by
        simpa only [Pi.mul_apply, Function.comp_apply, id_eq, mul_assoc] using
          (lintegral_const_mul (G z) (hG.mul (hf.comp (measurable_id.sub_const z)))).symm)
    _ = ∫⁻ z, ∫⁻ r, G z * G (r+z) * f r ∂volume ∂volume :=
      lintegral_congr (fun z => by
        simpa only [add_sub_cancel_right] using
          (lintegral_add_right_eq_self (μ := (volume : Measure (Rd d)))
            (fun w => G z*G w*f (w-z)) z).symm)
    _ = ∫⁻ r, ∫⁻ z, G z * G (r+z) * f r ∂volume ∂volume :=
      lintegral_lintegral_swap
        (((hG.comp measurable_fst).mul
          (hG.comp (measurable_snd.add measurable_fst))).mul
            (hf.comp measurable_snd)).aemeasurable
    _ = _ := lintegral_congr (fun r => by
      have hGG : Measurable (fun z : Rd d => G z * G (r+z)) :=
        hG.mul (hG.comp (measurable_const.add measurable_id))
      rw [lintegral_mul_const (f r) hGG, hconvolution r])

private theorem heat_mark_gaussian_constant
    (d : ℕ) (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
    (4*Real.pi*(2*t)) ^ (-((d : ℝ)/2)) * B d (1/(4*(2*t))+u) =
      (1+8*t*u) ^ (-((d : ℝ)/2)) := by
  have hα : 0 < 1/(4*(2*t)) := by positivity
  have hden : 0 < 1+8*t*u := by positivity
  have hbase : (Real.pi/(1/(4*(2*t))+u))/(Real.pi/(1/(4*(2*t)))) =
      (1+8*t*u)⁻¹ := by
    field_simp [ht.ne', Real.pi_ne_zero, (add_pos hα hu).ne', hden.ne']
    ring
  rw [heatGaussian_constant_eq_inv_B d (2*t) (by positivity), inv_mul_eq_div,
    B, B, ← Real.div_rpow (div_pos Real.pi_pos (add_pos hα hu)).le
      (div_pos Real.pi_pos hα).le, hbase,
    Real.inv_rpow hden.le, Real.rpow_neg hden.le]

private theorem lintegral_heat_marks_gaussian
    (d : ℕ) (t u : ℝ) (ht : 0 < t) (hu : 0 < u) (b : Rd d) :
    (∫⁻ z, ∫⁻ w, ENNReal.ofReal (Real.exp (-(u*‖b+w-z‖^2)))
      ∂heatDisplacementLaw d t ∂heatDisplacementLaw d t) =
      ENNReal.ofReal ((1+8*t*u)^(-((d : ℝ)/2))) *
        ENNReal.ofReal (Real.exp (-((u/(1+8*t*u))*‖b‖^2))) := by
  let α : ℝ := 1/(4*(2*t))
  let κ : ℝ := (4*Real.pi*(2*t))^(-((d : ℝ)/2))
  have hα : 0 < α := by dsimp [α]; positivity
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hparam : α*u/(α+u) = u/(1+8*t*u) := by
    dsimp [α]
    field_simp [ht.ne', (add_pos hα hu).ne', (show (1+8*t*u) ≠ 0 by positivity)]
    ring
  have hpoint (r : Rd d) :
      ENNReal.ofReal (originalHeatGaussian d (2*t) r) *
          ENNReal.ofReal (Real.exp (-(u*‖b+r‖^2))) =
        ENNReal.ofReal κ *
          (ENNReal.ofReal (Real.exp (-α*‖(0 : Rd d)-r‖^2)) *
            ENNReal.ofReal (Real.exp (-u*‖(-b)-r‖^2))) := by
    have hn : ‖(-b)-r‖ = ‖b+r‖ := by rw [show (-b)-r = -(b+r) by abel, norm_neg]
    have he : -(1/(4*(2*t)))*‖r‖^2 = -α*‖(0 : Rd d)-r‖^2 := by
      simp only [zero_sub, norm_neg, α]
    change ENNReal.ofReal (κ*Real.exp (-(1/(4*(2*t)))*‖r‖^2)) * _ = _
    rw [ENNReal.ofReal_mul hκ, he, hn, ← neg_mul, mul_assoc]
  calc
    _ = ∫⁻ r, ENNReal.ofReal (originalHeatGaussian d (2*t) r) *
        ENNReal.ofReal (Real.exp (-(u*‖b+r‖^2))) ∂volume := by
      have hf : Measurable (fun r : Rd d =>
          ENNReal.ofReal (Real.exp (-(u*‖b+r‖^2)))) := by fun_prop
      simpa only [add_sub_assoc] using lintegral_heat_mark_difference d t ht _ hf
    _ = ENNReal.ofReal κ *
        (∫⁻ r, ENNReal.ofReal (Real.exp (-α*‖(0 : Rd d)-r‖^2)) *
          ENNReal.ofReal (Real.exp (-u*‖(-b)-r‖^2)) ∂volume) :=
      (lintegral_congr hpoint).trans (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
    _ = _ := by
      rw [lintegral_unequal_rawGaussians d α u hα hu (0 : Rd d) (-b), hparam]
      simp only [zero_sub, norm_neg]
      rw [mul_left_comm (ENNReal.ofReal κ),
        ← ENNReal.ofReal_mul hκ, heat_mark_gaussian_constant d t u ht hu]
      rw [neg_mul, mul_comm]

theorem Q_displacedLaw_eq_factorialQ
    (d : ℕ) (hd : 0 < d) (t : ℝ) (ht : 0 < t)
    (P : Measure (CountingConfiguration d)) [IsProbabilityMeasure P]
    (hstationary : IsStationary d (P.map Subtype.val))
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d)))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (u : ℝ) (hu : 0 < u) :
    Q d (displacedLaw d t P) u =
      ENNReal.ofReal ((1+8*t*u)^(-((d : ℝ)/2))) *
        factorialQ d P hsecond (u/(1+8*t*u)) := by
  let Γ := expectedFactorialMeasure d P hsecond
  let ν := heatDisplacementLaw d t
  letI : IsProbabilityMeasure ν := heatDisplacementLaw_probability d t ht
  let K : (Rd d × Rd d) × (Rd d × Rd d) → ℝ≥0∞ := fun q =>
    anchoredGaussianKernel d u (q.1.1+q.2.1,q.1.2+q.2.2)
  let L : (Rd d × Rd d) × (Rd d × Rd d) → ℝ≥0∞ := fun q =>
    if q.1.1 ∈ cube d 1 then
      ENNReal.ofReal (Real.exp (-(u*‖q.1.2-q.1.1+q.2.2-q.2.1‖^2))) else 0
  have hK : Measurable K := (measurable_anchoredGaussianKernel d u).comp
    (((measurable_fst.comp measurable_fst).add
      (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).add (measurable_snd.comp measurable_snd)))
  have hL : Measurable L := Measurable.ite
    ((Riesz.Negative.measurableSet_cube d 1).preimage
      (measurable_fst.comp measurable_fst)) (by fun_prop) measurable_const
  have hfixed (q : Rd d × Rd d) :
      (∫⁻ p, K (p,q) ∂Γ) = ∫⁻ p, L (p,q) ∂Γ := by
    let T : Rd d × Rd d → Rd d × Rd d := fun p => (q.1+p.1,q.1+p.2)
    have hT : Measurable T :=
      (measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd)
    have hpoint (p : Rd d × Rd d) : K (p,q) = L (T p,q) := by
      dsimp [K,L,T,anchoredGaussianKernel]
      rw [add_comm q.1 p.1,
        show (q.1+p.2)-(p.1+q.1)+q.2-q.1 = (p.2+q.2)-(p.1+q.1) by abel]
    exact (lintegral_congr hpoint).trans
      ((lintegral_map (hL.comp measurable_prodMk_right) hT).symm.trans (by
        rw [expectedFactorialMeasure_stationary_allCounting d P hsecond hstationary q.1]
        rfl))
  calc
    _ = ∫⁻ p, ∫⁻ q, K (p,q) ∂ν.prod ν ∂Γ :=
      (Q_displacedLaw_eq_factorial_mark_average d hd t ht P hmean hsecond u).trans
        (lintegral_congr (fun p =>
          (lintegral_prod _ (hK.comp measurable_prodMk_left).aemeasurable).symm))
    _ = ∫⁻ q, ∫⁻ p, K (p,q) ∂Γ ∂ν.prod ν := lintegral_lintegral_swap hK.aemeasurable
    _ = ∫⁻ q, ∫⁻ p, L (p,q) ∂Γ ∂ν.prod ν := lintegral_congr hfixed
    _ = ∫⁻ p, ∫⁻ q, L (p,q) ∂ν.prod ν ∂Γ :=
      (lintegral_lintegral_swap hL.aemeasurable).symm
    _ = ∫⁻ p, ENNReal.ofReal ((1+8*t*u)^(-((d : ℝ)/2))) *
        anchoredGaussianKernel d (u/(1+8*t*u)) p ∂Γ := by
      refine lintegral_congr (fun p => ?_)
      by_cases hp : p.1 ∈ cube d 1
      · rw [lintegral_prod (fun q : Rd d × Rd d => L (p,q))
          (hL.comp measurable_prodMk_left).aemeasurable]
        simpa only [L, if_pos hp, anchoredGaussianKernel, if_pos hp] using
          lintegral_heat_marks_gaussian d t u ht hu (p.2-p.1)
      · simp [L, hp, anchoredGaussianKernel]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem Q_displacedLaw_ne_top_of_factorialW_ne_top
    (d : ℕ) (hd : 0 < d) (s : ℝ) (hs_lower : -2 < s)
    (t : ℝ) (ht : 0 < t)
    (P : Measure (CountingConfiguration d)) [IsProbabilityMeasure P]
    (hstationary : IsStationary d (P.map Subtype.val))
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d)))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hW : factorialW d s P hsecond ≠ ⊤) (u : ℝ) (hu : 0 < u) :
    Q d (displacedLaw d t P) u ≠ ∞ := by
  rw [Q_displacedLaw_eq_factorialQ d hd t ht P hstationary hmean hsecond u hu]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (factorialQ_ne_top_of_factorialW_ne_top d s hs_lower P hsecond hW
      (u/(1+8*t*u)) (div_pos hu (by positivity)))

private theorem displaced_background_identity
    (d : ℕ) (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
    (1+8*t*u)^(-((d : ℝ)/2)) * B d (u/(1+8*t*u)) = B d u := by
  have hden : 0 < 1+8*t*u := by positivity
  have hbase : Real.pi/(u/(1+8*t*u)) = (Real.pi/u)*(1+8*t*u) := by
    field_simp [hu.ne', hden.ne']
  rw [B, B, hbase, Real.mul_rpow (div_pos Real.pi_pos hu).le hden.le,
    Real.rpow_neg hden.le]
  field_simp [(Real.rpow_pos_of_pos hden ((d : ℝ)/2)).ne']

private theorem clipped_affine_comparison (Q b a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    max (a*Q+1-a*b) 0 ≤ a*max (Q+1-b) 0+1-a := by
  apply max_le
  · calc
      a*Q+1-a*b = a*(Q+1-b)+1-a := by ring
      _ ≤ a*max (Q+1-b) 0+1-a := by
        nlinarith [mul_le_mul_of_nonneg_left (le_max_left (Q+1-b) 0) ha0]
  · nlinarith [mul_nonneg ha0 (le_max_right (Q+1-b) 0)]


private theorem displaced_retained_mellin_lintegral_le
    (D r h : ℝ) (hh : 0 < h) (hβ : 0 ≤ D+r-1)
    (F : ℝ → ℝ≥0∞) :
    (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u^(-r-1)) *
      ENNReal.ofReal ((1+h*u)^(-D)) * F (u/(1+h*u))) ≤
      ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (v^(-r-1)) * F v := by
  let S : Set ℝ := Set.Ioo 0 (1/h)
  let f : ℝ → ℝ := fun v => v/(1-h*v)
  let f' : ℝ → ℝ := fun v => ((1-h*v)^2)⁻¹
  have hbase (v : ℝ) (hv : v ∈ S) : 0 < 1-h*v := by
    have hvh : v*h < 1 := (lt_div_iff₀ hh).mp hv.2
    nlinarith
  have hden (v : ℝ) (hv : v ∈ S) : 1+h*f v = 1/(1-h*v) := by
    dsimp [f]
    field_simp [(hbase v hv).ne']
    ring
  have hback (v : ℝ) (hv : v ∈ S) : f v/(1+h*f v) = v := by
    rw [hden v hv]
    dsimp [f]
    field_simp [(hbase v hv).ne']
    exact mul_div_cancel_right₀ v (by nlinarith [hbase v hv])
  have himage : f '' S = Set.Ioi (0 : ℝ) := by
    ext u
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact div_pos hv.1 (hbase v hv)
    · intro hu
      have hupos : 0 < u := hu
      have hdu : 0 < 1+h*u := by positivity
      refine ⟨u/(1+h*u), ⟨div_pos hupos hdu, ?_⟩, ?_⟩
      · apply (div_lt_div_iff₀ hdu hh).2
        nlinarith
      · dsimp [f]
        field_simp [hdu.ne', hh.ne']
        ring
  have hinj : Set.InjOn f S := by
    intro v hv w hw hvw
    have heq := congrArg (fun u : ℝ => u/(1+h*u)) hvw
    simpa only [hback v hv, hback w hw] using heq
  have hderiv (v : ℝ) (hv : v ∈ S) : HasDerivWithinAt f (f' v) S v := by
    apply HasDerivWithinAt.congr_deriv (((hasDerivAt_id v).div
      ((hasDerivAt_const v 1).sub ((hasDerivAt_id v).const_mul h))
      (hbase v hv).ne').hasDerivWithinAt)
    dsimp [f']
    ring
  have hcoef (v : ℝ) (hv : v ∈ S) :
      |f' v| * (f v)^(-r-1) * (1+h*f v)^(-D) =
        v^(-r-1)*(1-h*v)^(D+r-1) := by
    have ha : 0 < 1-h*v := hbase v hv
    have hatt : (1+h*f v)^(-D) = (1-h*v)^D := by
      rw [hden v hv, one_div, Real.inv_rpow ha.le,
        Real.rpow_neg ha.le D, inv_inv]
    have hp : ((1-h*v)^D / (1-h*v)^(-r-1)) / (1-h*v)^2 =
        (1-h*v)^(D+r-1) := by
      rw [← Real.rpow_sub ha D (-r-1), ← Real.rpow_two (1-h*v),
        ← Real.rpow_sub ha (D-(-r-1)) 2]
      congr 1
      ring
    rw [hatt, abs_of_nonneg (by dsimp [f']; positivity)]
    dsimp [f,f']
    rw [Real.div_rpow hv.1.le ha.le, ← hp]
    ring
  let G : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (u^(-r-1)) *
    ENNReal.ofReal ((1+h*u)^(-D)) * F (u/(1+h*u))
  have hpoint (v : ℝ) (hv : v ∈ S) :
      ENNReal.ofReal (|f' v|) * G (f v) =
        ENNReal.ofReal (v^(-r-1)) *
          ENNReal.ofReal ((1-h*v)^(D+r-1)) * F v := by
    have hfpos : 0 < f v := div_pos hv.1 (hbase v hv)
    calc
      _ = ENNReal.ofReal (|f' v| * (f v)^(-r-1) * (1+h*f v)^(-D)) * F v := by
        dsimp [G]
        rw [hback v hv, ENNReal.ofReal_mul
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hfpos.le _)),
          ENNReal.ofReal_mul (abs_nonneg _)]
        ac_rfl
      _ = _ := by rw [hcoef v hv, ENNReal.ofReal_mul (Real.rpow_nonneg hv.1.le _)]
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := S) (f := f) (f' := f') measurableSet_Ioo hderiv hinj G
  calc
    _ = ∫⁻ v in S, ENNReal.ofReal (|f' v|) * G (f v) := by
      simpa only [himage] using hchange
    _ = ∫⁻ v in S, ENNReal.ofReal (v^(-r-1)) *
        ENNReal.ofReal ((1-h*v)^(D+r-1)) * F v :=
      setLIntegral_congr_fun measurableSet_Ioo hpoint
    _ ≤ ∫⁻ v in S, ENNReal.ofReal (v^(-r-1)) * F v := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro v hv
      have ha1 : 1-h*v ≤ 1 := by nlinarith [hh, hv.1]
      have hcut : ENNReal.ofReal ((1-h*v)^(D+r-1)) ≤ 1 := by
        simpa only [ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (Real.rpow_le_one (hbase v hv).le ha1 hβ)
      calc
        _ ≤ (ENNReal.ofReal (v^(-r-1))*1) * F v := by gcongr
        _ = _ := by rw [mul_one]
    _ ≤ _ := lintegral_mono_set (fun v hv => hv.1)

private theorem displaced_noise_bound
    (D h u : ℝ) (M : ℕ) (hD : 0 ≤ D) (hDM : D ≤ (M : ℝ))
    (hh : 0 ≤ h) (hu : 0 < u) :
    0 ≤ 1-(1+h*u)^(-D) ∧
      1-(1+h*u)^(-D) ≤ 1 ∧
      1-(1+h*u)^(-D) ≤ (M : ℝ)*h*u := by
  have hb : 1 ≤ 1+h*u := by nlinarith
  have hbpos : 0 < 1+h*u := lt_of_lt_of_le zero_lt_one hb
  let a : ℝ := 1/(1+h*u)
  have ha0 : 0 < a := div_pos zero_lt_one hbpos
  have ha1 : a ≤ 1 := (div_le_one hbpos).2 hb
  have haD : a^D = (1+h*u)^(-D) := by
    dsimp [a]
    rw [one_div, Real.inv_rpow hbpos.le, Real.rpow_neg hbpos.le]
  have hpow : a^M ≤ a^D := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_ge ha0 ha1 hDM
  have hgeom : 1-a^M ≤ (M : ℝ)*(1-a) := by
    calc
      _ = (∑ k ∈ Finset.range M, a^k)*(1-a) := (geom_sum_mul_neg a M).symm
      _ ≤ (∑ _k ∈ Finset.range M, (1 : ℝ))*(1-a) :=
        mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum (fun k _hk => pow_le_one₀ ha0.le ha1)) (sub_nonneg.mpr ha1)
      _ = _ := by simp
  have hsub : 1-a ≤ h*u := by
    have heq : 1-a = h*u/(1+h*u) := by
      dsimp [a]
      field_simp [hbpos.ne']
      ring
    rw [heq]
    exact div_le_self (mul_nonneg hh hu.le) hb
  have hupper : (1+h*u)^(-D) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hD)
  refine ⟨sub_nonneg.mpr hupper, ?_, ?_⟩
  · linarith [Real.rpow_nonneg hbpos.le (-D)]
  · calc
      _ = 1-a^D := by rw [haD]
      _ ≤ 1-a^M := sub_le_sub_left hpow 1
      _ ≤ (M : ℝ)*(1-a) := hgeom
      _ ≤ (M : ℝ)*(h*u) := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg M)
      _ = _ := by ring

private theorem displaced_noise_sequence_finite_and_tendsto
    (D r : ℝ) (hD : 0 ≤ D) (hr0 : 0 < r) (hr1 : r < 1) :
    (∀ n : ℕ,
      (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (u^(-r-1)*(1-(1+(1/((n : ℝ)+1))*u)^(-D)))) ≠ ∞) ∧
    Tendsto (fun n : ℕ =>
      ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (u^(-r-1)*(1-(1+(1/((n : ℝ)+1))*u)^(-D)))) atTop (𝓝 0) := by
  obtain ⟨M,hDM⟩ := exists_nat_ge D
  let h : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  let F : ℕ → ℝ → ℝ≥0∞ := fun n u => ENNReal.ofReal
    (u^(-r-1)*(1-(1+h n*u)^(-D)))
  let b : ℝ → ℝ := fun u => if u ≤ 1 then (M : ℝ)*u^(-r) else u^(-r-1)
  have hhpos (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have hh1 (n : ℕ) : h n ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ)+1)).2
    linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hhlim : Tendsto h atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hbmeas : Measurable b := Measurable.ite
    (measurableSet_le measurable_id measurable_const)
    (measurable_const.mul (measurable_id.pow_const (-r)))
    (measurable_id.pow_const (-r-1))
  have hleftpow : IntegrableOn (fun u : ℝ => u^(-r)) (Set.Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  have hleft : IntegrableOn b (Set.Ioc 0 1) :=
    IntegrableOn.congr_fun (hleftpow.const_mul (M : ℝ))
      (fun u hu => by simp only [b, if_pos hu.2]) measurableSet_Ioc
  have hright : IntegrableOn b (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -r-1 < -1) zero_lt_one).congr_fun
      (fun u hu => by simp only [b, if_neg (not_le_of_gt (show (1 : ℝ) < u from hu))])
      measurableSet_Ioi
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext u
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h0,_h1⟩ | h1)
      · exact h0
      · exact zero_lt_one.trans h1
    · intro h0
      rcases le_or_gt u 1 with h1 | h1
      · exact Or.inl ⟨h0,h1⟩
      · exact Or.inr h1
  have hbi : IntegrableOn b (Set.Ioi 0) := hunion ▸ hleft.union hright
  have hbnonneg : ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ b u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := (show (0 : ℝ) < u from hu).le
    dsimp [b]
    split_ifs <;> positivity
  have hbfinite : (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (b u)) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hbmeas.aestronglyMeasurable hbnonneg).2 hbi
  have hFmeas (n : ℕ) : Measurable (F n) :=
    ((measurable_id.pow_const (-r-1)).mul
      (measurable_const.sub
        ((measurable_const.add (measurable_const.mul measurable_id)).pow_const (-D)))).ennreal_ofReal
  have hbound (n : ℕ) : F n ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun u => ENNReal.ofReal (b u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨_h0,h1,hlinear⟩ := displaced_noise_bound D (h n) u M hD hDM (hhpos n).le hu
    have hweight : 0 ≤ u^(-r-1) := Real.rpow_nonneg hu.le _
    dsimp [F,b]
    split_ifs with hu1
    · have hlinear' : 1-(1+h n*u)^(-D) ≤ (M : ℝ)*u :=
        hlinear.trans (by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hh1 n) (Nat.cast_nonneg M)) hu.le))
      calc
        _ ≤ u^(-r-1)*((M : ℝ)*u) := mul_le_mul_of_nonneg_left hlinear' hweight
        _ = (M : ℝ)*u^(-r) := by
          have hpow : u^(-r) = u^(-r-1)*u := by
            simpa only [show -r-1+1 = -r by ring] using
              Real.rpow_add_one (ne_of_gt (show (0 : ℝ) < u from hu)) (-r-1)
          rw [hpow]
          ring
    · exact (mul_le_mul_of_nonneg_left h1 hweight).trans_eq (mul_one _)
  have hlim : ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Tendsto (fun n => F n u) atTop (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _hu
    have hbase : Tendsto (fun n => 1+h n*u) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add (hhlim.mul_const u)
    have hpow := hbase.rpow_const (p := -D) (Or.inl one_ne_zero)
    have hreal : Tendsto (fun n => u^(-r-1)*(1-(1+h n*u)^(-D))) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Real.one_rpow, sub_self, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => u^(-r-1)) atTop (𝓝 (u^(-r-1)))).mul
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ))).sub hpow)
    simpa only [F, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal
  refine ⟨?_, ?_⟩
  · intro n
    exact ne_top_of_le_ne_top hbfinite (lintegral_mono_ae (hbound n))
  · simpa only [F, lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence (fun u => ENNReal.ofReal (b u))
        hFmeas hbound hbfinite hlim

private theorem factorial_remainder_add_correction_truncated
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ)))^2 ∂P) < ∞)
    (u : ℝ) (hQ : factorialQ d P hsecond u ≠ ∞) :
    ENNReal.ofReal (gaussianCorrection d u) + factorialGaussianRemainder d P hsecond u =
      ENNReal.ofReal (max ((factorialQ d P hsecond u).toReal+1-B d u) 0) := by
  have hrem : factorialGaussianRemainder d P hsecond u =
      ENNReal.ofReal ((factorialQ d P hsecond u).toReal-max (B d u-1) 0) := by
    unfold factorialGaussianRemainder
    conv_lhs => rw [← ENNReal.ofReal_toReal hQ]
    exact (ENNReal.ofReal_sub _ (le_max_right (B d u-1) 0)).symm
  have hmax : ENNReal.ofReal ((factorialQ d P hsecond u).toReal-max (B d u-1) 0) =
      ENNReal.ofReal (max ((factorialQ d P hsecond u).toReal-max (B d u-1) 0) 0) := by simp
  rw [hrem,hmax,gaussianCorrection,
    ← ENNReal.ofReal_add (le_max_right (1-B d u) 0)
      (le_max_right ((factorialQ d P hsecond u).toReal-max (B d u-1) 0) 0)]
  congr 1
  have hq : 0 ≤ (factorialQ d P hsecond u).toReal := ENNReal.toReal_nonneg
  grind

theorem factorialW_eq_weighted_truncated_profile_neg
    (d : ℕ) (s : ℝ) (hd : 2 ≤ d) (hs_lower : -2 < s) (hs_neg : s < 0)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ)))^2 ∂P) < ∞)
    (hW : factorialW d s P hsecond ≠ ⊤) :
    factorialW d s P hsecond =
      ((ENNReal.ofReal (gamma_s s) *
        ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u^(s/2-1)) *
          ENNReal.ofReal (max ((factorialQ d P hsecond u).toReal+1-B d u) 0)) : ℝ≥0∞) := by
  have hIntegral :
      (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u^(s/2-1)) *
        ENNReal.ofReal (gaussianCorrection d u)) +
      (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u^(s/2-1)) *
        factorialGaussianRemainder d P hsecond u) =
      ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u^(s/2-1)) *
        ENNReal.ofReal (max ((factorialQ d P hsecond u).toReal+1-B d u) 0) := by
    have hmeas : Measurable (fun u : ℝ => ENNReal.ofReal (u^(s/2-1)) *
        ENNReal.ofReal (gaussianCorrection d u)) :=
      (measurable_id.pow_const _).ennreal_ofReal.mul
        (gaussianCorrection_measurable d).ennreal_ofReal
    rw [← lintegral_add_left hmeas]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [← mul_add, factorial_remainder_add_correction_truncated d P hsecond u
      (factorialQ_ne_top_of_factorialW_ne_top d s hs_lower P hsecond hW u hu)]
  have hc0 : 0 ≤ c0 d s :=
    (c0_pos_of_neg d s hd hs_lower (hs_neg.trans_le (Nat.cast_nonneg d)) hs_neg).le
  have hc0coe : (c0 d s : EReal) = (ENNReal.ofReal (c0 d s) : EReal) := by
    simp only [EReal.coe_ennreal_ofReal, max_eq_left hc0]
  unfold factorialW
  rw [hc0coe, ← gamma_correction_lintegral_eq_c0 d s hs_lower hs_neg,
    ← EReal.coe_ennreal_add, ← mul_add, hIntegral]

private theorem displacedLaw_energy_le_factorialW_add_noise
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs_lower : -2 < s) (hs_neg : s < 0)
    (P : Measure (CountingConfiguration d)) [IsProbabilityMeasure P]
    (hstationary : IsStationary d (P.map Subtype.val))
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d)))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ)))^2 ∂P) < ∞)
    (hW : factorialW d s P hsecond ≠ ⊤)
    (h : ℝ) (hh : 0 < h)
    (hJ : (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
      (u^(s/2-1)*(1-(1+h*u)^(-((d : ℝ)/2))))) ≠ ∞) :
    W d s (displacedLaw d (h/8) P) ≠ ⊤ ∧
      W d s (displacedLaw d (h/8) P) ≤ factorialW d s P hsecond +
        ((ENNReal.ofReal (gamma_s s) *
          ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
            (u^(s/2-1)*(1-(1+h*u)^(-((d : ℝ)/2))))) : ℝ≥0∞) := by
  let t : ℝ := h/8
  let Pout : ConfigurationLaw d := displacedLaw d t P
  let γ : ℝ≥0∞ := ENNReal.ofReal (gamma_s s)
  let w : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (u^(s/2-1))
  let Fin : ℝ → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (max ((factorialQ d P hsecond u).toReal+1-B d u) 0)
  let Fout : ℝ → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (max ((Q d Pout u).toReal+1-B d u) 0)
  let Tin : ℝ≥0∞ := ∫⁻ u in Set.Ioi (0 : ℝ), w u*Fin u
  let Tout : ℝ≥0∞ := ∫⁻ u in Set.Ioi (0 : ℝ), w u*Fout u
  let J : ℝ≥0∞ := ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
    (u^(s/2-1)*(1-(1+h*u)^(-((d : ℝ)/2))))
  have ht : 0 < t := div_pos hh (by norm_num)
  have hdpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hd
  have htu : 8*t = h := by dsimp [t]; ring
  have hinput : factorialW d s P hsecond = (γ*Tin : ℝ≥0∞) :=
    factorialW_eq_weighted_truncated_profile_neg d s hd hs_lower hs_neg P hsecond hW
  have hγ0 : γ ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Riesz.Analysis.gamma_s_pos s hs_lower)
  have hTin : Tin ≠ ∞ := by
    intro htop
    apply hW
    rw [hinput,htop,ENNReal.mul_top hγ0,EReal.coe_ennreal_top]
  have hQin (u : ℝ) (hu : 0 < u) : factorialQ d P hsecond u ≠ ∞ :=
    factorialQ_ne_top_of_factorialW_ne_top d s hs_lower P hsecond hW u hu
  have hQout (u : ℝ) (hu : 0 < u) : Q d Pout u ≠ ∞ :=
    Q_displacedLaw_ne_top_of_factorialW_ne_top
      d hdpos s hs_lower t ht P hstationary hmean hsecond hW u hu
  have hQid (u : ℝ) (hu : 0 < u) :
      Q d Pout u = ENNReal.ofReal ((1+h*u)^(-((d : ℝ)/2))) *
        factorialQ d P hsecond (u/(1+h*u)) := by
    simpa only [← mul_assoc,htu] using
      Q_displacedLaw_eq_factorialQ d hdpos t ht P hstationary hmean hsecond u hu
  have hpoint (u : ℝ) (hu : 0 < u) :
      w u*Fout u ≤
        ENNReal.ofReal (u^(s/2-1)*(1-(1+h*u)^(-((d : ℝ)/2)))) +
          w u*ENNReal.ofReal ((1+h*u)^(-((d : ℝ)/2)))*Fin (u/(1+h*u)) := by
    let a : ℝ := (1+h*u)^(-((d : ℝ)/2))
    let v : ℝ := u/(1+h*u)
    have hden : 0 < 1+h*u := by positivity
    have ha0 : 0 ≤ a := Real.rpow_nonneg hden.le _
    have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
      (by nlinarith : 1 ≤ 1+h*u)
      (by linarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d])
    have hv : 0 < v := div_pos hu hden
    have _hqfinite := hQin v hv
    have _houtfinite := hQout u hu
    have hqreal : (Q d Pout u).toReal = a*(factorialQ d P hsecond v).toReal := by
      rw [hQid u hu,ENNReal.toReal_mul,ENNReal.toReal_ofReal ha0]
    have hbackground : a*B d v = B d u :=
      by simpa only [← mul_assoc,htu] using displaced_background_identity d t u ht hu
    have hreal : max ((Q d Pout u).toReal+1-B d u) 0 ≤
        a*max ((factorialQ d P hsecond v).toReal+1-B d v) 0+(1-a) := by
      rw [hqreal,← hbackground]
      simpa only [add_sub_assoc] using clipped_affine_comparison
        (factorialQ d P hsecond v).toReal (B d v) a ha0 ha1
    have hNN : Fout u ≤ ENNReal.ofReal a*Fin v+ENNReal.ofReal (1-a) := by
      calc
        _ ≤ ENNReal.ofReal
            (a*max ((factorialQ d P hsecond v).toReal+1-B d v) 0+(1-a)) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = _ := by
          rw [ENNReal.ofReal_add
            (mul_nonneg ha0 (le_max_right _ _)) (sub_nonneg.mpr ha1),
            ENNReal.ofReal_mul ha0]
    calc
      _ ≤ w u*(ENNReal.ofReal a*Fin v+ENNReal.ofReal (1-a)) :=
        mul_le_mul_right hNN (w u)
      _ = _ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _),mul_add]
        dsimp [a,v,w]
        ac_rfl
  have hnoiseMeas : Measurable (fun u : ℝ => ENNReal.ofReal
      (u^(s/2-1)*(1-(1+h*u)^(-((d : ℝ)/2))))) :=
    ((measurable_id.pow_const _).mul (measurable_const.sub
      ((measurable_const.add (measurable_const.mul measurable_id)).pow_const _))).ennreal_ofReal
  have hretained :
      (∫⁻ u in Set.Ioi (0 : ℝ), w u*
        ENNReal.ofReal ((1+h*u)^(-((d : ℝ)/2)))*Fin (u/(1+h*u))) ≤ Tin := by
    have hβ : 0 ≤ (d : ℝ)/2+(-s/2)-1 := by
      have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have he : -(-s/2)-1 = s/2-1 := by ring
    simpa only [he] using
      displaced_retained_mellin_lintegral_le ((d : ℝ)/2) (-s/2) h hh hβ Fin
  have hTout : Tout ≤ Tin+J := by
    calc
      _ ≤ ∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (u^(s/2-1)*(1-(1+h*u)^(-((d : ℝ)/2)))) +
            w u*ENNReal.ofReal ((1+h*u)^(-((d : ℝ)/2)))*Fin (u/(1+h*u)) :=
        setLIntegral_mono' measurableSet_Ioi hpoint
      _ = J + ∫⁻ u in Set.Ioi (0 : ℝ),
          w u*ENNReal.ofReal ((1+h*u)^(-((d : ℝ)/2)))*Fin (u/(1+h*u)) :=
        lintegral_add_left hnoiseMeas _
      _ ≤ J+Tin := add_le_add_right hretained J
      _ = _ := add_comm _ _
  have hToutfinite : Tout ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hTin,hJ⟩) hTout
  have hrem (u : ℝ) (hu : 0 < u) : gaussianRemainder d Pout u ≤ Fout u := by
    unfold gaussianRemainder
    rw [← ENNReal.ofReal_toReal (hQout u hu),
      ← ENNReal.ofReal_sub _ (le_max_right (B d u-1) 0)]
    apply ENNReal.ofReal_le_ofReal
    exact (by linarith [le_max_left (B d u-1) 0] :
      (Q d Pout u).toReal-max (B d u-1) 0 ≤ (Q d Pout u).toReal+1-B d u).trans
        (le_max_left _ _)
  have hIrem : (∫⁻ u in Set.Ioi (0 : ℝ), w u*gaussianRemainder d Pout u) ≠ ∞ :=
    ne_top_of_le_ne_top hToutfinite
      (setLIntegral_mono' measurableSet_Ioi (fun u hu => mul_le_mul_right (hrem u hu) (w u)))
  have hWout : W d s Pout ≠ ⊤ := by
    unfold W
    exact EReal.add_ne_top (EReal.coe_ne_top _)
      (fun htop => (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIrem)
        (EReal.coe_ennreal_eq_top_iff.mp htop))
  refine ⟨hWout, ?_⟩
  calc
    W d s Pout = (γ*Tout : ℝ≥0∞) :=
      W_eq_weighted_truncated_profile_neg d s hd hs_lower hs_neg Pout hWout
    _ ≤ (γ*(Tin+J) : ℝ≥0∞) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.mpr (mul_le_mul_right hTout γ)
    _ = (γ*Tin : ℝ≥0∞)+(γ*J : ℝ≥0∞) := by
      rw [mul_add,EReal.coe_ennreal_add]
    _ = _ := by rw [← hinput]

/-- Actual admissible simple laws approximate finite factorial energy from above. -/
theorem exists_admissible_displacedLaw_energy_le_factorialW_add
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs_lower : -2 < s) (hs_neg : s < 0)
    (P : Measure (CountingConfiguration d)) [IsProbabilityMeasure P]
    (hstationary : IsStationary d (P.map Subtype.val))
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d)))
    (hsecond : ∀ K : Set (Rd d), MeasurableSet K → Bornology.IsBounded K →
      (∫⁻ μ, (μ.val K)^2 ∂P) < ∞)
    (hW : factorialW d s P
      (fun n => hsecond (Metric.closedBall (0 : Rd d) (n : ℝ))
        measurableSet_closedBall (isCompact_closedBall (0 : Rd d) (n : ℝ)).isBounded) ≠ ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ Admissible d (displacedLaw d t P) ∧
      W d s (displacedLaw d t P) ≤ factorialW d s P
        (fun n => hsecond (Metric.closedBall (0 : Rd d) (n : ℝ))
          measurableSet_closedBall (isCompact_closedBall (0 : Rd d) (n : ℝ)).isBounded) +
          (ε : EReal) := by
  let hball : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ)))^2 ∂P) < ∞ :=
    fun n => hsecond (Metric.closedBall (0 : Rd d) (n : ℝ))
      measurableSet_closedBall (isCompact_closedBall (0 : Rd d) (n : ℝ)).isBounded
  let h : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  let J : ℕ → ℝ≥0∞ := fun n => ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
    (u^(s/2-1)*(1-(1+h n*u)^(-((d : ℝ)/2))))
  let γ : ℝ≥0∞ := ENNReal.ofReal (gamma_s s)
  have hh (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have hr0 : 0 < -s/2 := by linarith
  have hr1 : -s/2 < 1 := by linarith
  have he : -(-s/2)-1 = s/2-1 := by ring
  have hnoise : (∀ n, J n ≠ ∞) ∧ Tendsto J atTop (𝓝 0) := by
    simpa only [he] using displaced_noise_sequence_finite_and_tendsto
      ((d : ℝ)/2) (-s/2) (by positivity) hr0 hr1
  have hproduct : Tendsto (fun n => γ*J n) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hnoise.2 (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨n,hn⟩ := (hproduct.eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  have henergy := (displacedLaw_energy_le_factorialW_add_noise
    d hd s hs_lower hs_neg P hstationary hmean hball hW (h n) (hh n) (hnoise.1 n)).2
  refine ⟨h n/8, div_pos (hh n) (by norm_num),
    displacedLaw_admissible d (lt_of_lt_of_le (by decide : 0 < 2) hd)
      (h n/8) (div_pos (hh n) (by norm_num)) P hstationary hmean hsecond, ?_⟩
  have herror : ((γ*J n : ℝ≥0∞) : EReal) ≤ (ε : EReal) := by
    calc
      _ ≤ (ENNReal.ofReal ε : EReal) :=
        EReal.coe_ennreal_le_coe_ennreal_iff.mpr hn.le
      _ = _ := by rw [EReal.coe_ennreal_ofReal,max_eq_left hε.le]
  exact henergy.trans (add_le_add_right herror _)


end Riesz.Stationary

namespace Riesz.Stationary

private def displacedDeficitCutoff (β h v : ℝ) : ℝ := (max (1-h*v) 0)^β

private theorem displacedDeficitCutoff_bounds
    (β h v : ℝ) (hβ : 0 < β) (hh : 0 < h) (hv : 0 < v) :
    0 ≤ displacedDeficitCutoff β h v ∧ displacedDeficitCutoff β h v ≤ 1 := by
  have hb0 : 0 ≤ max (1-h*v) 0 := le_max_right _ _
  have hb1 : max (1-h*v) 0 ≤ 1 := max_le (by nlinarith) zero_le_one
  exact ⟨Real.rpow_nonneg hb0 _, Real.rpow_le_one hb0 hb1 hβ.le⟩

private theorem displacedDeficitCutoff_linear_bound
    (β h v : ℝ) (N : ℕ) (hβ : 0 < β) (hN : β ≤ (N : ℝ))
    (hN1 : 1 ≤ N) (hh : 0 < h) (hv : 0 < v) :
    1-displacedDeficitCutoff β h v ≤ (N : ℝ)*h*v := by
  by_cases ha : 0 < 1-h*v
  · let a : ℝ := 1-h*v
    have ha1 : a ≤ 1 := by dsimp [a]; nlinarith
    have hpow : a^N ≤ a^β := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_ge ha ha1 hN
    calc
      _ = 1-a^β := by rw [displacedDeficitCutoff,max_eq_left ha.le]
      _ ≤ 1-a^N := sub_le_sub_left hpow 1
      _ = (∑ k ∈ Finset.range N, a^k)*(1-a) := (geom_sum_mul_neg a N).symm
      _ ≤ (∑ _k ∈ Finset.range N, (1 : ℝ))*(1-a) :=
        mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum (fun k _hk => pow_le_one₀ ha.le ha1))
          (sub_nonneg.mpr ha1)
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; dsimp [a]; ring
  · have hhval : 1 ≤ h*v := by linarith
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    rw [displacedDeficitCutoff,max_eq_right (le_of_not_gt ha),Real.zero_rpow hβ.ne',sub_zero]
    calc
      (1 : ℝ) = 1*1 := by ring
      _ ≤ (N : ℝ)*(h*v) := mul_le_mul hNR hhval zero_le_one (Nat.cast_nonneg N)
      _ = _ := by ring

private theorem displaced_mellin_piece_majorant_integrable
    (r C : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    IntegrableOn (fun v : ℝ => if v ≤ 1 then C*v^(-r) else v^(-r-1))
      (Set.Ioi 0) := by
  let b : ℝ → ℝ := fun v => if v ≤ 1 then C*v^(-r) else v^(-r-1)
  have hi : IntegrableOn (fun v : ℝ => v^(-r)) (Set.Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  have hleft : IntegrableOn b (Set.Ioc 0 1) :=
    IntegrableOn.congr_fun (hi.const_mul C)
      (fun v hv => by simp only [b,if_pos hv.2]) measurableSet_Ioc
  have hright : IntegrableOn b (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -r-1 < -1) zero_lt_one).congr_fun
      (fun v hv => by simp only [b,if_neg (not_le_of_gt (show (1 : ℝ) < v from hv))])
      measurableSet_Ioi
  have hu : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext v
    simp only [Set.mem_union,Set.mem_Ioc,Set.mem_Ioi]
    constructor
    · rintro (⟨hv,_⟩ | hv)
      · exact hv
      · exact zero_lt_one.trans hv
    · intro hv
      rcases le_or_gt v 1 with h1 | h1
      · exact Or.inl ⟨hv,h1⟩
      · exact Or.inr h1
  exact hu ▸ hleft.union hright

private theorem displaced_deficit_integrable
    (β r h : ℝ) (hβ : 0 < β) (hr0 : 0 < r) (hr1 : r < 1) (hh : 0 < h) :
    IntegrableOn (fun v : ℝ => v^(-r-1)*(1-displacedDeficitCutoff β h v))
      (Set.Ioi 0) := by
  obtain ⟨N0,hN0⟩ := exists_nat_ge β
  let N : ℕ := max N0 1
  have hN : β ≤ (N : ℝ) := hN0.trans (by exact_mod_cast le_max_left N0 1)
  have hN1 : 1 ≤ N := le_max_right N0 1
  have hk : Measurable (displacedDeficitCutoff β h) := by
    change Measurable (fun v : ℝ => (max (1-h*v) 0)^β)
    exact (((measurable_const.sub (measurable_const.mul measurable_id)).max
      measurable_const).pow_const β)
  apply (displaced_mellin_piece_majorant_integrable r ((N : ℝ)*h) hr0 hr1).mono'
    (((measurable_id.pow_const (-r-1)).mul (measurable_const.sub hk)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  change ‖v^(-r-1)*(1-displacedDeficitCutoff β h v)‖ ≤ _
  have hb := displacedDeficitCutoff_bounds β h v hβ hh hv
  have hnonneg : 0 ≤ v^(-r-1)*(1-displacedDeficitCutoff β h v) :=
    mul_nonneg (Real.rpow_nonneg hv.le _) (sub_nonneg.mpr hb.2)
  rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
  split_ifs with hv1
  · calc
      _ ≤ v^(-r-1)*((N : ℝ)*h*v) := mul_le_mul_of_nonneg_left
          (displacedDeficitCutoff_linear_bound β h v N hβ hN hN1 hh hv)
          (Real.rpow_nonneg hv.le _)
      _ = ((N : ℝ)*h)*v^(-r) := by
        have hpow : v^(-r) = v^(-r-1)*v := by
          simpa only [show -r-1+1 = -r by ring] using
            Real.rpow_add_one (ne_of_gt (show (0 : ℝ) < v from hv)) (-r-1)
        rw [hpow]
        ring
  · exact (mul_le_mul_of_nonneg_left (sub_le_self 1 hb.1)
      (Real.rpow_nonneg hv.le _)).trans_eq (mul_one _)

private def displacedDeficitPrimitive (h r v : ℝ) : ℝ :=
  v^(-r)*((1-h*v)^r-1)

private theorem displacedDeficitPrimitive_hasDerivAt
    (h r : ℝ) (hh : 0 < h) {v : ℝ} (hv : v ∈ Set.Ioo 0 (1/h)) :
    HasDerivAt (displacedDeficitPrimitive h r)
      (r*v^(-r-1)*(1-(1-h*v)^(r-1))) v := by
  have ha : 0 < 1-h*v := by
    have hx := (lt_div_iff₀ hh).mp hv.2
    nlinarith
  have hb : HasDerivAt (fun x : ℝ => 1-h*x) (-h) v :=
    (hasDerivAt_const_mul h).const_sub 1
  have hvpow : v^(-r) = v^(-r-1)*v := by
    rw [Real.rpow_sub_one hv.1.ne' (-r)]
    field_simp [hv.1.ne']
  have hapow : (1-h*v)^r = (1-h*v)^(r-1)*(1-h*v) := by
    rw [Real.rpow_sub_one ha.ne' r]
    field_simp [ha.ne']
  have hraw := ((hasDerivAt_id v).rpow_const (p := -r) (Or.inl hv.1.ne')).mul
    ((hb.rpow_const (p := r) (Or.inl ha.ne')).sub_const 1)
  apply HasDerivAt.congr_deriv hraw
  dsimp only [id_eq]
  rw [hvpow,hapow]
  ring

private theorem displacedDeficitPrimitive_zero_limit
    (h r : ℝ) (hr1 : r < 1) :
    Tendsto (displacedDeficitPrimitive h r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hf : HasDerivAt (fun v : ℝ => (1-h*v)^r) (-h*r) 0 := by
    have hb : HasDerivAt (fun v : ℝ => 1-h*v) (-h) 0 :=
      (hasDerivAt_const_mul h).const_sub 1
    simpa using hb.rpow_const (p := r) (Or.inl (by norm_num))
  have hquot : Tendsto (fun v : ℝ => ((1-h*v)^r-1)/v)
      (𝓝[>] (0 : ℝ)) (𝓝 (-h*r)) := by
    simpa only [zero_add,mul_zero,sub_zero,Real.one_rpow,smul_eq_mul,
      div_eq_mul_inv,mul_comm] using hf.tendsto_slope_zero_right
  have hpower : Tendsto (fun v : ℝ => v^(1-r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hp := (Real.continuousAt_rpow_const (0 : ℝ) (1-r)
      (Or.inr (by linarith : 0 ≤ 1-r))).tendsto
    simpa only [Real.zero_rpow (by linarith : 1-r ≠ 0)] using hp.mono_left nhdsWithin_le_nhds
  have hproduct : Tendsto (fun v : ℝ => v^(1-r)*(((1-h*v)^r-1)/v))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hpower.mul hquot
  apply Filter.Tendsto.congr' (h := hproduct)
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hp : v^(-r) = v^(1-r)/v := by
    simpa only [show 1-r-1 = -r by ring] using Real.rpow_sub_one (ne_of_gt hv) (1-r)
  dsimp [displacedDeficitPrimitive]
  rw [hp]
  ring

private theorem displacedDeficitPrimitive_cap_limit
    (h r : ℝ) (hh : 0 < h) (hr0 : 0 < r) :
    Tendsto (displacedDeficitPrimitive h r) (𝓝[<] (1/h)) (𝓝 (-(h^r))) := by
  have hc : 0 < 1/h := div_pos zero_lt_one hh
  have hcont : ContinuousAt (displacedDeficitPrimitive h r) (1/h) :=
    (Real.continuousAt_rpow_const (1/h) (-r) (Or.inl hc.ne')).mul
      (((continuous_const.sub (continuous_const.mul continuous_id)).rpow_const
        (fun _ => Or.inr hr0.le)).continuousAt.sub_const 1)
  have hvalue : displacedDeficitPrimitive h r (1/h) = -(h^r) := by
    dsimp [displacedDeficitPrimitive]
    rw [mul_one_div_cancel hh.ne',sub_self,Real.zero_rpow hr0.ne',zero_sub,
      one_div,Real.inv_rpow hh.le,Real.rpow_neg hh.le,inv_inv]
    ring
  simpa only [hvalue] using hcont.tendsto.mono_left nhdsWithin_le_nhds

private theorem displaced_noise_mobius_identity
    (D r h : ℝ) (hh : 0 < h) :
    (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
      (u^(-r-1)*(1-(1+h*u)^(-D)))) =
      ∫⁻ v in Set.Ioo (0 : ℝ) (1/h), ENNReal.ofReal
        (v^(-r-1)*((1-h*v)^(r-1)-(1-h*v)^(D+r-1))) := by
  let S : Set ℝ := Set.Ioo 0 (1/h)
  let f : ℝ → ℝ := fun v => v/(1-h*v)
  let f' : ℝ → ℝ := fun v => ((1-h*v)^2)⁻¹
  have hbase (v : ℝ) (hv : v ∈ S) : 0 < 1-h*v := by
    have hvh := (lt_div_iff₀ hh).mp hv.2
    nlinarith
  have hden (v : ℝ) (hv : v ∈ S) : 1+h*f v = 1/(1-h*v) := by
    dsimp [f]
    field_simp [(hbase v hv).ne']
    ring
  have himage : f '' S = Set.Ioi (0 : ℝ) := by
    ext u
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact div_pos hv.1 (hbase v hv)
    · intro hu
      have hu0 : (0 : ℝ) < u := hu
      have hdu : 0 < 1+h*u := by positivity
      have hcancel : 1-h*(u/(1+h*u)) = (1+h*u)⁻¹ := by
        field_simp [hdu.ne']
        ring
      refine ⟨u/(1+h*u), ⟨div_pos hu0 hdu, ?_⟩, ?_⟩
      · apply (div_lt_div_iff₀ hdu hh).2
        nlinarith
      · change (u/(1+h*u))/(1-h*(u/(1+h*u))) = u
        rw [hcancel]
        field_simp [hdu.ne']
  have hinj : Set.InjOn f S := by
    intro v hv w hw heq
    have heq' : v*(1-h*w) = w*(1-h*v) :=
      (div_eq_div_iff (hbase v hv).ne' (hbase w hw).ne').mp heq
    nlinarith
  have hderiv (v : ℝ) (hv : v ∈ S) : HasDerivWithinAt f (f' v) S v := by
    have hraw := ((hasDerivAt_id v).div
      ((hasDerivAt_const v 1).sub ((hasDerivAt_id v).const_mul h))
      (hbase v hv).ne').hasDerivWithinAt (s := S)
    apply HasDerivWithinAt.congr_deriv hraw
    dsimp only [id_eq,f',Pi.sub_apply]
    ring
  have hcoef (v : ℝ) (hv : v ∈ S) :
      |f' v| * ((f v)^(-r-1)*(1-(1+h*f v)^(-D))) =
        v^(-r-1)*((1-h*v)^(r-1)-(1-h*v)^(D+r-1)) := by
    have ha := hbase v hv
    have hatt : (1+h*f v)^(-D) = (1-h*v)^D := by
      rw [hden v hv,one_div,Real.inv_rpow ha.le,
        Real.rpow_neg ha.le D,inv_inv]
    have hp : |f' v| * (f v)^(-r-1) = v^(-r-1)*(1-h*v)^(r-1) := by
      rw [abs_of_nonneg (by dsimp [f']; positivity)]
      dsimp [f,f']
      rw [Real.div_rpow hv.1.le ha.le,
        show r-1 = (0-(-r-1))-2 by ring,
        Real.rpow_sub ha (0-(-r-1)) 2,Real.rpow_sub ha 0 (-r-1),
        Real.rpow_zero,Real.rpow_two]
      ring
    have hpβ : (1-h*v)^(r-1)*(1-h*v)^D = (1-h*v)^(D+r-1) := by
      rw [← Real.rpow_add ha]
      congr 1
      ring
    rw [← mul_assoc,hp,hatt,mul_sub,mul_one,mul_assoc,hpβ]
    ring
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := S) (f := f) (f' := f') measurableSet_Ioo hderiv hinj
      (fun u => ENNReal.ofReal (u^(-r-1)*(1-(1+h*u)^(-D))))
  rw [himage] at hchange
  refine hchange.trans (setLIntegral_congr_fun measurableSet_Ioo (fun v hv => ?_))
  rw [← ENNReal.ofReal_mul (abs_nonneg _),hcoef v hv]

private theorem displaced_tail_mellin_lintegral
    (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    (∫⁻ v in Set.Ioi c, ENNReal.ofReal (v^(-r-1))) = ENNReal.ofReal (c^(-r)/r) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -r-1 < -1) hc
  have hn : ∀ᵐ v ∂volume.restrict (Set.Ioi c), 0 ≤ v^(-r-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact Real.rpow_nonneg (hc.trans hv).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_Ioi_rpow_of_lt (by linarith : -r-1 < -1) hc]
  congr 1
  rw [show -r-1+1 = -r by ring]
  field_simp [hr.ne']

private theorem displaced_deficit_eq_noise
    (D r h : ℝ) (_hD : 0 < D) (hr0 : 0 < r) (hr1 : r < 1)
    (hβ : 0 < D+r-1) (hh : 0 < h)
    (hJ : (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
      (u^(-r-1)*(1-(1+h*u)^(-D)))) ≠ ∞) :
    (∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal
      (v^(-r-1)*(1-displacedDeficitCutoff (D+r-1) h v))) =
      ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (u^(-r-1)*(1-(1+h*u)^(-D))) := by
  let β : ℝ := D+r-1
  let cap : ℝ := 1/h
  let S : Set ℝ := Set.Ioo 0 cap
  let i : ℝ → ℝ := fun v => v^(-r-1)*(1-(1-h*v)^β)
  let j : ℝ → ℝ := fun v => v^(-r-1)*((1-h*v)^(r-1)-(1-h*v)^β)
  let H : ℝ → ℝ := fun v => v^(-r-1)*(1-(1-h*v)^(r-1))
  have hc : 0 < cap := div_pos zero_lt_one hh
  have hbase (v : ℝ) (hv : v ∈ S) : 0 < 1-h*v := by
    have hvh := (lt_div_iff₀ hh).mp hv.2
    nlinarith
  have hinonneg : ∀ᵐ v ∂volume.restrict S, 0 ≤ i v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact mul_nonneg (Real.rpow_nonneg hv.1.le _)
      (sub_nonneg.mpr (Real.rpow_le_one (hbase v hv).le (by nlinarith [hh,hv.1]) hβ.le))
  have hjnonneg : ∀ᵐ v ∂volume.restrict S, 0 ≤ j v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact mul_nonneg (Real.rpow_nonneg hv.1.le _)
      (sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_ge
        (hbase v hv) (by nlinarith [hh,hv.1]) (by dsimp [β]; linarith)))
  have hi : IntegrableOn i S :=
    IntegrableOn.congr_fun ((displaced_deficit_integrable β r h hβ hr0 hr1 hh).mono_set
      Set.Ioo_subset_Ioi_self) (fun v hv => by
        change v^(-r-1)*(1-displacedDeficitCutoff β h v) =
          v^(-r-1)*(1-(1-h*v)^β)
        rw [displacedDeficitCutoff,max_eq_left (hbase v hv).le]) measurableSet_Ioo
  have hJtrans := displaced_noise_mobius_identity D r h hh
  have hjfinite : (∫⁻ v in S, ENNReal.ofReal (j v)) ≠ ∞ := by
    rw [← hJtrans]
    exact hJ
  have hj : IntegrableOn j S :=
    (lintegral_ofReal_ne_top_iff_integrable
      (((measurable_id.pow_const _).mul
        (((measurable_const.sub (measurable_const.mul measurable_id)).pow_const _).sub
          ((measurable_const.sub (measurable_const.mul measurable_id)).pow_const _))).aestronglyMeasurable)
      hjnonneg).1 hjfinite
  have hHpoint (v : ℝ) : i v-j v = H v := by dsimp [i,j,H]; ring
  have hHi : IntegrableOn H S := (hi.sub hj).congr_fun
    (fun v _ => hHpoint v) measurableSet_Ioo
  have hderiv (v : ℝ) (hv : v ∈ S) :
      HasDerivAt (displacedDeficitPrimitive h r) (r*H v) v := by
    simpa only [H,mul_assoc] using displacedDeficitPrimitive_hasDerivAt h r hh hv
  have hint : IntervalIntegrable (fun v => r*H v) volume 0 cap :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hc.le).mpr (hHi.const_mul r)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    hc hderiv hint (displacedDeficitPrimitive_zero_limit h r hr1)
      (displacedDeficitPrimitive_cap_limit h r hh hr0)
  rw [intervalIntegral.integral_of_le hc.le,integral_Ioc_eq_integral_Ioo,
    integral_const_mul,sub_zero] at hFTC
  have hHint : (∫ v in S, H v) = (∫ v in S, i v)-(∫ v in S, j v) := by
    rw [← integral_sub hi hj]
    exact setIntegral_congr_fun measurableSet_Ioo (fun v _ => (hHpoint v).symm)
  rw [hHint] at hFTC
  have hreal : (∫ v in S, i v)+h^r/r = ∫ v in S, j v := by
    field_simp [hr0.ne']
    nlinarith [hFTC]
  have hNN : (∫⁻ v in S, ENNReal.ofReal (i v))+ENNReal.ofReal (h^r/r) =
      ∫⁻ v in S, ENNReal.ofReal (j v) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi hinonneg,
      ← ofReal_integral_eq_lintegral_ofReal hj hjnonneg,
      ← ENNReal.ofReal_add (integral_nonneg_of_ae hinonneg)
        (div_nonneg (Real.rpow_nonneg hh.le _) hr0.le),hreal]
  have hunion : Set.Ioc (0 : ℝ) cap ∪ Set.Ioi cap = Set.Ioi 0 := by
    ext v
    simp only [Set.mem_union,Set.mem_Ioc,Set.mem_Ioi]
    constructor
    · rintro (⟨hv,_⟩ | hv)
      · exact hv
      · exact hc.trans hv
    · intro hv
      rcases le_or_gt v cap with h1 | h1
      · exact Or.inl ⟨hv,h1⟩
      · exact Or.inr h1
  have hdisjoint : Disjoint (Set.Ioc (0 : ℝ) cap) (Set.Ioi cap) :=
    Set.disjoint_left.2 (fun _ hv hw => (not_lt_of_ge hv.2) (show cap < _ from hw))
  have htail : (∫⁻ v in Set.Ioi cap, ENNReal.ofReal
      (v^(-r-1)*(1-displacedDeficitCutoff β h v))) = ENNReal.ofReal (h^r/r) := by
    calc
      _ = ∫⁻ v in Set.Ioi cap, ENNReal.ofReal (v^(-r-1)) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro v hv
        have ha : 1-h*v ≤ 0 := by
          have hvh := (div_lt_iff₀ hh).mp hv
          nlinarith
        dsimp only [displacedDeficitCutoff]
        rw [max_eq_right ha,Real.zero_rpow hβ.ne',sub_zero,mul_one]
      _ = ENNReal.ofReal (cap^(-r)/r) := displaced_tail_mellin_lintegral r cap hr0 hc
      _ = _ := by
        dsimp [cap]
        rw [one_div,Real.inv_rpow hh.le,Real.rpow_neg hh.le,inv_inv]
  calc
    _ = (∫⁻ v in Set.Ioc (0 : ℝ) cap, ENNReal.ofReal
        (v^(-r-1)*(1-displacedDeficitCutoff β h v))) +
        (∫⁻ v in Set.Ioi cap, ENNReal.ofReal
          (v^(-r-1)*(1-displacedDeficitCutoff β h v))) := by
      rw [← hunion,lintegral_union measurableSet_Ioi hdisjoint]
    _ = (∫⁻ v in S, ENNReal.ofReal (i v))+ENNReal.ofReal (h^r/r) := by
      rw [htail,← restrict_Ioo_eq_restrict_Ioc]
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro v hv
      change ENNReal.ofReal (v^(-r-1)*(1-displacedDeficitCutoff β h v)) =
        ENNReal.ofReal (v^(-r-1)*(1-(1-h*v)^β))
      rw [displacedDeficitCutoff,max_eq_left (hbase v hv).le]
    _ = ∫⁻ v in S, ENNReal.ofReal (j v) := hNN
    _ = _ := hJtrans.symm

private theorem displaced_retained_mellin_lintegral_identity
    (D r h : ℝ) (hh : 0 < h) (hβ : 0 < D+r-1) (F : ℝ → ℝ≥0∞) :
    (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u^(-r-1)) *
      ENNReal.ofReal ((1+h*u)^(-D)) * F (u/(1+h*u))) =
      ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (v^(-r-1)) *
        ENNReal.ofReal (displacedDeficitCutoff (D+r-1) h v) * F v := by
  let S : Set ℝ := Set.Ioo 0 (1/h)
  let f : ℝ → ℝ := fun v => v/(1-h*v)
  let f' : ℝ → ℝ := fun v => ((1-h*v)^2)⁻¹
  have hbase (v : ℝ) (hv : v ∈ S) : 0 < 1-h*v := by
    have hvh := (lt_div_iff₀ hh).mp hv.2
    nlinarith
  have hden (v : ℝ) (hv : v ∈ S) : 1+h*f v = 1/(1-h*v) := by
    dsimp [f]
    field_simp [(hbase v hv).ne']
    ring
  have hback (v : ℝ) (hv : v ∈ S) : f v/(1+h*f v) = v := by
    rw [hden v hv]
    dsimp [f]
    rw [div_div_div_cancel_right₀ (hbase v hv).ne',div_one]
  have himage : f '' S = Set.Ioi (0 : ℝ) := by
    ext u
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact div_pos hv.1 (hbase v hv)
    · intro hu
      have hu0 : (0 : ℝ) < u := hu
      have hdu : 0 < 1+h*u := by positivity
      have hcancel : 1-h*(u/(1+h*u)) = (1+h*u)⁻¹ := by
        field_simp [hdu.ne']
        ring
      refine ⟨u/(1+h*u), ⟨div_pos hu0 hdu, ?_⟩, ?_⟩
      · apply (div_lt_div_iff₀ hdu hh).2
        nlinarith
      · change (u/(1+h*u))/(1-h*(u/(1+h*u))) = u
        rw [hcancel]
        field_simp [hdu.ne']
  have hinj : Set.InjOn f S := by
    intro v hv w hw heq
    have heq' := congrArg (fun u : ℝ => u/(1+h*u)) heq
    simpa only [hback v hv,hback w hw] using heq'
  have hderiv (v : ℝ) (hv : v ∈ S) : HasDerivWithinAt f (f' v) S v := by
    have hraw := ((hasDerivAt_id v).div
      ((hasDerivAt_const v 1).sub ((hasDerivAt_id v).const_mul h))
      (hbase v hv).ne').hasDerivWithinAt (s := S)
    apply HasDerivWithinAt.congr_deriv hraw
    dsimp only [id_eq,f',Pi.sub_apply]
    ring
  have hcoef (v : ℝ) (hv : v ∈ S) :
      |f' v| * (f v)^(-r-1)*(1+h*f v)^(-D) =
        v^(-r-1)*(1-h*v)^(D+r-1) := by
    have ha := hbase v hv
    have hatt : (1+h*f v)^(-D) = (1-h*v)^D := by
      rw [hden v hv,one_div,Real.inv_rpow ha.le,Real.rpow_neg ha.le D,inv_inv]
    have hp : ((1-h*v)^D/(1-h*v)^(-r-1))/(1-h*v)^2 =
        (1-h*v)^(D+r-1) := by
      rw [← Real.rpow_sub ha D (-r-1),← Real.rpow_two (1-h*v),
        ← Real.rpow_sub ha (D-(-r-1)) 2]
      congr 1
      ring
    rw [hatt,abs_of_nonneg (by dsimp [f']; positivity)]
    dsimp [f,f']
    rw [Real.div_rpow hv.1.le ha.le,← hp]
    ring
  let G : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (u^(-r-1)) *
    ENNReal.ofReal ((1+h*u)^(-D)) * F (u/(1+h*u))
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := S) (f := f) (f' := f') measurableSet_Ioo hderiv hinj G
  have hfirst : (∫⁻ u in Set.Ioi (0 : ℝ), G u) =
      ∫⁻ v in S, ENNReal.ofReal (v^(-r-1))*
        ENNReal.ofReal (displacedDeficitCutoff (D+r-1) h v)*F v := by
    rw [himage] at hchange
    refine hchange.trans (setLIntegral_congr_fun measurableSet_Ioo (fun v hv => ?_))
    have hfpos : 0 < f v := div_pos hv.1 (hbase v hv)
    calc
      _ = ENNReal.ofReal (|f' v| * (f v)^(-r-1)*(1+h*f v)^(-D))*F v := by
        dsimp [G]
        rw [hback v hv,ENNReal.ofReal_mul
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hfpos.le _)),
          ENNReal.ofReal_mul (abs_nonneg _)]
        ac_rfl
      _ = _ := by
        rw [hcoef v hv,ENNReal.ofReal_mul (Real.rpow_nonneg hv.1.le _),
          displacedDeficitCutoff,max_eq_left (hbase v hv).le]
  have hsplit : Set.Ioc (0 : ℝ) (1/h) ∪ Set.Ioi (1/h) = Set.Ioi 0 := by
    ext v
    simp only [Set.mem_union,Set.mem_Ioc,Set.mem_Ioi]
    constructor
    · rintro (⟨hv,_⟩ | hv)
      · exact hv
      · exact (div_pos zero_lt_one hh).trans hv
    · intro hv
      rcases le_or_gt v (1/h) with hc | hc
      · exact Or.inl ⟨hv,hc⟩
      · exact Or.inr hc
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) (1/h)) (Set.Ioi (1/h)) :=
    Set.disjoint_left.2 (fun _ hv hw => (not_lt_of_ge hv.2) (show 1/h < _ from hw))
  have htail : (∫⁻ v in Set.Ioi (1/h), ENNReal.ofReal (v^(-r-1))*
      ENNReal.ofReal (displacedDeficitCutoff (D+r-1) h v)*F v) = 0 := by
    apply setLIntegral_eq_zero measurableSet_Ioi
    intro v hv
    have ha : 1-h*v ≤ 0 := by
      have hvh := (div_lt_iff₀ hh).mp hv
      nlinarith
    simp only [displacedDeficitCutoff,max_eq_right ha,Real.zero_rpow hβ.ne',
      ENNReal.ofReal_zero,mul_zero,zero_mul,Pi.zero_apply]
  calc
    _ = ∫⁻ v in S, ENNReal.ofReal (v^(-r-1))*
        ENNReal.ofReal (displacedDeficitCutoff (D+r-1) h v)*F v := hfirst
    _ = _ := by
      rw [← hsplit,lintegral_union measurableSet_Ioi hdisj,htail,add_zero,
        ← restrict_Ioo_eq_restrict_Ioc]

private theorem exists_displaced_strict_scalar_budget
    (D r : ℝ) (hD : 0 < D) (hr0 : 0 < r) (hr1 : r < 1)
    (hβ : 0 < D+r-1) (F : ℝ → ℝ≥0∞)
    (hT : (∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (v^(-r-1))*F v) ≠ ∞)
    (R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (hfloor : ∀ v : ℝ, R < v → ENNReal.ofReal (1+c) ≤ F v) :
    ∃ n : ℕ,
      let h : ℝ := 1/((n : ℝ)+1)
      (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (u^(-r-1)*(1-(1+h*u)^(-D)))) ≠ ∞ ∧
      (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u^(-r-1))*
        ENNReal.ofReal ((1+h*u)^(-D))*F (u/(1+h*u))) +
        (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (u^(-r-1)*(1-(1+h*u)^(-D)))) <
        ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (v^(-r-1))*F v := by
  let β : ℝ := D+r-1
  let hn : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  let L : ℝ≥0∞ := ∫⁻ v in Set.Ioc (0 : ℝ) R, ENNReal.ofReal (v^(-r))
  obtain ⟨N0,hN0⟩ := exists_nat_ge β
  let N : ℕ := max N0 1
  have hN : β ≤ (N : ℝ) := hN0.trans (by exact_mod_cast le_max_left N0 1)
  have hN1 : 1 ≤ N := le_max_right N0 1
  have hLi : IntegrableOn (fun v : ℝ => v^(-r)) (Set.Ioc 0 R) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hR).2 (by linarith)
  have hLfinite : L ≠ ∞ := by
    exact (lintegral_ofReal_ne_top_iff_integrable
      (measurable_id.pow_const _).aestronglyMeasurable (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
        exact Real.rpow_nonneg hv.1.le _)).2 hLi
  let C : ℝ := (N : ℝ)*L.toReal
  have hhn (n : ℕ) : 0 < hn n := by dsimp [hn]; positivity
  have hhnlim : Tendsto hn atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall : ∀ᶠ n : ℕ in atTop, C*(hn n)^(1-r) < c/r := by
    have hpow := hhnlim.rpow_const (Or.inr (by linarith : 0 ≤ 1-r))
    have hlim : Tendsto (fun n => C*(hn n)^(1-r)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Real.zero_rpow (by linarith : 1-r ≠ 0),mul_zero] using hpow.const_mul C
    exact hlim.eventually (gt_mem_nhds (div_pos hc hr0))
  have hcap : ∀ᶠ n : ℕ in atTop, hn n*R < 1 := by
    have hlim : Tendsto (fun n => hn n*R) atTop (𝓝 (0 : ℝ)) := by
      simpa only [zero_mul] using hhnlim.mul_const R
    exact hlim.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨n,hnsmall,hncap⟩ := (hsmall.and hcap).exists
  let h : ℝ := hn n
  have hh : 0 < h := hhn n
  have hRcap : R < 1/h := by
    apply (lt_div_iff₀ hh).2
    simpa only [mul_comm] using hncap
  let w : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (v^(-r-1))
  let k : ℝ → ℝ := displacedDeficitCutoff β h
  let A : ℝ≥0∞ := ∫⁻ v in Set.Ioi (0 : ℝ), w v*ENNReal.ofReal (1-k v)*F v
  let B : ℝ≥0∞ := ∫⁻ v in Set.Ioi (0 : ℝ), w v*ENNReal.ofReal (k v)*F v
  let I0 : ℝ≥0∞ := ∫⁻ v in Set.Ioc (0 : ℝ) R, w v*ENNReal.ofReal (1-k v)
  let I1 : ℝ≥0∞ := ∫⁻ v in Set.Ioi R, w v*ENNReal.ofReal (1-k v)
  let J : ℝ≥0∞ := ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
    (u^(-r-1)*(1-(1+h*u)^(-D)))
  have hnoise := displaced_noise_sequence_finite_and_tendsto D r hD.le hr0 hr1
  have hJ : J ≠ ∞ := hnoise.1 n
  have hsplit : Set.Ioc (0 : ℝ) R ∪ Set.Ioi R = Set.Ioi 0 := by
    ext v
    simp only [Set.mem_union,Set.mem_Ioc,Set.mem_Ioi]
    constructor
    · rintro (⟨hv,_⟩ | hv)
      · exact hv
      · exact hR.trans hv
    · intro hv
      rcases le_or_gt v R with hvR | hvR
      · exact Or.inl ⟨hv,hvR⟩
      · exact Or.inr hvR
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) R) (Set.Ioi R) :=
    Set.disjoint_left.2 (fun _ hv hw => (not_lt_of_ge hv.2) (show R < _ from hw))
  have hIsum : I0+I1 = J := by
    rw [← lintegral_union measurableSet_Ioi hdisj,hsplit]
    calc
      _ = ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (v^(-r-1)*(1-k v)) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro v hv
        exact (ENNReal.ofReal_mul (Real.rpow_nonneg hv.le _)).symm
      _ = J := displaced_deficit_eq_noise D r h hD hr0 hr1 hβ hh hJ
  have hIfinite : I0+I1 ≠ ∞ := by rw [hIsum]; exact hJ
  have hI1 : I1 ≠ ∞ := (ENNReal.add_ne_top.mp hIfinite).2
  have hlow : I0 ≤ ENNReal.ofReal (h*C) := by
    calc
      _ ≤ ∫⁻ v in Set.Ioc (0 : ℝ) R,
          ENNReal.ofReal ((N : ℝ)*h)*ENNReal.ofReal (v^(-r)) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro v hv
        have hbound := displacedDeficitCutoff_linear_bound β h v N hβ hN hN1 hh hv.1
        calc
          _ = ENNReal.ofReal (v^(-r-1)*(1-k v)) :=
            (ENNReal.ofReal_mul (Real.rpow_nonneg hv.1.le _)).symm
          _ ≤ ENNReal.ofReal (v^(-r-1)*((N : ℝ)*h*v)) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hbound
              (Real.rpow_nonneg hv.1.le _))
          _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            have hp : v^(-r) = v^(-r-1)*v := by
              simpa only [show (-r-1)+1 = -r by ring] using
                Real.rpow_add_one hv.1.ne' (-r-1)
            rw [hp]
            ring
      _ = ENNReal.ofReal ((N : ℝ)*h)*L :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (h*C) := by
        rw [← ENNReal.ofReal_toReal hLfinite,← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [C]
        ring
  have htail : ENNReal.ofReal (h^r/r) ≤ I1 := by
    calc
      _ = ∫⁻ v in Set.Ioi (1/h), w v*ENNReal.ofReal (1-k v) := by
        calc
          _ = ∫⁻ v in Set.Ioi (1/h), ENNReal.ofReal (v^(-r-1)) := by
            rw [displaced_tail_mellin_lintegral r (1/h) hr0 (div_pos zero_lt_one hh)]
            rw [one_div,Real.inv_rpow hh.le,Real.rpow_neg hh.le,inv_inv]
          _ = _ := by
            apply setLIntegral_congr_fun measurableSet_Ioi
            intro v hv
            have ha : 1-h*v ≤ 0 := by
              have hvh := (div_lt_iff₀ hh).mp hv
              nlinarith
            have hkzero : k v = 0 := by
              change (max (1-h*v) 0)^β = 0
              rw [max_eq_right ha,Real.zero_rpow (show β ≠ 0 from hβ.ne')]
            change w v = w v*ENNReal.ofReal (1-k v)
            rw [hkzero]
            simp
      _ ≤ I1 := lintegral_mono_set (fun _ hv => hRcap.trans hv)
  have hsmallreal : h*C < c*(h^r/r) := by
    have hmul := mul_lt_mul_of_pos_right hnsmall (Real.rpow_pos_of_pos hh r)
    have hp : h^(1-r)*h^r = h := by
      rw [← Real.rpow_add hh,show 1-r+r = 1 by ring,Real.rpow_one]
    calc
      h*C = C*(h^(1-r)*h^r) := by rw [hp]; ring
      _ < (c/r)*h^r := by simpa only [mul_assoc] using hmul
      _ = _ := by ring
  have hlowstrict : I0 < ENNReal.ofReal c*I1 := by
    calc
      I0 ≤ ENNReal.ofReal (h*C) := hlow
      _ < ENNReal.ofReal (c*(h^r/r)) :=
        (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc (div_pos
          (Real.rpow_pos_of_pos hh r) hr0))).2 hsmallreal
      _ = ENNReal.ofReal c*ENNReal.ofReal (h^r/r) := ENNReal.ofReal_mul hc.le
      _ ≤ ENNReal.ofReal c*I1 := mul_le_mul_right htail _
  have hlossfloor : (1+ENNReal.ofReal c)*I1 ≤ A := by
    calc
      _ = ∫⁻ v in Set.Ioi R, (1+ENNReal.ofReal c)*(w v*ENNReal.ofReal (1-k v)) :=
        (lintegral_const_mul' _ _ (by simp)).symm
      _ ≤ ∫⁻ v in Set.Ioi R, w v*ENNReal.ofReal (1-k v)*F v := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro v hv
        have hf := hfloor v hv
        rw [ENNReal.ofReal_add zero_le_one hc.le,ENNReal.ofReal_one] at hf
        simpa only [mul_comm,mul_left_comm,mul_assoc] using
          mul_le_mul_left hf (w v*ENNReal.ofReal (1-k v))
      _ ≤ A := lintegral_mono_set (fun _ hv => hR.trans hv)
  have hJA : J < A := by
    calc
      J = I0+I1 := hIsum.symm
      _ < ENNReal.ofReal c*I1+I1 := ENNReal.add_lt_add_right hI1 hlowstrict
      _ = (1+ENNReal.ofReal c)*I1 := by rw [add_mul,one_mul]; ac_rfl
      _ ≤ A := hlossfloor
  have hBT : B ≤ ∫⁻ v in Set.Ioi (0 : ℝ), w v*F v := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro v hv
    have hk := displacedDeficitCutoff_bounds β h v hβ hh hv
    have hkle : ENNReal.ofReal (k v) ≤ 1 := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hk.2
    calc
      _ ≤ w v*1*F v := by gcongr
      _ = _ := by rw [mul_one]
  have hB : B ≠ ∞ := ne_top_of_le_ne_top hT hBT
  have hBAT : B+A ≤ ∫⁻ v in Set.Ioi (0 : ℝ), w v*F v := by
    calc
      _ ≤ ∫⁻ v in Set.Ioi (0 : ℝ),
          w v*ENNReal.ofReal (k v)*F v+w v*ENNReal.ofReal (1-k v)*F v :=
        le_lintegral_add _ _
      _ = _ := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro v hv
        have hk := displacedDeficitCutoff_bounds β h v hβ hh hv
        change w v*ENNReal.ofReal (k v)*F v+
          w v*ENNReal.ofReal (1-k v)*F v = w v*F v
        rw [← add_mul,← mul_add,← ENNReal.ofReal_add hk.1 (sub_nonneg.mpr hk.2)]
        simp only [add_sub_cancel,ENNReal.ofReal_one,mul_one]
  refine ⟨n,hJ,?_⟩
  rw [displaced_retained_mellin_lintegral_identity D r h hh hβ F]
  exact (ENNReal.add_lt_add_left hB hJA).trans_le hBAT

/-- A genuinely nonsimple counting law admits an actual strictly better simple law. -/
theorem exists_admissible_displacedLaw_energy_lt_factorialW_of_not_ae_simple
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs_lower : -2 < s) (hs_neg : s < 0)
    (P : Measure (CountingConfiguration d)) [IsProbabilityMeasure P]
    (hstationary : IsStationary d (P.map Subtype.val))
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d)))
    (hsecond : ∀ K : Set (Rd d), MeasurableSet K → Bornology.IsBounded K →
      (∫⁻ μ, (μ.val K)^2 ∂P) < ∞)
    (hW : factorialW d s P
      (fun n => hsecond (Metric.closedBall (0 : Rd d) (n : ℝ))
        measurableSet_closedBall (isCompact_closedBall (0 : Rd d) (n : ℝ)).isBounded) ≠ ⊤)
    (hnonsimple : ¬ ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val) :
    ∃ t : ℝ, 0 < t ∧ Admissible d (displacedLaw d t P) ∧
      W d s (displacedLaw d t P) < factorialW d s P
        (fun n => hsecond (Metric.closedBall (0 : Rd d) (n : ℝ))
          measurableSet_closedBall (isCompact_closedBall (0 : Rd d) (n : ℝ)).isBounded) := by
  let hball : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ)))^2 ∂P) < ∞ :=
    fun n => hsecond (Metric.closedBall (0 : Rd d) (n : ℝ))
      measurableSet_closedBall (isCompact_closedBall (0 : Rd d) (n : ℝ)).isBounded
  let D : ℝ := (d : ℝ)/2
  let r : ℝ := -s/2
  let γ : ℝ≥0∞ := ENNReal.ofReal (gamma_s s)
  let F : ℝ → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (max ((factorialQ d P hball v).toReal+1-B d v) 0)
  let T : ℝ≥0∞ := ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (v^(-r-1))*F v
  let m : ℝ≥0∞ := factorialCollisionAnchor d P hball (cube d 1)
  let c : ℝ := m.toReal/2
  have hdpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hd
  have hD : 0 < D := by dsimp [D]; positivity
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hβ : 0 < D+r-1 := by
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    dsimp [D,r]
    linarith
  have he : -r-1 = s/2-1 := by dsimp [r]; ring
  have hγ0 : γ ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Riesz.Analysis.gamma_s_pos s hs_lower)
  have hinput : factorialW d s P hball = (γ*T : ℝ≥0∞) := by
    simpa only [T,F,he] using
      factorialW_eq_weighted_truncated_profile_neg d s hd hs_lower hs_neg P hball hW
  have hT : T ≠ ∞ := by
    intro htop
    apply hW
    rw [hinput,htop,ENNReal.mul_top hγ0,EReal.coe_ennreal_top]
  have hmfinite : m ≠ ∞ := (factorialCollisionAnchor_unitCube_lt_top d P hball).ne
  have hmpos : 0 < m.toReal :=
    factorialCollisionAnchor_unitCube_toReal_pos_of_not_ae_simple
      d P hball hstationary hnonsimple
  have hc : 0 < c := half_pos hmpos
  have hBlim : Tendsto (B d) atTop (𝓝 (0 : ℝ)) := by
    have hdiv : Tendsto (fun v : ℝ => Real.pi/v) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop tendsto_id
    change Tendsto (fun v : ℝ => (Real.pi/v)^D) atTop (𝓝 (0 : ℝ))
    simpa only [Real.zero_rpow hD.ne'] using hdiv.rpow_const (Or.inr hD.le)
  obtain ⟨R0,hR0⟩ := eventually_atTop.1 (hBlim.eventually (gt_mem_nhds hc))
  let R : ℝ := max R0 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right R0 1)
  have hfloor (v : ℝ) (hv : R < v) : ENNReal.ofReal (1+c) ≤ F v := by
    have hvpos : 0 < v := hR.trans hv
    have hqfinite := factorialQ_ne_top_of_factorialW_ne_top d s hs_lower P hball hW v hvpos
    have hmq : m.toReal ≤ (factorialQ d P hball v).toReal :=
      (ENNReal.toReal_le_toReal hmfinite hqfinite).2
        (factorialCollisionAnchor_unitCube_le_factorialQ d P hball v)
    have hBv : B d v < c := hR0 v ((le_max_left R0 1).trans hv.le)
    apply ENNReal.ofReal_le_ofReal
    exact (by dsimp [c] at *; linarith :
      1+c ≤ (factorialQ d P hball v).toReal+1-B d v).trans (le_max_left _ _)
  obtain ⟨n,hnJ,hbudget⟩ := exists_displaced_strict_scalar_budget
    D r hD hr0 hr1 hβ F hT R c hR hc hfloor
  let h : ℝ := 1/((n : ℝ)+1)
  let t : ℝ := h/8
  let Pout : ConfigurationLaw d := displacedLaw d t P
  let J : ℝ≥0∞ := ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
    (u^(s/2-1)*(1-(1+h*u)^(-D)))
  let A : ℝ≥0∞ := ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u^(s/2-1))*
    ENNReal.ofReal ((1+h*u)^(-D))*F (u/(1+h*u))
  let Tout : ℝ≥0∞ := ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u^(s/2-1))*
    ENNReal.ofReal (max ((Q d Pout u).toReal+1-B d u) 0)
  have hh : 0 < h := by dsimp [h]; positivity
  have ht : 0 < t := div_pos hh (by norm_num)
  have htu : 8*t = h := by dsimp [t]; ring
  have hJ : J ≠ ∞ := by simpa only [he] using hnJ
  have hAT : A+J < T := by simpa only [A,J,T,he] using hbudget
  have hWout : W d s Pout ≠ ⊤ :=
    (displacedLaw_energy_le_factorialW_add_noise
      d hd s hs_lower hs_neg P hstationary hmean hball hW h hh hJ).1
  have hpoint (u : ℝ) (hu : 0 < u) :
      ENNReal.ofReal (u^(s/2-1))*
        ENNReal.ofReal (max ((Q d Pout u).toReal+1-B d u) 0) ≤
      ENNReal.ofReal (u^(s/2-1)*(1-(1+h*u)^(-D))) +
        ENNReal.ofReal (u^(s/2-1))*ENNReal.ofReal ((1+h*u)^(-D))*F (u/(1+h*u)) := by
    let a : ℝ := (1+h*u)^(-D)
    let v : ℝ := u/(1+h*u)
    have hden : 0 < 1+h*u := by positivity
    have ha0 : 0 ≤ a := Real.rpow_nonneg hden.le _
    have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
      (by nlinarith : 1 ≤ 1+h*u) (by linarith)
    have hq : Q d Pout u = ENNReal.ofReal a*factorialQ d P hball v := by
      simpa only [← mul_assoc,htu] using
        Q_displacedLaw_eq_factorialQ d hdpos t ht P hstationary hmean hball u hu
    have hqreal : (Q d Pout u).toReal = a*(factorialQ d P hball v).toReal := by
      rw [hq,ENNReal.toReal_mul,ENNReal.toReal_ofReal ha0]
    have hbackground : a*B d v = B d u := by
      simpa only [← mul_assoc,htu] using displaced_background_identity d t u ht hu
    have hreal : max ((Q d Pout u).toReal+1-B d u) 0 ≤
        a*max ((factorialQ d P hball v).toReal+1-B d v) 0+(1-a) := by
      rw [hqreal,← hbackground]
      simpa only [add_sub_assoc] using clipped_affine_comparison
        (factorialQ d P hball v).toReal (B d v) a ha0 ha1
    have hNN : ENNReal.ofReal (max ((Q d Pout u).toReal+1-B d u) 0) ≤
        ENNReal.ofReal a*F v+ENNReal.ofReal (1-a) := by
      calc
        _ ≤ ENNReal.ofReal
            (a*max ((factorialQ d P hball v).toReal+1-B d v) 0+(1-a)) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = _ := by
          rw [ENNReal.ofReal_add (mul_nonneg ha0 (le_max_right _ _))
            (sub_nonneg.mpr ha1),ENNReal.ofReal_mul ha0]
    calc
      _ ≤ ENNReal.ofReal (u^(s/2-1))*
          (ENNReal.ofReal a*F v+ENNReal.ofReal (1-a)) := mul_le_mul_right hNN _
      _ = _ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _),mul_add]
        dsimp [a,v]
        ac_rfl
  have hnoiseMeas : Measurable (fun u : ℝ => ENNReal.ofReal
      (u^(s/2-1)*(1-(1+h*u)^(-D)))) :=
    ((measurable_id.pow_const _).mul (measurable_const.sub
      ((measurable_const.add (measurable_const.mul measurable_id)).pow_const _))).ennreal_ofReal
  have hout : Tout ≤ A+J := by
    calc
      _ ≤ ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (u^(s/2-1)*(1-(1+h*u)^(-D))) + ENNReal.ofReal (u^(s/2-1))*
            ENNReal.ofReal ((1+h*u)^(-D))*F (u/(1+h*u)) :=
        setLIntegral_mono' measurableSet_Ioi hpoint
      _ = J+A := lintegral_add_left hnoiseMeas _
      _ = A+J := add_comm _ _
  have hstrict : Tout < T := hout.trans_lt hAT
  refine ⟨t,ht,displacedLaw_admissible d hdpos t ht P hstationary hmean hsecond,?_⟩
  calc
    W d s Pout = (γ*Tout : ℝ≥0∞) :=
      W_eq_weighted_truncated_profile_neg d s hd hs_lower hs_neg Pout hWout
    _ < (γ*T : ℝ≥0∞) := EReal.coe_ennreal_strictMono
      (ENNReal.mul_lt_mul_right hγ0 ENNReal.ofReal_ne_top hstrict)
    _ = factorialW d s P hball := hinput.symm

end Riesz.Stationary
