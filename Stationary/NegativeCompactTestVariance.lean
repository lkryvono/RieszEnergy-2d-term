import Riesz.Stationary.NegativeCompactPairHeatRemoval
import Riesz.Stationary.NegativeHeatSpectrum
import Riesz.Stationary.CompactHeadAngularSpectrum

/-! Compact complex-test variance under the original common angular spectrum. -/

noncomputable section
open MeasureTheory Filter RieszShowcase Riesz.Configuration
open scoped ENNReal Topology ComplexConjugate CompactlySupported RealInnerProductSpace

namespace Riesz.Stationary

def negativeCompactAngularAmplitude (d : ℕ) (f : Rd d → ℂ) (k : Rd d) : ℂ :=
  ∫ x, f x * Complex.exp ((inner ℝ k x : ℂ) * Complex.I)

def negativeCompactTestDiscrepancy (d : ℕ)
    (f : C_c(Rd d, ℂ)) (η : CountingConfiguration d) : ℂ :=
  (∫ x, f x ∂η.val) - ∫ x, f x ∂volume

def negativeCompactPairReal (d : ℕ) (f : C_c(Rd d, ℂ)) :
    C_c(Rd d × Rd d, ℝ) :=
  ⟨⟨fun p => (conj (f p.1) * f p.2).re, by fun_prop⟩, by
    refine HasCompactSupport.intro
      (f.hasCompactSupport.prod f.hasCompactSupport) ?_
    intro p hp
    by_cases ha : p.1 ∈ tsupport f
    · have hb : p.2 ∉ tsupport f := fun hb => hp ⟨ha, hb⟩
      simp [image_eq_zero_of_notMem_tsupport hb]
    · simp [image_eq_zero_of_notMem_tsupport ha]⟩

private theorem measurable_negativeCompactAngularAmplitude
    (d : ℕ) (f : C_c(Rd d, ℂ)) :
    Measurable (negativeCompactAngularAmplitude d f) := by
  have hm : StronglyMeasurable (fun p : Rd d × Rd d =>
      f p.2 * Complex.exp ((inner ℝ p.1 p.2 : ℂ) * Complex.I)) :=
    (show Continuous _ from by fun_prop).stronglyMeasurable
  exact hm.integral_prod_right'.measurable


private theorem negativeCompactAngularAmplitude_pair
    (d : ℕ) (f : Rd d → ℂ) (k : Rd d) :
    (∫ p : Rd d × Rd d, conj (f p.1) * f p.2 *
      Complex.exp ((inner ℝ k (p.2-p.1) : ℂ) * Complex.I)
        ∂(volume.prod volume)) =
      (Complex.normSq (negativeCompactAngularAmplitude d f k) : ℂ) := by
  have hp (p : Rd d × Rd d) :
      conj (f p.1) * f p.2 *
        Complex.exp ((inner ℝ k (p.2-p.1) : ℂ) * Complex.I) =
      conj (f p.1 * Complex.exp ((inner ℝ k p.1 : ℂ) * Complex.I)) *
        (f p.2 * Complex.exp ((inner ℝ k p.2 : ℂ) * Complex.I)) := by
    rw [angularPhase_pair]
    simp only [map_mul]
    ring
  rw [integral_congr_ae (Eventually.of_forall hp),
    integral_prod_mul
      (fun x : Rd d => conj (f x *
        Complex.exp ((inner ℝ k x : ℂ) * Complex.I)))
      (fun x : Rd d => f x *
        Complex.exp ((inner ℝ k x : ℂ) * Complex.I)),
    integral_conj, ← Complex.normSq_eq_conj_mul_self,
    negativeCompactAngularAmplitude]


private theorem countingCompact_mean_nonneg
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (u : C_c(Rd d, ℝ)) (hu : ∀ x, 0 ≤ u x) :
    Integrable (fun η : CountingConfiguration d => ∫ x, u x ∂η.val)
        (countingLawOfSimple d P) ∧
    (∫ η : CountingConfiguration d, (∫ x, u x ∂η.val)
        ∂countingLawOfSimple d P) = ∫ x, u x ∂volume := by
  let Qc := countingLawOfSimple d P
  let F : CountingConfiguration d → ℝ≥0∞ :=
    fun η => ∫⁻ x, ENNReal.ofReal (u x) ∂η.val
  have hFm : Measurable F :=
    (Measure.measurable_lintegral u.continuous.measurable.ennreal_ofReal).comp
      measurable_subtype_coe
  have hmean : (∫⁻ η, F η ∂Qc) = ∫⁻ x, ENNReal.ofReal (u x) ∂volume := by
    have h := originalAdmissible_mean_lintegral d P hP
      (fun x => ENNReal.ofReal (u x)) u.continuous.measurable.ennreal_ofReal
    rw [← countingLawOfSimple_map_val d P hP.2.1] at h
    exact (lintegral_map (Measure.measurable_lintegral
      u.continuous.measurable.ennreal_ofReal) measurable_subtype_coe).symm.trans h
  have hvolfin : (∫⁻ x, ENNReal.ofReal (u x) ∂volume) ≠ ∞ :=
    (ofReal_integral_eq_lintegral_ofReal u.integrable
      (Eventually.of_forall hu)).symm.trans_ne ENNReal.ofReal_ne_top
  have hFfin : (∫⁻ η, F η ∂Qc) ≠ ∞ := hmean.trans_ne hvolfin
  have hpoint (η : CountingConfiguration d) :
      (F η).toReal = ∫ x, u x ∂η.val :=
    (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hu)
      u.integrable.aestronglyMeasurable).symm
  have hI : Integrable (fun η => (F η).toReal) Qc :=
    integrable_toReal_of_lintegral_ne_top hFm.aemeasurable hFfin
  refine ⟨hI.congr (Eventually.of_forall hpoint), ?_⟩
  calc
    _ = ∫ η, (F η).toReal ∂Qc :=
      integral_congr_ae (Eventually.of_forall (fun η => (hpoint η).symm))
    _ = (∫⁻ η, F η ∂Qc).toReal :=
      integral_toReal hFm.aemeasurable (ae_lt_top hFm hFfin)
    _ = (∫⁻ x, ENNReal.ofReal (u x) ∂volume).toReal := congrArg ENNReal.toReal hmean
    _ = _ := (integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall hu) u.integrable.aestronglyMeasurable).symm


private theorem countingCompact_mean
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (u : C_c(Rd d, ℝ)) :
    Integrable (fun η : CountingConfiguration d => ∫ x, u x ∂η.val)
        (countingLawOfSimple d P) ∧
    (∫ η : CountingConfiguration d, (∫ x, u x ∂η.val)
        ∂countingLawOfSimple d P) = ∫ x, u x ∂volume := by
  let up : C_c(Rd d, ℝ) := u ⊔ 0
  let um : C_c(Rd d, ℝ) := (-u) ⊔ 0
  have hp := countingCompact_mean_nonneg d P hP up (fun x => le_max_right _ _)
  have hm := countingCompact_mean_nonneg d P hP um (fun x => le_max_right _ _)
  have hdec (x : Rd d) : u x = up x - um x := by
    simpa only [up, um, CompactlySupportedContinuousMap.sup_apply,
      CompactlySupportedContinuousMap.zero_apply,
      CompactlySupportedContinuousMap.neg_apply] using (max_zero_sub_eq_self (u x)).symm
  have hInt (μ : Measure (Rd d)) [IsFiniteMeasureOnCompacts μ] :
      (∫ x, u x ∂μ) = (∫ x, up x ∂μ) - ∫ x, um x ∂μ :=
    (integral_congr_ae (Eventually.of_forall hdec)).trans
      (integral_sub up.integrable um.integrable)
  refine ⟨(hp.1.sub hm.1).congr
    (Eventually.of_forall (fun η => (hInt η.val).symm)), ?_⟩
  calc
    _ = ∫ η : CountingConfiguration d,
        ((∫ x, up x ∂η.val) - ∫ x, um x ∂η.val) ∂countingLawOfSimple d P :=
      integral_congr_ae (Eventually.of_forall (fun η => hInt η.val))
    _ = (∫ η : CountingConfiguration d, (∫ x, up x ∂η.val)
        ∂countingLawOfSimple d P) -
        ∫ η : CountingConfiguration d, (∫ x, um x ∂η.val)
          ∂countingLawOfSimple d P := integral_sub hp.1 hm.1
    _ = (∫ x, up x ∂volume) - ∫ x, um x ∂volume := by rw [hp.2, hm.2]
    _ = _ := (hInt volume).symm


private def realCompactProduct (d : ℕ) (u : C_c(Rd d, ℝ)) :
    C_c(Rd d × Rd d, ℝ) :=
  ⟨⟨fun p => u p.1 * u p.2, by fun_prop⟩, by
    refine HasCompactSupport.intro
      (u.hasCompactSupport.prod u.hasCompactSupport) ?_
    intro p hp
    by_cases ha : p.1 ∈ tsupport u
    · have hb : p.2 ∉ tsupport u := fun hb => hp ⟨ha, hb⟩
      simp [image_eq_zero_of_notMem_tsupport hb]
    · simp [image_eq_zero_of_notMem_tsupport ha]⟩

private theorem countingCompact_square
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (u : C_c(Rd d, ℝ)) :
    Integrable (fun η : CountingConfiguration d => (∫ x, u x ∂η.val)^2)
      (countingLawOfSimple d P) ∧
    (∫ η : CountingConfiguration d, (∫ x, u x ∂η.val)^2
      ∂countingLawOfSimple d P) =
      (∫ p, realCompactProduct d u p ∂originalAdmissibleFactorialMeasure d P hP) +
        ∫ x : Rd d, (u x)^2 ∂volume := by
  let Qc := countingLawOfSimple d P
  let v := realCompactProduct d u
  let diag := countingDiagonalTest d v
  have hfac := integrable_countingFactorialIntegral d Qc
    (countingLawOfSimple_localSecond_of_admissible d P hP) v
  have hdiag := countingCompact_mean d P hP diag
  have hGammaMean :
      (∫ p, v p ∂originalAdmissibleFactorialMeasure d P hP) =
        ∫ η, countingFactorialIntegral d η v ∂Qc :=
    integral_expectedFactorialMeasure d Qc
      (countingLawOfSimple_localSecond_of_admissible d P hP) v
  have hpoint (η : CountingConfiguration d) :
      (∫ x, u x ∂η.val)^2 =
        countingFactorialIntegral d η v + ∫ x, diag x ∂η.val := by
    change (∫ x, u x ∂η.val)^2 =
      ((∫ p : Rd d × Rd d, u p.1 * u p.2 ∂η.val.prod η.val) -
        ∫ x, u x * u x ∂η.val) + ∫ x, u x * u x ∂η.val
    rw [integral_prod_mul]
    ring
  refine ⟨(hfac.add hdiag.1).congr
    (Eventually.of_forall (fun η => (hpoint η).symm)), ?_⟩
  calc
    _ = (∫ η, countingFactorialIntegral d η v ∂Qc) +
        ∫ η : CountingConfiguration d, (∫ x, diag x ∂η.val) ∂Qc :=
      (integral_congr_ae (Eventually.of_forall hpoint)).trans
        (integral_add hfac hdiag.1)
    _ = (∫ p, v p ∂originalAdmissibleFactorialMeasure d P hP) +
        ∫ x, diag x ∂volume := by
      rw [← hGammaMean, hdiag.2]
    _ = _ := by
      change _ + (∫ x : Rd d, u x * u x ∂volume) = _ + ∫ x : Rd d, (u x)^2 ∂volume
      simp only [v, pow_two]



private theorem countingCompact_centered_square
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (u : C_c(Rd d, ℝ)) :
    Integrable (fun η : CountingConfiguration d =>
      ((∫ x, u x ∂η.val) - ∫ x, u x ∂volume)^2) (countingLawOfSimple d P) ∧
    (∫ η : CountingConfiguration d,
      ((∫ x, u x ∂η.val) - ∫ x, u x ∂volume)^2 ∂countingLawOfSimple d P) =
      (∫ p, realCompactProduct d u p ∂originalAdmissibleFactorialMeasure d P hP) +
        (∫ x : Rd d, (u x)^2 ∂volume) - (∫ x, u x ∂volume)^2 := by
  letI : IsProbabilityMeasure P := hP.1
  let Qc := countingLawOfSimple d P
  let X : CountingConfiguration d → ℝ := fun η => ∫ x, u x ∂η.val
  let m : ℝ := ∫ x, u x ∂volume
  obtain ⟨hX, hmean⟩ := countingCompact_mean d P hP u
  obtain ⟨hX2, hsecond⟩ := countingCompact_square d P hP u
  change Integrable X Qc at hX
  change Integrable (fun η => (X η)^2) Qc at hX2
  have hpoly (η : CountingConfiguration d) :
      (X η - m)^2 = (X η^2 - 2*m*X η) + m^2 := by ring
  have hI : Integrable (fun η => (X η^2 - 2*m*X η) + m^2) Qc :=
    (hX2.sub (hX.const_mul (2*m))).add (integrable_const (m^2))
  refine ⟨hI.congr (Eventually.of_forall (fun η => (hpoly η).symm)), ?_⟩
  change (∫ η, (X η - m)^2 ∂Qc) = _
  have hadd : (∫ η, (X η^2 - 2*m*X η) + m^2 ∂Qc) =
      (∫ η, X η^2 - 2*m*X η ∂Qc) + ∫ _η : CountingConfiguration d, m^2 ∂Qc :=
    integral_add (hX2.sub (hX.const_mul (2*m))) (integrable_const (m^2))
  have hsub : (∫ η, X η^2 - 2*m*X η ∂Qc) =
      (∫ η, X η^2 ∂Qc) - ∫ η, 2*m*X η ∂Qc :=
    integral_sub hX2 (hX.const_mul (2*m))
  rw [integral_congr_ae (Eventually.of_forall hpoly), hadd,
    hsub, integral_const_mul, integral_const]
  change ((∫ η, X η^2 ∂Qc) - 2*m*(∫ η, X η ∂Qc)) +
    Qc.real Set.univ • m^2 = _
  rw [show Qc.real Set.univ = 1 by simp [Qc, Measure.real], one_smul,
    hmean, hsecond]
  dsimp only [m]
  ring

private def compactRe (d : ℕ) (f : C_c(Rd d, ℂ)) : C_c(Rd d, ℝ) :=
  ⟨⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩,
    f.hasCompactSupport.comp_left (g := Complex.re) rfl⟩

private def compactIm (d : ℕ) (f : C_c(Rd d, ℂ)) : C_c(Rd d, ℝ) :=
  ⟨⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩,
    f.hasCompactSupport.comp_left (g := Complex.im) rfl⟩

private theorem negativeCompactPairReal_split (d : ℕ)
    (f : C_c(Rd d, ℂ)) (p : Rd d × Rd d) :
    negativeCompactPairReal d f p = realCompactProduct d (compactRe d f) p +
      realCompactProduct d (compactIm d f) p := by
  change (conj (f p.1) * f p.2).re =
    (f p.1).re * (f p.2).re + (f p.1).im * (f p.2).im
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem negativeCompactTest_physical_variance
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (f : C_c(Rd d, ℂ)) :
    Integrable (fun η : CountingConfiguration d =>
      Complex.normSq (negativeCompactTestDiscrepancy d f η))
        (countingLawOfSimple d P) ∧
    (∫ η : CountingConfiguration d,
      Complex.normSq (negativeCompactTestDiscrepancy d f η)
        ∂countingLawOfSimple d P) =
      (∫ p, negativeCompactPairReal d f p ∂originalAdmissibleFactorialMeasure d P hP) +
        (∫ x : Rd d, negativeCompactPairReal d f (x,x) ∂volume) -
          ∫ p : Rd d × Rd d, negativeCompactPairReal d f p ∂volume.prod volume := by
  let fr := compactRe d f
  let fi := compactIm d f
  let Γ := originalAdmissibleFactorialMeasure d P hP
  let Qc := countingLawOfSimple d P
  obtain ⟨hrI, hr⟩ := countingCompact_centered_square d P hP fr
  obtain ⟨hiI, hi⟩ := countingCompact_centered_square d P hP fi
  have hcoord (μ : Measure (Rd d)) [IsFiniteMeasureOnCompacts μ] :
      (∫ x, f x ∂μ).re = ∫ x, fr x ∂μ ∧
        (∫ x, f x ∂μ).im = ∫ x, fi x ∂μ :=
    ⟨(integral_re f.integrable).symm, (integral_im f.integrable).symm⟩
  have hpoint (η : CountingConfiguration d) :
      Complex.normSq (negativeCompactTestDiscrepancy d f η) =
        ((∫ x, fr x ∂η.val) - ∫ x, fr x ∂volume)^2 +
          ((∫ x, fi x ∂η.val) - ∫ x, fi x ∂volume)^2 := by
    simp only [negativeCompactTestDiscrepancy, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, (hcoord η.val).1, (hcoord η.val).2,
      (hcoord volume).1, (hcoord volume).2, pow_two]
  have hΓid : (∫ p, negativeCompactPairReal d f p ∂Γ) =
      (∫ p, realCompactProduct d fr p ∂Γ) + ∫ p, realCompactProduct d fi p ∂Γ :=
    (integral_congr_ae (Eventually.of_forall (negativeCompactPairReal_split d f))).trans
      (integral_add (realCompactProduct d fr).integrable (realCompactProduct d fi).integrable)
  have hdiagid : (∫ x : Rd d, negativeCompactPairReal d f (x,x) ∂volume) =
      (∫ x : Rd d, (fr x)^2 ∂volume) + ∫ x : Rd d, (fi x)^2 ∂volume := by
    calc
      _ = ∫ x : Rd d, (fr x * fr x + fi x * fi x) ∂volume :=
        integral_congr_ae (Eventually.of_forall (fun x => negativeCompactPairReal_split d f (x,x)))
      _ = _ := by
        have hfr : Integrable (fun x : Rd d => fr x * fr x) volume :=
          (countingDiagonalTest d (realCompactProduct d fr)).integrable
        have hfi : Integrable (fun x : Rd d => fi x * fi x) volume :=
          (countingDiagonalTest d (realCompactProduct d fi)).integrable
        rw [integral_add hfr hfi]
        simp only [pow_two]
  have hbackid : (∫ p : Rd d × Rd d, negativeCompactPairReal d f p ∂volume.prod volume) =
      (∫ x, fr x ∂volume)^2 + (∫ x, fi x ∂volume)^2 := by
    calc
      _ = ∫ p : Rd d × Rd d, (fr p.1 * fr p.2 + fi p.1 * fi p.2) ∂volume.prod volume :=
        integral_congr_ae (Eventually.of_forall (negativeCompactPairReal_split d f))
      _ = _ := by
        rw [integral_add (fr.integrable.mul_prod fr.integrable)
          (fi.integrable.mul_prod fi.integrable), integral_prod_mul, integral_prod_mul]
        simp only [pow_two]
  refine ⟨(hrI.add hiI).congr (Eventually.of_forall (fun η => (hpoint η).symm)), ?_⟩
  rw [integral_congr_ae (Eventually.of_forall hpoint), integral_add hrI hiI, hr, hi,
    hΓid, hdiagid, hbackid]
  ring


private theorem compactComplex_finiteSpectrum_fubini
    (d : ℕ) (f : C_c(Rd d, ℂ)) (σ : Measure (Rd d)) [IsFiniteMeasure σ] :
    Integrable (fun k => Complex.normSq (negativeCompactAngularAmplitude d f k)) σ ∧
    Integrable (fun p : Rd d × Rd d =>
      conj (f p.1) * f p.2 * charFun σ (p.2-p.1))
        ((volume : Measure (Rd d)).prod volume) ∧
    Integrable (fun k => (Complex.normSq (negativeCompactAngularAmplitude d f k) : ℂ)) σ ∧
    (∫ p : Rd d × Rd d, conj (f p.1) * f p.2 * charFun σ (p.2-p.1)
      ∂(volume : Measure (Rd d)).prod volume) =
      ∫ k, (Complex.normSq (negativeCompactAngularAmplitude d f k) : ℂ) ∂σ := by
  let Δ : Measure (Rd d × Rd d) := (volume : Measure (Rd d)).prod volume
  let K : (Rd d × Rd d) × Rd d → ℂ := fun q =>
    conj (f q.1.1) * f q.1.2 *
      Complex.exp ((inner ℝ q.2 (q.1.2-q.1.1) : ℂ) * Complex.I)
  have hK : Integrable K (Δ.prod σ) := by
    refine ((f.integrable.norm.mul_prod f.integrable.norm).comp_fst σ).mono'
      (show Continuous K from by fun_prop).aestronglyMeasurable ?_
    exact Eventually.of_forall (fun q => by
      simp only [K, norm_mul, Complex.norm_conj,
        Complex.norm_exp_ofReal_mul_I, mul_one, le_refl])
  have hinner (p : Rd d × Rd d) :
      (∫ k, K (p,k) ∂σ) = conj (f p.1) * f p.2 * charFun σ (p.2-p.1) := by
    dsimp only [K]
    rw [integral_const_mul, ← charFun_apply]
  have hpair (k : Rd d) :
      (∫ p, K (p,k) ∂Δ) =
        (Complex.normSq (negativeCompactAngularAmplitude d f k) : ℂ) :=
    negativeCompactAngularAmplitude_pair d f k
  have hleft : Integrable (fun p : Rd d × Rd d =>
      conj (f p.1) * f p.2 * charFun σ (p.2-p.1)) Δ :=
    hK.integral_prod_left.congr (Eventually.of_forall hinner)
  have hright : Integrable (fun k =>
      (Complex.normSq (negativeCompactAngularAmplitude d f k) : ℂ)) σ :=
    hK.integral_prod_right.congr (Eventually.of_forall hpair)
  have hswap :
      (∫ p : Rd d × Rd d, (∫ k, K (p,k) ∂σ) ∂Δ) =
        ∫ k, (∫ p : Rd d × Rd d, K (p,k) ∂Δ) ∂σ :=
    integral_integral_swap (μ := Δ) (ν := σ)
      (f := fun p k => K (p,k)) hK
  refine ⟨?_, hleft, hright, ?_⟩
  · have hrightre : Integrable (fun k =>
        ((Complex.normSq (negativeCompactAngularAmplitude d f k) : ℂ)).re) σ := hright.re
    simpa only [Complex.ofReal_re] using hrightre
  · exact (integral_congr_ae (Eventually.of_forall hinner)).symm.trans
      (hswap.trans (integral_congr_ae (Eventually.of_forall hpair)))

private theorem negativeCompactTest_heatSpectrum_integral
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (f : C_c(Rd d, ℂ)) (t : ℝ) (ht : 0 < t) :
    Integrable (fun p : Rd d × Rd d => negativeCompactPairReal d f p *
      originalHeatCovariance d P t (p.2-p.1)) (volume.prod volume) ∧
    Integrable (fun k => Complex.normSq (negativeCompactAngularAmplitude d f k))
      (originalHeatSpectrumGeneral d s hs P hP hW t ht : Measure (Rd d)) ∧
    (∫ p : Rd d × Rd d, negativeCompactPairReal d f p *
      originalHeatCovariance d P t (p.2-p.1) ∂volume.prod volume) =
      ∫ k, Complex.normSq (negativeCompactAngularAmplitude d f k)
        ∂(originalHeatSpectrumGeneral d s hs P hP hW t ht : Measure (Rd d)) := by
  let σ : Measure (Rd d) := originalHeatSpectrumGeneral d s hs P hP hW t ht
  obtain ⟨hI, hleft, hright, heq⟩ := compactComplex_finiteSpectrum_fubini d f σ
  have hpoint (p : Rd d × Rd d) :
      (conj (f p.1) * f p.2 * charFun σ (p.2-p.1)).re =
        negativeCompactPairReal d f p * originalHeatCovariance d P t (p.2-p.1) := by
    dsimp only [σ]
    rw [charFun_originalHeatSpectrumGeneral]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rfl
  refine ⟨hleft.re.congr (Eventually.of_forall hpoint), hI, ?_⟩
  calc
    _ = ∫ p : Rd d × Rd d,
        (conj (f p.1) * f p.2 * charFun σ (p.2-p.1)).re ∂volume.prod volume :=
      integral_congr_ae (Eventually.of_forall (fun p => (hpoint p).symm))
    _ = (∫ p : Rd d × Rd d,
        conj (f p.1) * f p.2 * charFun σ (p.2-p.1) ∂volume.prod volume).re :=
      integral_re hleft
    _ = (∫ k, (Complex.normSq (negativeCompactAngularAmplitude d f k) : ℂ) ∂σ).re :=
      congrArg Complex.re heq
    _ = _ := by
      have hr : (∫ k, (Complex.normSq (negativeCompactAngularAmplitude d f k) : ℂ) ∂σ).re =
          ∫ k, ((Complex.normSq (negativeCompactAngularAmplitude d f k) : ℂ)).re ∂σ :=
        (integral_re hright).symm
      simpa only [Complex.ofReal_re] using hr

private theorem negativeCompactTest_angularSpectrum_lintegral
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (f : C_c(Rd d, ℂ)) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (∫ p : Rd d × Rd d, negativeCompactPairReal d f p *
      originalHeatCovariance d P t (p.2-p.1) ∂volume.prod volume) =
      ∫⁻ k, heatSpectralWeight d t k * ENNReal.ofReal
        (Complex.normSq (negativeCompactAngularAmplitude d f k))
          ∂originalAngularSpectrumGeneral d s hs P hP hW := by
  have hJ : Measurable (fun k => ENNReal.ofReal
      (Complex.normSq (negativeCompactAngularAmplitude d f k))) :=
    (Complex.continuous_normSq.measurable.comp
      (measurable_negativeCompactAngularAmplitude d f)).ennreal_ofReal
  refine Eq.trans ?_ (lintegral_withDensity_eq_lintegral_mul
    (originalAngularSpectrumGeneral d s hs P hP hW) (measurable_heatSpectralWeight d t) hJ)
  rw [originalAngularSpectrumGeneral_withDensity_eq_heatSpectrum d s hs P hP hW t ht]
  obtain ⟨_, hI, heq⟩ := negativeCompactTest_heatSpectrum_integral d s hs P hP hW f t ht
  exact (congrArg ENNReal.ofReal heq).trans
    (ofReal_integral_eq_lintegral_ofReal hI
      (Eventually.of_forall (fun _ => Complex.normSq_nonneg _)))

/-- Actual compact complex-test variance under the original common spectrum. -/
theorem originalAngularSpectrumGeneral_compact_test_variance
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (f : C_c(Rd d, ℂ)) :
    Integrable (fun η : CountingConfiguration d =>
      Complex.normSq (negativeCompactTestDiscrepancy d f η))
        (countingLawOfSimple d P) ∧
    (∫⁻ k, ENNReal.ofReal (Complex.normSq (negativeCompactAngularAmplitude d f k))
      ∂originalAngularSpectrumGeneral d s hs P hP hW) ≠ ∞ ∧
    Integrable (fun k => Complex.normSq (negativeCompactAngularAmplitude d f k))
      (originalAngularSpectrumGeneral d s hs P hP hW) ∧
    ENNReal.ofReal (∫ η : CountingConfiguration d,
      Complex.normSq (negativeCompactTestDiscrepancy d f η) ∂countingLawOfSimple d P) =
        ∫⁻ k, ENNReal.ofReal (Complex.normSq (negativeCompactAngularAmplitude d f k))
          ∂originalAngularSpectrumGeneral d s hs P hP hW ∧
    (∫ η : CountingConfiguration d,
      Complex.normSq (negativeCompactTestDiscrepancy d f η) ∂countingLawOfSimple d P) =
        ∫ k, Complex.normSq (negativeCompactAngularAmplitude d f k)
          ∂originalAngularSpectrumGeneral d s hs P hP hW := by
  obtain ⟨hvar, hphysicalEq⟩ := negativeCompactTest_physical_variance d P hP f
  let ρ := originalAngularSpectrumGeneral d s hs P hP hW
  let J : Rd d → ℝ≥0∞ := fun k => ENNReal.ofReal
    (Complex.normSq (negativeCompactAngularAmplitude d f k))
  let v : ℝ := ∫ η : CountingConfiguration d,
    Complex.normSq (negativeCompactTestDiscrepancy d f η) ∂countingLawOfSimple d P
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let T : ℕ → ℝ := fun n => ∫ p : Rd d × Rd d, negativeCompactPairReal d f p *
    originalHeatCovariance d P ((ε n)^2) (p.2-p.1) ∂volume.prod volume
  have hεpos (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hJ : Measurable J :=
    (Complex.continuous_normSq.measurable.comp
      (measurable_negativeCompactAngularAmplitude d f)).ennreal_ofReal
  have hphysical := (compactPair_covariance_tendsto_of_neg_two_lt
    d s hs P hP hW (negativeCompactPairReal d f) ε hεpos hε).2
  rw [← hphysicalEq] at hphysical
  have hphysical' : Tendsto T atTop (𝓝 v) := hphysical
  have hvalue : (∫⁻ k, J k ∂ρ) = ENNReal.ofReal v :=
    tendsto_nhds_unique
      (angularHead_heatWeight_sq_lintegral_tendsto d ρ J hJ
        (fun _ => ENNReal.ofReal_ne_top))
      ((ENNReal.tendsto_ofReal hphysical').congr' (Eventually.of_forall (fun n =>
        negativeCompactTest_angularSpectrum_lintegral d s hs P hP hW f
          ((ε n)^2) (sq_pos_of_pos (hεpos n)))))
  have hfinite : (∫⁻ k, J k ∂ρ) ≠ ∞ := hvalue.trans_ne ENNReal.ofReal_ne_top
  have hI : Integrable (fun k => Complex.normSq (negativeCompactAngularAmplitude d f k)) ρ :=
    (integrable_toReal_of_lintegral_ne_top hJ.aemeasurable hfinite).congr
      (Eventually.of_forall (fun k => ENNReal.toReal_ofReal (Complex.normSq_nonneg _)))
  have hv : 0 ≤ v := integral_nonneg (fun _ => Complex.normSq_nonneg _)
  have hreal : v = ∫ k, Complex.normSq (negativeCompactAngularAmplitude d f k) ∂ρ := by
    calc
      _ = (ENNReal.ofReal v).toReal := (ENNReal.toReal_ofReal hv).symm
      _ = (∫⁻ k, J k ∂ρ).toReal := congrArg ENNReal.toReal hvalue.symm
      _ = ∫ k, (J k).toReal ∂ρ :=
        (integral_toReal hJ.aemeasurable (ae_lt_top hJ hfinite)).symm
      _ = _ := integral_congr_ae (Eventually.of_forall
        (fun k => ENNReal.toReal_ofReal (Complex.normSq_nonneg _)))
  exact ⟨hvar, hfinite, hI, hvalue.symm, hreal⟩

theorem originalAngularSpectrumGeneral_compact_test_nn_variance
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (f : C_c(Rd d, ℂ)) :
    (∫⁻ η : CountingConfiguration d,
      ENNReal.ofReal (Complex.normSq (negativeCompactTestDiscrepancy d f η))
        ∂countingLawOfSimple d P) =
      ∫⁻ k, ENNReal.ofReal (Complex.normSq (negativeCompactAngularAmplitude d f k))
        ∂originalAngularSpectrumGeneral d s hs P hP hW := by
  have h := originalAngularSpectrumGeneral_compact_test_variance d s hs P hP hW f
  exact (ofReal_integral_eq_lintegral_ofReal h.1
    (Eventually.of_forall (fun _ => Complex.normSq_nonneg _))).symm.trans h.2.2.2.1

end Riesz.Stationary

