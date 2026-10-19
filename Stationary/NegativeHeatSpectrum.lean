import Riesz.Stationary.NegativeDisplacement
import Riesz.Stationary.AngularMellinEstimates

/-! The original simple law's heat spectrum from finite energy at any exponent above -2. -/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration Set
open scoped ENNReal Classical Topology RealInnerProductSpace InnerProductSpace

namespace Riesz.Stationary

theorem continuous_originalHeatCovariance_of_Q_ne_top
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t)
    (hQt : Q d P (1 / (8 * t)) ≠ ∞)
    (hQ2t : Q d P (1 / (8 * (2 * t))) ≠ ∞) :
    Continuous (originalHeatCovariance d P t) := by
  letI : IsProbabilityMeasure P := hP.1
  refine continuous_iff_continuousAt.mpr (fun a => ?_)
  let Y : Measure (Rd d) → ℝ := fun μ => (originalHeatMass d (2 * t) a μ).toReal
  let D : ℝ := (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) /
    (4 * Real.pi * (2 * t)) ^ (-((d : ℝ) / 2)) * Real.exp (1 / (4 * t))
  have hD : 0 ≤ D := by positivity
  have hY : MemLp Y 2 P :=
    originalHeatMass_memLp_two d P hP (2 * t) (by positivity) a hQ2t
  have hF0 : MemLp (originalHeatField d t 0) 2 P :=
    originalHeatField_memLp_two d P hP t ht 0 hQt
  have hBound : Integrable (fun μ => ‖originalHeatField d t 0 μ‖ * (D * Y μ + 1)) P :=
    hF0.norm.integrable_mul ((hY.const_mul D).add (memLp_const (1 : ℝ)))
  have hYfinite : ∀ᵐ μ ∂P, originalHeatMass d (2 * t) a μ < ∞ :=
    ae_lt_top (measurable_originalHeatMass d (2 * t) a)
      ((lintegral_originalHeatMass d P hP (2 * t) (by positivity) a).trans_ne ENNReal.one_ne_top)
  have hZle (b : Rd d) (hb : ‖b - a‖ ≤ 1) (μ : Measure (Rd d)) :
      originalHeatMass d t b μ ≤ ENNReal.ofReal D * originalHeatMass d (2 * t) a μ :=
    (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal
      (originalHeatGaussian_le_wideGaussian_of_norm_sub_le_one d t ht a b x hb))).trans_eq
        ((lintegral_congr (fun x => ENNReal.ofReal_mul
          (p := D) (q := originalHeatGaussian d (2 * t) (a - x)) hD)).trans
            (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top))
  refine continuousAt_of_dominated
    (F := fun b μ => originalHeatField d t 0 μ * originalHeatField d t b μ)
    (bound := fun μ => ‖originalHeatField d t 0 μ‖ * (D * Y μ + 1)) ?_ ?_ hBound ?_
  case refine_2 =>
    filter_upwards [Metric.ball_mem_nhds a (show (0 : ℝ) < 1 by norm_num)] with b hb
    have hba : ‖b - a‖ ≤ 1 := le_of_lt
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hb)
    filter_upwards [hYfinite] with μ hμ
    have hXle : (originalHeatMass d t b μ).toReal ≤ D * Y μ :=
      (by simpa only [Y, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD] using
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ.ne) (hZle b hba μ))
    have hFb : ‖originalHeatField d t b μ‖ ≤ D * Y μ + 1 :=
      (show ‖(originalHeatMass d t b μ).toReal - 1‖ ≤
          (originalHeatMass d t b μ).toReal + 1 from by
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ (originalHeatMass d t b μ).toReal from ENNReal.toReal_nonneg),
          abs_one] using norm_sub_le (originalHeatMass d t b μ).toReal (1 : ℝ)).trans
            (add_le_add hXle le_rfl)
    exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left hFb (norm_nonneg _))
  case refine_1 =>
    exact Eventually.of_forall (fun b =>
      ((measurable_originalHeatField d t 0).mul
        (measurable_originalHeatField d t b)).aestronglyMeasurable)
  exact (ae_continuousAt_originalHeatMass_toReal d P hP t ht a).mono
    (fun μ hμ => continuousAt_const.mul (hμ.sub continuousAt_const))

theorem positiveDefinite_originalHeatCovariance_of_Q_ne_top
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (hQt : Q d P (1 / (8 * t)) ≠ ∞) :
    IsPositiveDefinite (fun z => (originalHeatCovariance d P t z : ℂ)) := by
  refine ⟨fun z => ?_, fun m x c => ?_⟩
  case refine_2 =>
    have hLp (a : Rd d) : MemLp (originalHeatField d t a) 2 P :=
      originalHeatField_memLp_two d P hP t ht a hQt
    have hsum (a : Fin m → ℂ) :
        (∑ i, ∑ j, starRingEnd ℂ (a i) * a j) =
          (Complex.normSq (∑ k, a k) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
    have hC (i j : Fin m) :
        (originalHeatCovariance d P t (x i - x j) : ℂ) =
          ∫ μ, ((originalHeatField d t (x i) μ * originalHeatField d t (x j) μ : ℝ) : ℂ) ∂P :=
      (congrArg Complex.ofReal
        (integral_originalHeatField_mul_eq_covariance d P hP t (x j) (x i)).symm).trans
          ((congrArg Complex.ofReal (integral_congr_ae
            (Eventually.of_forall (fun μ => mul_comm _ _)))).trans
              (integral_complex_ofReal).symm)
    have hterm (i j : Fin m) : Integrable (fun μ => starRingEnd ℂ (c i) * c j *
        ((originalHeatField d t (x i) μ * originalHeatField d t (x j) μ : ℝ) : ℂ)) P :=
      (((hLp (x i)).integrable_mul (hLp (x j))).ofReal).const_mul _
    have hpoint (μ : Measure (Rd d)) :
        (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
          ((originalHeatField d t (x i) μ * originalHeatField d t (x j) μ : ℝ) : ℂ)) =
            (Complex.normSq (∑ k, c k * (originalHeatField d t (x k) μ : ℂ)) : ℂ) := by
      simpa only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul,
        mul_assoc, mul_left_comm, mul_comm] using
          hsum (fun k => c k * (originalHeatField d t (x k) μ : ℂ))
    have hcomplex :
        (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
          (originalHeatCovariance d P t (x i - x j) : ℂ)) =
            ∫ μ, (Complex.normSq (∑ k, c k * (originalHeatField d t (x k) μ : ℂ)) : ℂ) ∂P :=
      (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        (congrArg (fun z : ℂ => starRingEnd ℂ (c i) * c j * z) (hC i j)).trans
          (integral_const_mul _ _).symm))).trans
            ((Finset.sum_congr rfl (fun i _ =>
              (integral_finsetSum _ (fun j _ => hterm i j)).symm)).trans
                ((integral_finsetSum _ (fun i _ =>
                  integrable_finsetSum _ (fun j _ => hterm i j))).symm.trans
                    (integral_congr_ae (Eventually.of_forall hpoint))))
    simpa only [hcomplex, integral_complex_ofReal, Complex.ofReal_re] using
      integral_nonneg (μ := P) (fun μ =>
        Complex.normSq_nonneg (∑ k, c k * (originalHeatField d t (x k) μ : ℂ)))
  exact (congrArg Complex.ofReal (originalHeatCovariance_neg d P hP t z)).trans
    (by simp)

def originalHeatSpectrumGeneral
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    FiniteMeasure (Rd d) :=
  Classical.choose (exists_finiteMeasure_charFun_of_real_continuous_pd d
    (originalHeatCovariance d P t)
    (continuous_originalHeatCovariance_of_Q_ne_top d P hP t ht
      (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs P hW _ (by positivity))
      (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs P hW _ (by positivity)))
    (positiveDefinite_originalHeatCovariance_of_Q_ne_top d P hP t ht
      (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs P hW _ (by positivity))))

theorem charFun_originalHeatSpectrumGeneral
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t)
    (z : Rd d) :
    charFun (originalHeatSpectrumGeneral d s hs P hP hW t ht : Measure (Rd d)) z =
      (originalHeatCovariance d P t z : ℂ) :=
  Classical.choose_spec (exists_finiteMeasure_charFun_of_real_continuous_pd d
    (originalHeatCovariance d P t)
    (continuous_originalHeatCovariance_of_Q_ne_top d P hP t ht
      (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs P hW _ (by positivity))
      (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs P hW _ (by positivity)))
    (positiveDefinite_originalHeatCovariance_of_Q_ne_top d P hP t ht
      (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs P hW _ (by positivity)))) z

theorem mass_originalHeatSpectrumGeneral
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    (originalHeatSpectrumGeneral d s hs P hP hW t ht : Measure (Rd d)) univ =
      ENNReal.ofReal (originalHeatCovariance d P t 0) := by
  have hreal :
      (originalHeatSpectrumGeneral d s hs P hP hW t ht : Measure (Rd d)).real univ =
        originalHeatCovariance d P t 0 :=
    congrArg Complex.re ((charFun_zero _).symm.trans
      (charFun_originalHeatSpectrumGeneral d s hs P hP hW t ht 0))
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm.trans
    (congrArg ENNReal.ofReal hreal)

theorem originalHeatSpectrumGeneral_add_eq_withDensity
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (t h : ℝ) (ht : 0 < t) (hh : 0 < h) :
    (originalHeatSpectrumGeneral d s hs P hP hW (t + h) (add_pos ht hh) : Measure (Rd d)) =
      (originalHeatSpectrumGeneral d s hs P hP hW t ht : Measure (Rd d)).withDensity
        (heatSpectralWeight d h) := by
  letI : IsFiniteMeasure
      ((originalHeatSpectrumGeneral d s hs P hP hW t ht : Measure (Rd d)).withDensity
        (heatSpectralWeight d h)) :=
    isFiniteMeasure_withDensity_heatSpectralWeight d _ h hh.le
  refine Measure.ext_of_charFun (funext (fun z => ?_))
  rw [charFun_originalHeatSpectrumGeneral,
    show heatSpectralWeight d h =
      (fun k : Rd d => ENNReal.ofReal (Real.exp (-(2 * h) * ‖k‖ ^ 2))) from rfl,
    charFun_heatWeighted_eq_heatConvolution d _ (2 * h) (by positivity) z]
  simp_rw [charFun_originalHeatSpectrumGeneral, ← Complex.ofReal_mul]
  exact (congrArg Complex.ofReal
    (originalHeatCovariance_eq_convolution_of_Q_ne_top d P hP t h ht hh
      (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs P hW _ (by positivity))
      (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs P hW _ (by positivity)) z).2).trans
        integral_complex_ofReal.symm

def originalAngularSpectrumGeneral
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) : Measure (Rd d) :=
  (originalHeatSpectrumGeneral d s hs P hP hW 1 (by norm_num) : Measure (Rd d)).withDensity
    (heatSpectralWeight d (-1))

instance instSigmaFiniteOriginalAngularSpectrumGeneral
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    SigmaFinite (originalAngularSpectrumGeneral d s hs P hP hW) :=
  SigmaFinite.withDensity_ofReal
    (μ := (originalHeatSpectrumGeneral d s hs P hP hW 1 (by norm_num) : Measure (Rd d)))
    (fun k : Rd d => Real.exp (-(2 * (-1 : ℝ)) * ‖k‖ ^ 2))

instance instIsLocallyFiniteMeasureOriginalAngularSpectrumGeneral
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    IsLocallyFiniteMeasure (originalAngularSpectrumGeneral d s hs P hP hW) :=
  IsLocallyFiniteMeasure.withDensity_ofReal
    (μ := (originalHeatSpectrumGeneral d s hs P hP hW 1 (by norm_num) : Measure (Rd d)))
    (f := fun k : Rd d => Real.exp (-(2 * (-1 : ℝ)) * ‖k‖ ^ 2)) (by fun_prop)

theorem originalAngularSpectrumGeneral_withDensity_eq_heatSpectrum
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    (originalAngularSpectrumGeneral d s hs P hP hW).withDensity (heatSpectralWeight d t) =
      (originalHeatSpectrumGeneral d s hs P hP hW t ht : Measure (Rd d)) := by
  have hcommon :
      (originalHeatSpectrumGeneral d s hs P hP hW t ht : Measure (Rd d)).withDensity
          (heatSpectralWeight d 1) =
        (originalHeatSpectrumGeneral d s hs P hP hW 1 (by norm_num) : Measure (Rd d)).withDensity
          (heatSpectralWeight d t) :=
    (originalHeatSpectrumGeneral_add_eq_withDensity d s hs P hP hW t 1 ht (by norm_num)).symm.trans
      (by simpa only [add_comm t 1] using
        (originalHeatSpectrumGeneral_add_eq_withDensity d s hs P hP hW 1 t (by norm_num) ht))
  simpa only [originalAngularSpectrumGeneral, withDensity_heatSpectralWeight_add,
    show t + -1 = -1 + t by ring, show (1 : ℝ) + -1 = 0 by norm_num,
    heatSpectralWeight_zero, withDensity_one] using
      congrArg (fun μ : Measure (Rd d) => μ.withDensity (heatSpectralWeight d (-1))) hcommon.symm

theorem lintegral_originalAngularSpectrumGeneral_heatSpectralWeight
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    (∫⁻ k, heatSpectralWeight d t k ∂originalAngularSpectrumGeneral d s hs P hP hW) =
      ENNReal.ofReal (originalHeatCovariance d P t 0) := by
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using
    (congrArg (fun μ : Measure (Rd d) => μ univ)
      (originalAngularSpectrumGeneral_withDensity_eq_heatSpectrum d s hs P hP hW t ht)).trans
        (mass_originalHeatSpectrumGeneral d s hs P hP hW t ht)

theorem lintegral_originalAngularSpectrumGeneral_heatSpectralWeight_eq
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    (∫⁻ k, heatSpectralWeight d t k ∂originalAngularSpectrumGeneral d s hs P hP hW) =
      ENNReal.ofReal ((8 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
        ((Q d P (1 / (8 * t))).toReal + 1) - 1) :=
  (lintegral_originalAngularSpectrumGeneral_heatSpectralWeight d s hs P hP hW t ht).trans
    (congrArg ENNReal.ofReal (originalHeatCovariance_zero d P hP t ht
      (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs P hW _ (by positivity))))

theorem originalHeatSpectrumGeneral_eq_of_exponent
    (d : ℕ) (s r : ℝ) (hs : -2 < s) (hr : -2 < r) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hWs : W d s P ≠ ⊤) (hWr : W d r P ≠ ⊤)
    (t : ℝ) (ht : 0 < t) :
    originalHeatSpectrumGeneral d s hs P hP hWs t ht =
      originalHeatSpectrumGeneral d r hr P hP hWr t ht := rfl

theorem originalAngularSpectrumGeneral_eq_of_exponent
    (d : ℕ) (s r : ℝ) (hs : -2 < s) (hr : -2 < r) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hWs : W d s P ≠ ⊤) (hWr : W d r P ≠ ⊤) :
    originalAngularSpectrumGeneral d s hs P hP hWs =
      originalAngularSpectrumGeneral d r hr P hP hWr := rfl

theorem originalHeatSpectrumGeneral_eq_positive
    (d : ℕ) (s : ℝ) (hs : -2 < s) (hspos : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    originalHeatSpectrumGeneral d s hs P hP hW t ht =
      originalHeatSpectrum d s hspos P hP hW t ht := rfl

theorem originalAngularSpectrumGeneral_eq_positive
    (d : ℕ) (s : ℝ) (hs : -2 < s) (hspos : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    originalAngularSpectrumGeneral d s hs P hP hW =
      originalAngularSpectrum d s hspos P hP hW := rfl

theorem lintegral_generalAngularSpectrum_originalHeatGaussian
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) {u : ℝ} (hu : 0 < u) :
    (∫⁻ k, ENNReal.ofReal (originalHeatGaussian d u k)
      ∂originalAngularSpectrumGeneral d s hs P hP hW) =
      ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
        ENNReal.ofReal ((Q d P u).toReal + 1 - B d u) := by
  let ρ := originalAngularSpectrumGeneral d s hs P hP hW
  let A : ℝ := (2 * Real.pi) ^ d
  let κ : ℝ := (4 * Real.pi * u) ^ (-((d : ℝ) / 2))
  let v : ℝ := 1 / (8 * u)
  have hA : 0 < A := pow_pos (by positivity) _
  have hκ : 0 < κ := Real.rpow_pos_of_pos (by positivity) _
  have hB : 0 < B d u := Real.rpow_pos_of_pos (div_pos Real.pi_pos hu) _
  have hv : 0 < v := one_div_pos.mpr (by positivity)
  have hvar : 1 / (8 * v) = u := by
    dsimp only [v]
    field_simp [hu.ne']
  have hvbase : 8 * Real.pi * v = Real.pi / u := by
    dsimp only [v]
    field_simp [hu.ne']
  have htrace := lintegral_originalAngularSpectrumGeneral_heatSpectralWeight_eq
    d s hs P hP hW v hv
  rw [hvbase, hvar, Real.rpow_neg (div_pos Real.pi_pos hu).le] at htrace
  change (∫⁻ k, heatSpectralWeight d v k ∂ρ) =
    ENNReal.ofReal ((B d u)⁻¹ * ((Q d P u).toReal + 1) - 1) at htrace
  have hg (k : Rd d) : ENNReal.ofReal (originalHeatGaussian d u k) =
      ENNReal.ofReal κ * heatSpectralWeight d v k := by
    change ENNReal.ofReal (κ * Real.exp (-(1 / (4 * u)) * ‖k‖ ^ 2)) =
      ENNReal.ofReal κ * ENNReal.ofReal (Real.exp (-(2 * v) * ‖k‖ ^ 2))
    rw [ENNReal.ofReal_mul hκ.le]
    congr 3
    dsimp only [v]
    field_simp [hu.ne']
    ring
  have hAκ : A * κ = B d u := angularGaussian_normalization d hu
  have hκeq : κ = A⁻¹ * B d u := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul] using
      congrArg (fun z : ℝ => A⁻¹ * z) hAκ
  simp_rw [hg]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htrace,
    ← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_mul (inv_nonneg.mpr hA.le)]
  congr 1
  rw [hκeq]
  field_simp [hA.ne', hB.ne']

theorem W_eq_weighted_covariance_profile_neg
    (d : ℕ) (s : ℝ) (hd : 2 ≤ d) (hs : -2 < s) (hsneg : s < 0)
    (P : ConfigurationLaw d) (hW : W d s P ≠ ⊤) :
    W d s P = ((ENNReal.ofReal (gamma_s s) *
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) *
        ENNReal.ofReal ((Q d P u).toReal + 1 - B d u)) : ℝ≥0∞) := by
  rw [W_eq_weighted_truncated_profile_neg d s hd hs hsneg P hW]
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _)]

def fullAngularMellinKernel (d : ℕ) (s : ℝ) (k : Rd d) : ℝ≥0∞ :=
  ∫⁻ u in Ioi (0 : ℝ), angularHeadBaseNN d s (u, k)

def negativeAngularEnergyKernel (d : ℕ) (s : ℝ) (k : Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (gamma_s s) * ENNReal.ofReal ((2 * Real.pi) ^ d) *
    fullAngularMellinKernel d s k

theorem measurable_fullAngularMellinKernel (d : ℕ) (s : ℝ) :
    Measurable (fullAngularMellinKernel d s) :=
  (measurable_angularHeadBaseNN d s).lintegral_prod_left'
    (μ := volume.restrict (Ioi (0 : ℝ)))

theorem measurable_negativeAngularEnergyKernel (d : ℕ) (s : ℝ) :
    Measurable (negativeAngularEnergyKernel d s) :=
  show Measurable (fun k : Rd d => ENNReal.ofReal (gamma_s s) *
    ENNReal.ofReal ((2 * Real.pi) ^ d) * fullAngularMellinKernel d s k) from
      (measurable_const.mul measurable_const).mul (measurable_fullAngularMellinKernel d s)

theorem fullAngularMellinKernel_zero (d : ℕ) {s : ℝ} (hsd : s < (d : ℝ)) :
    fullAngularMellinKernel d s (0 : Rd d) = ∞ := by
  apply top_unique
  exact (angularMellinKernel_zero d hsd).symm.le.trans
    (lintegral_mono_set (fun _ hu => hu.1))

theorem negativeAngularEnergyKernel_zero
    (d : ℕ) (s : ℝ) (hs : -2 < s) (hsd : s < (d : ℝ)) :
    negativeAngularEnergyKernel d s (0 : Rd d) = ∞ := by
  have hC : ENNReal.ofReal (gamma_s s) *
      ENNReal.ofReal ((2 * Real.pi) ^ d) ≠ 0 :=
    mul_ne_zero
      (ENNReal.ofReal_ne_zero_iff.mpr (Riesz.Analysis.gamma_s_pos s hs))
      (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (by positivity) d))
  rw [negativeAngularEnergyKernel, fullAngularMellinKernel_zero d hsd,
    ENNReal.mul_top hC]

theorem negative_generalAngular_weighted_mass
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : -2 < s) (hsneg : s < 0)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    let ρ := originalAngularSpectrumGeneral d s hs P hP hW
    W d s P = ((∫⁻ k, negativeAngularEnergyKernel d s k ∂ρ) : EReal) ∧
    (∫⁻ k, negativeAngularEnergyKernel d s k ∂ρ) ≠ ∞ ∧
    (∀ᵐ k ∂ρ, k ≠ 0) ∧
    IsFiniteMeasure (ρ.withDensity (negativeAngularEnergyKernel d s)) := by
  let ρ := originalAngularSpectrumGeneral d s hs P hP hW
  let A : ℝ := (2 * Real.pi) ^ d
  let I : ℝ≥0∞ := ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) *
    ENNReal.ofReal ((Q d P u).toReal + 1 - B d u)
  have hA : 0 < A := pow_pos (by positivity) d
  have hAA : ENNReal.ofReal A * ENNReal.ofReal A⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hA.le, mul_inv_cancel₀ hA.ne', ENNReal.ofReal_one]
  have hswap :
      (∫⁻ k, ∫⁻ u in Ioi (0 : ℝ), angularHeadBaseNN d s (u, k) ∂volume ∂ρ) =
        ∫⁻ u in Ioi (0 : ℝ), ∫⁻ k, angularHeadBaseNN d s (u, k) ∂ρ :=
    lintegral_lintegral_swap
      (μ := ρ) (ν := volume.restrict (Ioi (0 : ℝ)))
      (f := fun k u => angularHeadBaseNN d s (u, k))
      ((measurable_angularHeadBaseNN d s).comp measurable_swap).aemeasurable
  have hM : (∫⁻ k, fullAngularMellinKernel d s k ∂ρ) = ENNReal.ofReal A⁻¹ * I := by
    refine hswap.trans ?_
    simp_rw [angularHeadBaseNN, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine Eq.trans ?_ (lintegral_const_mul'
      (μ := volume.restrict (Ioi (0 : ℝ))) (ENNReal.ofReal A⁻¹)
      (fun u : ℝ => ENNReal.ofReal (u ^ (s / 2 - 1)) *
        ENNReal.ofReal ((Q d P u).toReal + 1 - B d u)) ENNReal.ofReal_ne_top)
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [lintegral_generalAngularSpectrum_originalHeatGaussian d s hs P hP hW hu]
    dsimp only [A]
    ac_rfl
  have hN : (∫⁻ k, negativeAngularEnergyKernel d s k ∂ρ) =
      ENNReal.ofReal (gamma_s s) * I := by
    simp only [negativeAngularEnergyKernel]
    rw [lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), hM]
    change ENNReal.ofReal (gamma_s s) * ENNReal.ofReal A *
      (ENNReal.ofReal A⁻¹ * I) = ENNReal.ofReal (gamma_s s) * I
    rw [mul_assoc, ← mul_assoc (ENNReal.ofReal A) (ENNReal.ofReal A⁻¹), hAA, one_mul]
  have hWeq : W d s P = ((∫⁻ k, negativeAngularEnergyKernel d s k ∂ρ) : EReal) :=
    (W_eq_weighted_covariance_profile_neg d s hd hs hsneg P hW).trans
      (congrArg (fun z : ℝ≥0∞ => (z : EReal)) hN).symm
  have hfin : (∫⁻ k, negativeAngularEnergyKernel d s k ∂ρ) ≠ ∞ := by
    intro htop
    exact hW (hWeq.trans ((congrArg (fun z : ℝ≥0∞ => (z : EReal)) htop).trans
      EReal.coe_ennreal_top))
  have hzero : ∀ᵐ k ∂ρ, k ≠ 0 := by
    filter_upwards [ae_lt_top (measurable_negativeAngularEnergyKernel d s) hfin] with k hk
    exact fun hz => (ne_of_lt hk) ((congrArg (negativeAngularEnergyKernel d s) hz).trans
      (negativeAngularEnergyKernel_zero d s hs (hsneg.trans_le (Nat.cast_nonneg d))))
  exact ⟨hWeq, hfin, hzero, isFiniteMeasure_withDensity hfin⟩

def negativeAngularWeightedMeasure
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : -2 < s) (hsneg : s < 0)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    FiniteMeasure (Rd d) :=
  ⟨(originalAngularSpectrumGeneral d s hs P hP hW).withDensity
      (negativeAngularEnergyKernel d s),
    (negative_generalAngular_weighted_mass d hd s hs hsneg P hP hW).2.2.2⟩

theorem ae_ne_zero_originalAngularSpectrumGeneral
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : -2 < s) (hsneg : s < 0)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    ∀ᵐ k ∂originalAngularSpectrumGeneral d s hs P hP hW, k ≠ 0 :=
  (negative_generalAngular_weighted_mass d hd s hs hsneg P hP hW).2.2.1

theorem real_mass_negativeAngularWeightedMeasure
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : -2 < s) (hsneg : s < 0)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    (negativeAngularWeightedMeasure d hd s hs hsneg P hP hW : Measure (Rd d)).real univ =
      (W d s P).toReal := by
  have h := congrArg EReal.toReal
    (negative_generalAngular_weighted_mass d hd s hs hsneg P hP hW).1
  change ((originalAngularSpectrumGeneral d s hs P hP hW).withDensity
    (negativeAngularEnergyKernel d s)).real univ = (W d s P).toReal
  simpa only [Measure.real, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, EReal.toReal_coe_ennreal] using h.symm

theorem fullAngularMellinKernel_eq_radial
    (d : ℕ) (s : ℝ) (hsd : s < (d : ℝ)) {k : Rd d} (hk : k ≠ 0) :
    fullAngularMellinKernel d s k =
      ENNReal.ofReal ((angularMellinPrefactor d * (4 : ℝ) ^ (angularMellinOrder d s) *
        Real.Gamma (angularMellinOrder d s)) * ‖k‖ ^ (-((d : ℝ) - s))) := by
  have hp : 0 < angularMellinOrder d s := div_pos (sub_pos.mpr hsd) (by norm_num)
  have hb : 0 < ‖k‖ ^ 2 / 4 :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr hk)) (by norm_num)
  have hi := angularMellin_density_integrable d hsd hk
  have hn : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ angularMellinPrefactor d *
      (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(‖k‖ ^ 2 / 4) / u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (angularMellinPrefactor_pos d).le
      (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)
  have heq : fullAngularMellinKernel d s k = ∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (angularMellinPrefactor d *
        (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(‖k‖ ^ 2 / 4) / u))) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [angularHeadBaseNN, ← ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _),
      angularMellin_integrand_eq_density d s hu k]
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal hi hn, integral_const_mul,
    integral_angular_reciprocal_mellin hp hb,
    angular_reciprocal_radial_eq (angularMellinOrder d s) (norm_pos_iff.mpr hk)]
  congr 1
  have horder : 2 * angularMellinOrder d s = (d : ℝ) - s := by
    dsimp only [angularMellinOrder]
    ring
  rw [horder]
  ring

end Riesz.Stationary
