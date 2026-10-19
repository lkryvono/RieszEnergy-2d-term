import Riesz.Stationary.CompactHeadAngularSpectrum
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The actual normalized angular Gaussian Mellin mixture. -/

noncomputable section

open MeasureTheory RieszShowcase Set Filter
open scoped ENNReal Topology

namespace Riesz.Stationary

def angularMellinPrefactor (d : ℕ) : ℝ := (4 * Real.pi) ^ (-((d : ℝ) / 2))

def angularMellinOrder (d : ℕ) (s : ℝ) : ℝ := ((d : ℝ) - s) / 2

def angularMellinKernel (d : ℕ) (s : ℝ) (k : Rd d) : ℝ≥0∞ :=
  ∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ (s / 2 - 1)) *
    ENNReal.ofReal (originalHeatGaussian d u k)

def angularMellinReal (d : ℕ) (s : ℝ) (k : Rd d) : ℝ :=
  (angularMellinKernel d s k).toReal

theorem measurable_angularMellinKernel (d : ℕ) (s : ℝ) :
    Measurable (angularMellinKernel d s) := by
  exact (measurable_angularHeadBaseNN d s).lintegral_prod_left'
    (μ := volume.restrict (Ioc (0 : ℝ) 1))

theorem angularMellinPrefactor_pos (d : ℕ) : 0 < angularMellinPrefactor d := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem angularGaussian_normalization (d : ℕ) {u : ℝ} (hu : 0 < u) :
    (2 * Real.pi) ^ d * (4 * Real.pi * u) ^ (-((d : ℝ) / 2)) = B d u := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hU : 0 < 4 * Real.pi * u := by positivity
  have hprod : (Real.pi / u) * (4 * Real.pi * u) = (2 * Real.pi) ^ 2 := by
    field_simp [hu.ne']
    norm_num
  have hmass : B d u * (4 * Real.pi * u) ^ ((d : ℝ) / 2) = (2 * Real.pi) ^ d := by
    rw [B, ← Real.mul_rpow (div_nonneg Real.pi_pos.le hu.le) hU.le, hprod]
    rw [← Real.rpow_natCast (2 * Real.pi) 2, ← Real.rpow_mul hp.le]
    rw [Nat.cast_ofNat, show (2 : ℝ) * ((d : ℝ) / 2) = (d : ℝ) by ring,
      Real.rpow_natCast]
  rw [Real.rpow_neg hU.le, ← hmass, mul_assoc,
    mul_inv_cancel₀ (Real.rpow_pos_of_pos hU _).ne', mul_one]

theorem lintegral_originalAngularSpectrum_originalHeatGaussian
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) {u : ℝ} (hu : 0 < u) :
    (∫⁻ k, ENNReal.ofReal (originalHeatGaussian d u k)
      ∂originalAngularSpectrum d s hs P hP hW) =
      ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
        ENNReal.ofReal ((Q d P u).toReal + 1 - B d u) := by
  let ρ := originalAngularSpectrum d s hs P hP hW
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
  have htrace := lintegral_originalAngularSpectrum_heatSpectralWeight_eq d s hs P hP hW v hv
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

theorem lintegral_originalAngularSpectrum_originalHeatGaussian_le_remainder
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) {u : ℝ} (hu : 0 < u) :
    (∫⁻ k, ENNReal.ofReal (originalHeatGaussian d u k)
      ∂originalAngularSpectrum d s hs P hP hW) ≤
      ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) * (gaussianRemainder d P u + 1) := by
  rw [lintegral_originalAngularSpectrum_originalHeatGaussian d s hs P hP hW hu]
  refine mul_le_mul_right ?_ _
  have hQ := Q_ne_top_of_W_ne_top_pos d s hs P hW u hu
  have hcov := gaussian_covariance_lower_bound_of_admissible d P hP u hu
  have he : gaussianRemainder d P u ≠ ∞ := ENNReal.sub_ne_top hQ
  rw [← ENNReal.ofReal_toReal he, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one]
  apply ENNReal.ofReal_le_ofReal
  rw [gaussianRemainder, ENNReal.toReal_sub_of_le hcov hQ,
    ENNReal.toReal_ofReal (le_max_right _ _)]
  have hmax : max (B d u - 1) 0 ≤ B d u := max_le
    (sub_le_self _ zero_le_one) (Real.rpow_nonneg (div_nonneg Real.pi_pos.le hu.le) _)
  linarith

theorem lintegral_angularMellin_weight {s : ℝ} (hs : 0 < s) :
    (∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ (s / 2 - 1))) =
      ENNReal.ofReal (2 / s) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (positiveHeadWeight_integrable_and_integral s hs).1
    ((ae_restrict_mem measurableSet_Ioc).mono
      (fun u hu => Real.rpow_nonneg hu.1.le _)),
    (positiveHeadWeight_integrable_and_integral s hs).2]

theorem lintegral_angularMellinKernel_originalAngularSpectrum_ne_top
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    (∫⁻ k, angularMellinKernel d s k ∂originalAngularSpectrum d s hs P hP hW) ≠ ∞ := by
  let ρ := originalAngularSpectrum d s hs P hP hW
  let C : ℝ≥0∞ := ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹)
  let I : ℝ≥0∞ := ∫⁻ u in Ioi (0 : ℝ),
    ENNReal.ofReal (u ^ (s / 2 - 1)) * gaussianRemainder d P u
  have hI : I ≠ ∞ := weighted_gaussianRemainder_lintegral_ne_top_of_W_ne_top_pos d s hs P hW
  have hrepr : (∫⁻ k, angularMellinKernel d s k ∂ρ) =
      ∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ (s / 2 - 1)) *
        ∫⁻ k, ENNReal.ofReal (originalHeatGaussian d u k) ∂ρ := by
    simp only [angularMellinKernel]
    rw [lintegral_lintegral_swap (μ := ρ) (ν := volume.restrict (Ioc (0 : ℝ) 1))
      (f := fun k u => ENNReal.ofReal (u ^ (s / 2 - 1)) *
        ENNReal.ofReal (originalHeatGaussian d u k))
      ((measurable_angularHeadBaseNN d s).comp measurable_swap).aemeasurable]
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsplit : (∫⁻ u in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (u ^ (s / 2 - 1)) * (gaussianRemainder d P u + 1)) =
      (∫⁻ u in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (u ^ (s / 2 - 1)) * gaussianRemainder d P u) +
          ENNReal.ofReal (2 / s) := by
    simp_rw [mul_add, mul_one]
    rw [lintegral_add_right (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (fun u : ℝ => ENNReal.ofReal (u ^ (s / 2 - 1)) * gaussianRemainder d P u)
      (show Measurable (fun u : ℝ => ENNReal.ofReal (u ^ (s / 2 - 1))) from
        (measurable_id.pow_const (s / 2 - 1)).ennreal_ofReal),
      lintegral_angularMellin_weight hs]
  have hhead : (∫⁻ u in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (u ^ (s / 2 - 1)) * gaussianRemainder d P u) ≤ I :=
    lintegral_mono_set (fun _ hu => hu.1)
  have hbound : C * (I + ENNReal.ofReal (2 / s)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨hI, ENNReal.ofReal_ne_top⟩)
  apply ne_top_of_le_ne_top hbound
  refine le_trans ?_ (mul_le_mul_right (add_le_add_left hhead (ENNReal.ofReal (2 / s))) C)
  rw [hrepr, ← hsplit, ← lintegral_const_mul' C
    (fun u : ℝ => ENNReal.ofReal (u ^ (s / 2 - 1)) * (gaussianRemainder d P u + 1))
    (show C ≠ ∞ from ENNReal.ofReal_ne_top)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  simpa only [mul_left_comm] using mul_le_mul_right
    (lintegral_originalAngularSpectrum_originalHeatGaussian_le_remainder d s hs P hP hW hu.1)
    (ENNReal.ofReal (u ^ (s / 2 - 1)))

theorem lintegral_angularMellinKernel (d : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫⁻ k : Rd d, angularMellinKernel d s k) = ENNReal.ofReal (2 / s) := by
  refine (lintegral_lintegral_swap (μ := (volume : Measure (Rd d)))
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun k u => angularHeadBaseNN d s (u, k))
    ((measurable_angularHeadBaseNN d s).comp measurable_swap).aemeasurable).trans ?_
  exact (lintegral_prod _ (measurable_angularHeadBaseNN d s).aemeasurable).symm.trans
    (angularHeadBaseNN_lintegral d s hs)

theorem integrable_angularMellinReal (d : ℕ) {s : ℝ} (hs : 0 < s) :
    Integrable (angularMellinReal d s) volume := by
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_angularMellinKernel d s).aemeasurable
    ((lintegral_angularMellinKernel d hs).trans_ne ENNReal.ofReal_ne_top)

theorem integral_angularMellinReal (d : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ k : Rd d, angularMellinReal d s k) = 2 / s := by
  change (∫ k : Rd d, (angularMellinKernel d s k).toReal) = 2 / s
  rw [integral_toReal (measurable_angularMellinKernel d s).aemeasurable
    (ae_lt_top (measurable_angularMellinKernel d s)
      ((lintegral_angularMellinKernel d hs).trans_ne ENNReal.ofReal_ne_top)),
    lintegral_angularMellinKernel d hs, ENNReal.toReal_ofReal (by positivity)]

theorem angularMellin_integrand_eq_density
    (d : ℕ) (s : ℝ) {u : ℝ} (hu : 0 < u) (k : Rd d) :
    u ^ (s / 2 - 1) * originalHeatGaussian d u k = angularMellinPrefactor d *
      (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(‖k‖ ^ 2 / 4) / u)) := by
  rw [originalHeatGaussian, Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * Real.pi) hu.le]
  have he : -(1 / (4 * u)) * ‖k‖ ^ 2 = -(‖k‖ ^ 2 / 4) / u := by
    field_simp [hu.ne']
  rw [he]
  change u ^ (s / 2 - 1) *
    (angularMellinPrefactor d * u ^ (-((d : ℝ) / 2)) *
      Real.exp (-(‖k‖ ^ 2 / 4) / u)) = _
  conv_lhs => rw [mul_assoc,
    mul_left_comm (u ^ (s / 2 - 1)) (angularMellinPrefactor d),
    ← mul_assoc (u ^ (s / 2 - 1))]
  rw [← Real.rpow_add hu]
  congr 2
  congr 1
  dsimp only [angularMellinOrder]
  ring

theorem angularMellin_eq_lintegral_density (d : ℕ) (s : ℝ) (k : Rd d) :
    angularMellinKernel d s k = ∫⁻ u in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (angularMellinPrefactor d *
        (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(‖k‖ ^ 2 / 4) / u))) := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu.1.le _),
    angularMellin_integrand_eq_density d s hu.1]

theorem angular_lintegral_rpow_Ioc_eq_top {q : ℝ} (hq : q ≤ -1) :
    (∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ q)) = ∞ := by
  by_contra hf
  have hn : ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) 1), 0 ≤ u ^ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact Real.rpow_nonneg hu.1.le _
  have hi : IntegrableOn (fun u : ℝ => u ^ q) (Ioc 0 1) :=
    (lintegral_ofReal_ne_top_iff_integrable
      (measurable_id.pow_const q).aestronglyMeasurable hn).1 hf
  rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hi
  exact (not_lt_of_ge hq)
    ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).1 hi)

theorem angularMellinKernel_zero (d : ℕ) {s : ℝ} (hsd : s < (d : ℝ)) :
    angularMellinKernel d s (0 : Rd d) = ∞ := by
  rw [angularMellin_eq_lintegral_density]
  simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div,
    neg_zero, Real.exp_zero, mul_one]
  simp_rw [ENNReal.ofReal_mul (angularMellinPrefactor_pos d).le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hq : -angularMellinOrder d s - 1 ≤ -1 := by
    dsimp only [angularMellinOrder]
    linarith
  rw [angular_lintegral_rpow_Ioc_eq_top hq]
  exact ENNReal.mul_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr (angularMellinPrefactor_pos d)))

theorem ae_ne_zero_originalAngularSpectrum_of_finite_W
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    ∀ᵐ k ∂originalAngularSpectrum d s hs P hP hW, k ≠ 0 := by
  have hf := lintegral_angularMellinKernel_originalAngularSpectrum_ne_top d s hs P hP hW
  filter_upwards [ae_lt_top (measurable_angularMellinKernel d s) hf] with k hk
  intro hz
  subst k
  simp only [angularMellinKernel_zero d hsd, lt_self_iff_false] at hk

theorem angular_reciprocal_mellin_density (p b u : ℝ) (hu : 0 < u) :
    (|(-1 : ℝ)| * u ^ ((-1 : ℝ) - 1)) *
      ((u ^ (-1 : ℝ)) ^ (p - 1) * Real.exp (-(b * u ^ (-1 : ℝ)))) =
        u ^ (-p - 1) * Real.exp (-b / u) := by
  simp only [abs_neg, abs_one, one_mul]
  rw [← Real.rpow_mul hu.le, ← mul_assoc, ← Real.rpow_add hu, Real.rpow_neg_one]
  have he : (-1 : ℝ) - 1 + -1 * (p - 1) = -p - 1 := by ring
  rw [he]
  simp only [div_eq_mul_inv, neg_mul]

theorem integral_angular_reciprocal_mellin {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    (∫ u : ℝ in Ioi 0, u ^ (-p - 1) * Real.exp (-b / u)) =
      (1 / b) ^ p * Real.Gamma p := by
  calc
    _ = ∫ u : ℝ in Ioi 0, (|(-1 : ℝ)| * u ^ ((-1 : ℝ) - 1)) •
        ((u ^ (-1 : ℝ)) ^ (p - 1) * Real.exp (-(b * u ^ (-1 : ℝ)))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact (angular_reciprocal_mellin_density p b u hu).symm
    _ = ∫ v : ℝ in Ioi 0, v ^ (p - 1) * Real.exp (-(b * v)) :=
      integral_comp_rpow_Ioi (fun v : ℝ => v ^ (p - 1) * Real.exp (-(b * v)))
        (by norm_num : (-1 : ℝ) ≠ 0)
    _ = _ := Real.integral_rpow_mul_exp_neg_mul_Ioi hp hb

theorem integrable_angular_reciprocal_mellin {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ (-p - 1) * Real.exp (-b / u)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_angular_reciprocal_mellin hp hb]
  exact (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hb) _)
    (Real.Gamma_pos_of_pos hp)).ne'

theorem angularMellin_density_integrable
    (d : ℕ) {s : ℝ} (hsd : s < (d : ℝ)) {k : Rd d} (hk : k ≠ 0) :
    IntegrableOn (fun u : ℝ => angularMellinPrefactor d *
      (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(‖k‖ ^ 2 / 4) / u))) (Ioi 0) := by
  have hp : 0 < angularMellinOrder d s := by
    dsimp only [angularMellinOrder]
    linarith
  exact (integrable_angular_reciprocal_mellin hp
    (div_pos (sq_pos_of_pos (norm_pos_iff.mpr hk)) (by norm_num))).const_mul _

theorem angularMellin_density_nonneg (d : ℕ) (s : ℝ) (k : Rd d) :
    ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) 1), 0 ≤ angularMellinPrefactor d *
      (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(‖k‖ ^ 2 / 4) / u)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact mul_nonneg (angularMellinPrefactor_pos d).le
    (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.exp_pos _).le)

theorem angularMellinKernel_ne_top
    (d : ℕ) {s : ℝ} (hsd : s < (d : ℝ)) {k : Rd d} (hk : k ≠ 0) :
    angularMellinKernel d s k ≠ ∞ := by
  rw [angularMellin_eq_lintegral_density]
  have hi := (angularMellin_density_integrable d hsd hk).mono_set
    (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hu => hu.1)
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (angularMellin_density_nonneg d s k)).2 hi

theorem angularMellinReal_eq_integral
    (d : ℕ) {s : ℝ} (hsd : s < (d : ℝ)) {k : Rd d} (hk : k ≠ 0) :
    angularMellinReal d s k = ∫ u : ℝ in Ioc 0 1, angularMellinPrefactor d *
      (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(‖k‖ ^ 2 / 4) / u)) := by
  have hi := (angularMellin_density_integrable d hsd hk).mono_set
    (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hu => hu.1)
  rw [angularMellinReal, angularMellin_eq_lintegral_density,
    ← ofReal_integral_eq_lintegral_ofReal hi (angularMellin_density_nonneg d s k),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae (angularMellin_density_nonneg d s k))]

theorem continuousAt_angularMellinReal
    (d : ℕ) {s : ℝ} (hsd : s < (d : ℝ)) {k₀ : Rd d} (hk₀ : k₀ ≠ 0) :
    ContinuousAt (angularMellinReal d s) k₀ := by
  let r : ℝ := ‖k₀‖ / 2
  have hr : 0 < r := half_pos (norm_pos_iff.mpr hk₀)
  have hp : 0 < angularMellinOrder d s := div_pos (sub_pos.mpr hsd) (by norm_num)
  let F : Rd d → ℝ → ℝ := fun k u => angularMellinPrefactor d *
    (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(‖k‖ ^ 2 / 4) / u))
  let bound : ℝ → ℝ := fun u => angularMellinPrefactor d *
    (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(r ^ 2 / 4) / u))
  have hbfull : IntegrableOn bound (Ioi 0) :=
    (integrable_angular_reciprocal_mellin hp
      (div_pos (sq_pos_of_pos hr) (by norm_num))).const_mul (angularMellinPrefactor d)
  have hb : Integrable bound (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hbfull.mono_set (fun _ hu => hu.1)
  have hn : ∀ᶠ k in 𝓝 k₀, r < ‖k‖ :=
    continuous_norm.continuousAt.tendsto.eventually
      (Ioi_mem_nhds (half_lt_self (norm_pos_iff.mpr hk₀)))
  have hc : ContinuousAt (fun k => ∫ u in Ioc (0 : ℝ) 1, F k u) k₀ := by
    apply continuousAt_of_dominated (bound := bound) (μ := volume.restrict (Ioc (0 : ℝ) 1))
    · apply Eventually.of_forall
      exact fun k => (show Measurable (F k) from by fun_prop).aestronglyMeasurable
    · filter_upwards [hn] with k hk
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hsquare : r ^ 2 ≤ ‖k‖ ^ 2 := (sq_le_sq₀ hr.le (norm_nonneg k)).2 hk.le
      have he : Real.exp (-(‖k‖ ^ 2 / 4) / u) ≤ Real.exp (-(r ^ 2 / 4) / u) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div, neg_div]
        exact neg_le_neg (div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right hsquare (by norm_num)) hu.1.le)
      dsimp only [F, bound]
      rw [Real.norm_of_nonneg (mul_nonneg (angularMellinPrefactor_pos d).le
        (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.exp_pos _).le))]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hu.1.le _))
        (angularMellinPrefactor_pos d).le
    · exact hb
    · exact Eventually.of_forall (fun u => by fun_prop)
  apply hc.congr_of_eventuallyEq
  filter_upwards [hn] with k hk
  exact angularMellinReal_eq_integral d hsd (norm_pos_iff.mp (hr.trans hk))

theorem angular_reciprocal_radial_eq (p : ℝ) {r : ℝ} (hr : 0 < r) :
    (1 / (r ^ 2 / 4)) ^ p = (4 : ℝ) ^ p * r ^ (-(2 * p)) := by
  have hid : 1 / (r ^ 2 / 4) = (4 : ℝ) * (r ^ 2)⁻¹ := by
    field_simp [hr.ne']
  rw [hid, Real.mul_rpow (by norm_num) (inv_nonneg.mpr (sq_nonneg r)),
    Real.inv_rpow (sq_nonneg r), ← Real.rpow_neg (sq_nonneg r),
    ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
  simp only [Nat.cast_ofNat, mul_neg]

theorem angularMellinReal_le_riesz
    (d : ℕ) {s : ℝ} (hsd : s < (d : ℝ)) (k : Rd d) :
    angularMellinReal d s k ≤
      (angularMellinPrefactor d * (4 : ℝ) ^ (angularMellinOrder d s) *
        Real.Gamma (angularMellinOrder d s)) * ‖k‖ ^ (-((d : ℝ) - s)) := by
  have hp : 0 < angularMellinOrder d s := div_pos (sub_pos.mpr hsd) (by norm_num)
  by_cases hk : k = 0
  case neg =>
    rw [angularMellinReal_eq_integral d hsd hk]
    calc
      _ ≤ ∫ u : ℝ in Ioi 0, angularMellinPrefactor d *
          (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(‖k‖ ^ 2 / 4) / u)) := by
        apply setIntegral_mono_set (angularMellin_density_integrable d hsd hk)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact mul_nonneg (angularMellinPrefactor_pos d).le
            (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)
        · exact Eventually.of_forall (fun u hu => hu.1)
      _ = _ := by
        rw [integral_const_mul, integral_angular_reciprocal_mellin hp
          (div_pos (sq_pos_of_pos (norm_pos_iff.mpr hk)) (by norm_num)),
          angular_reciprocal_radial_eq _ (norm_pos_iff.mpr hk)]
        have he : 2 * angularMellinOrder d s = (d : ℝ) - s := by
          dsimp only [angularMellinOrder]
          ring
        rw [he]
        ring
  case pos =>
    subst k
    rw [angularMellinReal, angularMellinKernel_zero d hsd, ENNReal.toReal_top]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (angularMellinPrefactor_pos d).le (Real.rpow_nonneg (by norm_num) _))
      (Real.Gamma_pos_of_pos hp).le) (Real.rpow_nonneg (norm_nonneg _) _)

theorem angular_near_radial_eq (p : ℝ) {r : ℝ} (hr : 0 < r) :
    (r ^ 2 / 4 - r ^ 2 / 8) * (r ^ 2 / 4) ^ (-p - 1) =
      ((4 : ℝ) ^ (p + 1) / 8) * r ^ (-(2 * p)) := by
  have he : -p - 1 = -(p + 1) := by ring
  have h4 : (4 : ℝ) ^ (-p - 1) = ((4 : ℝ) ^ (p + 1))⁻¹ := by
    rw [he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
  have hrpow : r ^ 2 * (r ^ 2) ^ (-p - 1) = r ^ (-(2 * p)) := by
    conv_lhs => lhs; rw [← Real.rpow_one (r ^ 2)]
    rw [← Real.rpow_add (sq_pos_of_pos hr)]
    have hsum : (1 : ℝ) + (-p - 1) = -p := by ring
    rw [hsum, ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    simp only [Nat.cast_ofNat, mul_neg]
  calc
    _ = ((4 : ℝ) ^ (p + 1) / 8) * (r ^ 2 * (r ^ 2) ^ (-p - 1)) := by
      rw [Real.div_rpow (sq_nonneg r) (by norm_num : (0 : ℝ) ≤ 4)]
      simp only [h4, div_eq_mul_inv, inv_inv]
      ring
    _ = _ := by rw [hrpow]

theorem angular_reciprocal_mellin_near_lower {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hr2 : r ≤ 2) :
    ((4 : ℝ) ^ (p + 1) / 8 * Real.exp (-2)) * r ^ (-(2 * p)) ≤
      ∫ u : ℝ in Ioc 0 1, u ^ (-p - 1) * Real.exp (-(r ^ 2 / 4) / u) := by
  let A : ℝ := r ^ 2 / 8
  let B : ℝ := r ^ 2 / 4
  let C : ℝ := B ^ (-p - 1) * Real.exp (-2)
  let f : ℝ → ℝ := fun u => u ^ (-p - 1) * Real.exp (-(r ^ 2 / 4) / u)
  have hA : 0 < A := div_pos (sq_pos_of_pos hr) (by norm_num)
  have hAB : A < B := by
    dsimp only [A, B]
    nlinarith [sq_pos_of_pos hr]
  have hB1 : B ≤ 1 := by
    dsimp only [B]
    nlinarith
  have hsub : Ioo A B ⊆ Ioc (0 : ℝ) 1 :=
    fun u hu => ⟨hA.trans hu.1, hu.2.le.trans hB1⟩
  have hifull : IntegrableOn f (Ioi 0) :=
    integrable_angular_reciprocal_mellin hp
      (div_pos (sq_pos_of_pos hr) (by norm_num))
  have hi : IntegrableOn f (Ioc 0 1) := hifull.mono_set (fun _ hu => hu.1)
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.exp_pos _).le
  have hpoint : ∀ u ∈ Ioo A B, C ≤ f u := by
    intro u hu
    have hu0 : 0 < u := hA.trans hu.1
    have hexp : -p - 1 ≤ 0 := by linarith
    have hpow : B ^ (-p - 1) ≤ u ^ (-p - 1) :=
      Real.rpow_le_rpow_of_nonpos hu0 hu.2.le hexp
    have hrat : r ^ 2 / 4 ≤ 2 * u := by
      dsimp only [A] at hu
      linarith [hu.1.le]
    have he : Real.exp (-2) ≤ Real.exp (-(r ^ 2 / 4) / u) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      exact neg_le_neg ((div_le_iff₀ hu0).2 hrat)
    exact mul_le_mul hpow he (Real.exp_pos _).le (Real.rpow_nonneg hu0.le _)
  calc
    _ = (B - A) * C := by
      dsimp only [A, B, C]
      conv_rhs => rw [← mul_assoc, angular_near_radial_eq p hr]
      ring
    _ = ∫ u : ℝ in Ioo A B, C := by
      rw [setIntegral_const]
      simp only [measureReal_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hAB.le), smul_eq_mul]
    _ ≤ ∫ u : ℝ in Ioo A B, f u :=
      setIntegral_mono_on (integrableOn_const measure_Ioo_lt_top.ne)
        (hi.mono_set hsub) measurableSet_Ioo hpoint
    _ ≤ _ := setIntegral_mono_set hi hn (Eventually.of_forall (fun _ hu => hsub hu))

theorem angularMellinReal_ge_riesz_near
    (d : ℕ) {s : ℝ} (hsd : s < (d : ℝ)) {k : Rd d}
    (hk : k ≠ 0) (hk2 : ‖k‖ ≤ 2) :
    (angularMellinPrefactor d * (4 : ℝ) ^ (angularMellinOrder d s + 1) / 8 * Real.exp (-2)) *
      ‖k‖ ^ (-((d : ℝ) - s)) ≤ angularMellinReal d s k := by
  rw [angularMellinReal_eq_integral d hsd hk, integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left
    (angular_reciprocal_mellin_near_lower
      (show 0 < angularMellinOrder d s from div_pos (sub_pos.mpr hsd) (by norm_num))
      (norm_pos_iff.mpr hk) hk2) (angularMellinPrefactor_pos d).le
  have he : 2 * angularMellinOrder d s = (d : ℝ) - s := by
    norm_num [angularMellinOrder]
    ring
  rw [he] at hh
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh

theorem angularMellinReal_le_gaussian_tail
    (d : ℕ) {s : ℝ} (hsd : s < (d : ℝ)) {k : Rd d} (hk : 1 ≤ ‖k‖) :
    angularMellinReal d s k ≤
      (angularMellinPrefactor d * (8 : ℝ) ^ (angularMellinOrder d s) *
        Real.Gamma (angularMellinOrder d s)) * Real.exp (-‖k‖ ^ 2 / 8) := by
  let g : ℝ → ℝ := fun u => (angularMellinPrefactor d * Real.exp (-‖k‖ ^ 2 / 8)) *
    (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(1 / 8 : ℝ) / u))
  have hp : 0 < angularMellinOrder d s := div_pos (sub_pos.mpr hsd) (by norm_num)
  have hk0 : 0 < ‖k‖ := zero_lt_one.trans_le hk
  have hksq : (1 : ℝ) ≤ ‖k‖ ^ 2 := one_le_pow₀ hk
  have hi := (angularMellin_density_integrable d hsd (norm_pos_iff.mp hk0)).mono_set
    (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hu => hu.1)
  have hgfull : IntegrableOn g (Ioi 0) :=
    (integrable_angular_reciprocal_mellin hp (by norm_num : (0 : ℝ) < 1 / 8)).const_mul _
  have hg : IntegrableOn g (Ioc 0 1) := hgfull.mono_set (fun _ hu => hu.1)
  have hpoint : ∀ u ∈ Ioc (0 : ℝ) 1, angularMellinPrefactor d *
      (u ^ (-angularMellinOrder d s - 1) * Real.exp (-(‖k‖ ^ 2 / 4) / u)) ≤ g u := by
    intro u hu
    have hnum : -(‖k‖ ^ 2 / 4) ≤ (-‖k‖ ^ 2 / 8) * u - 1 / 8 := by
      nlinarith [mul_nonneg (sq_nonneg ‖k‖) (sub_nonneg.mpr hu.2)]
    have hh := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hnum hu.1.le)
    rw [sub_div, mul_div_cancel_right₀ _ hu.1.ne', sub_eq_add_neg, Real.exp_add] at hh
    simpa only [g, neg_div, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hu.1.le (-angularMellinOrder d s - 1)))
        (angularMellinPrefactor_pos d).le
  rw [angularMellinReal_eq_integral d hsd (norm_pos_iff.mp hk0)]
  calc
    _ ≤ ∫ u : ℝ in Ioc 0 1, g u := setIntegral_mono_on hi hg measurableSet_Ioc hpoint
    _ ≤ ∫ u : ℝ in Ioi 0, g u := by
      apply setIntegral_mono_set hgfull
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact mul_nonneg (mul_nonneg (angularMellinPrefactor_pos d).le (Real.exp_pos _).le)
          (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)
      · exact Eventually.of_forall (fun _ hu => hu.1)
    _ = _ := by
      dsimp only [g]
      rw [integral_const_mul, integral_angular_reciprocal_mellin hp
        (by norm_num : (0 : ℝ) < 1 / 8)]
      norm_num
      ring

theorem angular_even_gaussian_moment_le {c : ℝ} (hc : 0 < c) (m : ℕ) (r : ℝ) :
    r ^ (2 * m) * Real.exp (-c * r ^ 2) ≤ (m.factorial : ℝ) / c ^ m := by
  have hfac : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hz : 0 ≤ c * r ^ 2 := mul_nonneg hc.le (sq_nonneg r)
  have hp : (c * r ^ 2) ^ m ≤ Real.exp (c * r ^ 2) * (m.factorial : ℝ) :=
    (div_le_iff₀ hfac).1 (Real.pow_div_factorial_le_exp (c * r ^ 2) hz m)
  apply (le_div_iff₀ (pow_pos hc m)).2
  calc
    _ = (c * r ^ 2) ^ m * Real.exp (-(c * r ^ 2)) := by
      rw [neg_mul, mul_pow, pow_mul]
      ring
    _ ≤ (Real.exp (c * r ^ 2) * (m.factorial : ℝ)) * Real.exp (-(c * r ^ 2)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

theorem angular_gaussian_polynomial_tail (m : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    Real.exp (-r ^ 2 / 8) ≤
      ((2 : ℝ) ^ m * ((m.factorial : ℝ) / (1 / 8 : ℝ) ^ m)) * (1 + r) ^ (-(m : ℝ)) := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hw : (1 + r) ^ m * Real.exp (-r ^ 2 / 8) ≤
      (2 : ℝ) ^ m * ((m.factorial : ℝ) / (1 / 8 : ℝ) ^ m) := by
    calc
      _ ≤ (2 * r) ^ m * Real.exp (-r ^ 2 / 8) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) m)
          (Real.exp_pos _).le
      _ = (2 : ℝ) ^ m * (r ^ m * Real.exp (-r ^ 2 / 8)) := by
        rw [mul_pow]
        ring
      _ ≤ (2 : ℝ) ^ m * (r ^ (2 * m) * Real.exp (-r ^ 2 / 8)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hr (by omega)) (Real.exp_pos _).le) (pow_nonneg (by norm_num) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [neg_mul, mul_neg, div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc] using
          angular_even_gaussian_moment_le (by norm_num : (0 : ℝ) < 1 / 8) m r)
        (pow_nonneg (by norm_num) _)
  have hp : 0 < (1 + r) ^ m := pow_pos (by positivity) _
  have hh : Real.exp (-r ^ 2 / 8) ≤
      ((2 : ℝ) ^ m * ((m.factorial : ℝ) / (1 / 8 : ℝ) ^ m)) / (1 + r) ^ m :=
    (le_div_iff₀ hp).2 (by simpa only [mul_comm] using hw)
  simpa only [div_eq_mul_inv, ← Real.rpow_natCast,
    ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + r)] using hh

theorem angularMellinReal_le_polynomial_tail
    (d m : ℕ) {s : ℝ} (hsd : s < (d : ℝ)) {k : Rd d} (hk : 1 ≤ ‖k‖) :
    angularMellinReal d s k ≤
      ((angularMellinPrefactor d * (8 : ℝ) ^ (angularMellinOrder d s) *
        Real.Gamma (angularMellinOrder d s)) *
        ((2 : ℝ) ^ m * ((m.factorial : ℝ) / (1 / 8 : ℝ) ^ m))) *
          (1 + ‖k‖) ^ (-(m : ℝ)) := by
  have hp : 0 < angularMellinOrder d s := div_pos (sub_pos.mpr hsd) (by norm_num)
  have hD : 0 ≤ angularMellinPrefactor d * (8 : ℝ) ^ (angularMellinOrder d s) *
      Real.Gamma (angularMellinOrder d s) :=
    mul_nonneg (mul_nonneg (angularMellinPrefactor_pos d).le
      (Real.rpow_nonneg (by norm_num) _)) (Real.Gamma_pos_of_pos hp).le
  refine (angularMellinReal_le_gaussian_tail d hsd hk).trans ?_
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (angular_gaussian_polynomial_tail m hk) hD

theorem integrable_angularMellinReal_originalAngularSpectrum
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    Integrable (angularMellinReal d s) (originalAngularSpectrum d s hs P hP hW) := by
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_angularMellinKernel d s).aemeasurable
    (lintegral_angularMellinKernel_originalAngularSpectrum_ne_top d s hs P hP hW)

end Riesz.Stationary
