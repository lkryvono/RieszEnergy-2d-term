import Riesz.Stationary.WindowOverlap
import Riesz.Analysis.Bochner.Main
import Mathlib.MeasureTheory.Function.L2Space

/-!
Direct Campbell identities, Gaussian heat moments, and finite heat spectra for
the original simple Showcase-admissible law. Finite positive `W` supplies the
profile finiteness used for continuous, complex positive-definite covariance.
The last section constructs its finite Bochner measure at each positive time.
Compatibility between different heat times and the unsmoothed spectral measure
are separate remaining obligations.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration
open scoped ENNReal Classical Topology

namespace Riesz.Configuration

theorem simple_pair_lintegral_eq_diagonal_add_offsite
    (d : ℕ) (μ : Measure (Rd d)) (hμ : IsSimpleConfiguration d μ)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ x, ∫⁻ y, k (x, y) ∂μ ∂μ) =
      (∫⁻ x, k (x, x) ∂μ) +
        ∫⁻ x, ∫⁻ y, if x = y then 0 else k (x, y) ∂μ ∂μ := by
  have hdiag (x : Rd d) :
      (∫⁻ y, if x = y then k (x, y) else 0 ∂μ) = k (x, x) * μ {x} := by
    simpa only [Set.indicator_apply, Set.mem_singleton_iff, eq_comm] using
      (lintegral_indicator (μ := μ) (measurableSet_singleton x) (fun y => k (x, y))).trans
        (lintegral_singleton (μ := μ) (fun y => k (x, y)) x)
  have hsplit (x : Rd d) :
      (∫⁻ y, k (x, y) ∂μ) =
        (∫⁻ y, if x = y then k (x, y) else 0 ∂μ) +
          ∫⁻ y, if x = y then 0 else k (x, y) ∂μ := by
    simpa only [ite_add_ite, add_zero, zero_add, ite_self] using
      (lintegral_add_left (μ := μ) (f := fun y => if x = y then k (x, y) else 0)
        (Measurable.ite (measurableSet_eq_fun measurable_const measurable_id)
          (hk.comp (measurable_const.prodMk measurable_id)) measurable_const)
        (fun y => if x = y then 0 else k (x, y)))
  have hunit : ∀ᵐ x ∂μ, μ {x} = 1 :=
    locallySimple_ae_mem_sites d μ (simple_locallySimple d μ hμ)
  exact (lintegral_congr_ae (hunit.mono (fun x hx => by
    simpa only [hdiag x, hx, mul_one, Function.comp_def, id_eq] using hsplit x))).trans
      (lintegral_add_left (f := fun x => k (x, x))
        (hk.comp (measurable_id.prodMk measurable_id)) _)

end Riesz.Configuration

namespace Riesz.Stationary

theorem originalAdmissible_mean_lintegral
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (a : Rd d → ℝ≥0∞) (ha : Measurable a) :
    (∫⁻ μ, ∫⁻ x, a x ∂μ ∂P) = ∫⁻ x, a x ∂volume := by
  exact (Measure.lintegral_join ha.aemeasurable).symm.trans
    (congrArg (fun M => ∫⁻ x, a x ∂M) (join_eq_volume_of_admissible d P hP))

theorem originalAdmissible_pair_lintegral_eq_factorial_add_diagonal
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ μ, ∫⁻ x, ∫⁻ y, k (x, y) ∂μ ∂μ ∂P) =
      (∫⁻ p, k p ∂originalAdmissibleFactorialMeasure d P hP) +
        ∫⁻ x, k (x, x) ∂volume := by
  have hkdiag : Measurable (fun x : Rd d => k (x, x)) :=
    hk.comp (measurable_id.prodMk measurable_id)
  exact (lintegral_congr_ae (hP.2.1.mono (fun μ hμ =>
    simple_pair_lintegral_eq_diagonal_add_offsite d μ hμ k hk))).trans
      ((lintegral_add_left (f := fun μ : Measure (Rd d) => ∫⁻ x, k (x, x) ∂μ)
        (Measure.measurable_lintegral hkdiag) _).trans
        ((congrArg₂ (· + ·) (originalAdmissible_mean_lintegral d P hP _ hkdiag)
          (lintegral_originalAdmissibleFactorialMeasure_eq_pair_lintegral d P hP k hk).symm).trans
            (add_comm _ _)))

theorem nonnegativeMass_product_eq_pair_lintegral
    (d : ℕ) (μ : Measure (Rd d))
    (c e : Rd d → ℝ≥0∞) (hc : Measurable c) (he : Measurable e) :
    (∫⁻ x, c x ∂μ) * (∫⁻ y, e y ∂μ) =
      ∫⁻ x, ∫⁻ y, c x * e y ∂μ ∂μ := by
  exact ((lintegral_congr (fun x => lintegral_const_mul (μ := μ) (c x) he)).trans
    (lintegral_mul_const _ hc)).symm

theorem originalAdmissible_mass_product_expectation
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (c e : Rd d → ℝ≥0∞) (hc : Measurable c) (he : Measurable e) :
    (∫⁻ μ, (∫⁻ x, c x ∂μ) * (∫⁻ y, e y ∂μ) ∂P) =
      (∫⁻ p, c p.1 * e p.2 ∂originalAdmissibleFactorialMeasure d P hP) +
        ∫⁻ x, c x * e x ∂volume := by
  exact (lintegral_congr (fun μ =>
    nonnegativeMass_product_eq_pair_lintegral d μ c e hc he)).trans
      (originalAdmissible_pair_lintegral_eq_factorial_add_diagonal d P hP
        (fun p => c p.1 * e p.2) ((hc.comp measurable_fst).mul (he.comp measurable_snd)))

theorem originalAdmissible_mass_square_expectation
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (c : Rd d → ℝ≥0∞) (hc : Measurable c) :
    (∫⁻ μ, (∫⁻ x, c x ∂μ) ^ (2 : ℕ) ∂P) =
      (∫⁻ p, c p.1 * c p.2 ∂originalAdmissibleFactorialMeasure d P hP) +
        ∫⁻ x, c x ^ (2 : ℕ) ∂volume := by
  simpa only [pow_two] using originalAdmissible_mass_product_expectation d P hP c c hc hc

def originalHeatGaussian (d : ℕ) (t : ℝ) (x : Rd d) : ℝ :=
  (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
    Real.exp (-(1 / (4 * t)) * ‖x‖ ^ (2 : ℕ))

def originalHeatMass (d : ℕ) (t : ℝ) (a : Rd d)
    (μ : Measure (Rd d)) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (originalHeatGaussian d t (a - x)) ∂μ

def originalHeatField (d : ℕ) (t : ℝ) (a : Rd d)
    (μ : Measure (Rd d)) : ℝ :=
  (originalHeatMass d t a μ).toReal - 1

theorem B_double_ratio (d : ℕ) (β : ℝ) (hβ : 0 < β) :
    B d (2 * β) / (B d β) ^ 2 = (β / (2 * Real.pi)) ^ ((d : ℝ) / 2) := by
  have hpowers : ((Real.pi / β) ^ ((d : ℝ) / 2)) ^ (2 : ℕ) =
      ((Real.pi / β) ^ (2 : ℕ)) ^ ((d : ℝ) / 2) :=
    (Real.rpow_mul_natCast (div_pos Real.pi_pos hβ).le _ 2).symm.trans
      ((congrArg (fun r : ℝ => (Real.pi / β) ^ r) (mul_comm _ _)).trans
        (Real.rpow_natCast_mul (div_pos Real.pi_pos hβ).le 2 _))
  rw [B, B, hpowers, ← Real.div_rpow (div_pos Real.pi_pos (by positivity : 0 < 2 * β)).le
    (sq_nonneg (Real.pi / β))]
  congr 1
  field_simp [hβ.ne', Real.pi_ne_zero]

theorem heatGaussian_constant_eq_inv_B (d : ℕ) (t : ℝ) (ht : 0 < t) :
    (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) = (B d (1 / (4 * t)))⁻¹ := by
  have hb : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by
    field_simp [ht.ne']
  rw [B, hb, Real.rpow_neg (show 0 ≤ 4 * Real.pi * t by positivity)]

theorem heatGaussian_second_constant (d : ℕ) (t : ℝ) (ht : 0 < t) :
    ((4 * Real.pi * t) ^ (-((d : ℝ) / 2))) ^ 2 * B d (2 * (1 / (4 * t))) =
      (8 * Real.pi * t) ^ (-((d : ℝ) / 2)) := by
  have hfrac : (1 / (4 * t)) / (2 * Real.pi) = (8 * Real.pi * t)⁻¹ := by
    field_simp [ht.ne', Real.pi_ne_zero]
    norm_num
  rw [heatGaussian_constant_eq_inv_B d t ht, inv_pow, mul_comm, ← div_eq_mul_inv,
    B_double_ratio d (1 / (4 * t)) (by positivity), hfrac,
    Real.inv_rpow (show 0 ≤ 8 * Real.pi * t by positivity),
    Real.rpow_neg (show 0 ≤ 8 * Real.pi * t by positivity)]

theorem nonnegativeWindowOverlap_rawGaussian
    (d : ℕ) (β : ℝ) (hβ : 0 < β) (a z : Rd d) :
    nonnegativeWindowOverlap d
      (fun x => ENNReal.ofReal (Real.exp (-β * ‖a - x‖ ^ (2 : ℕ)))) z =
      ENNReal.ofReal (B d (2 * β)) *
        ENNReal.ofReal (Real.exp (-(β / 2) * ‖z‖ ^ (2 : ℕ))) := by
  have hshift (x : Rd d) : a - (x + z) = (a - z) - x := by abel
  have hparam : -β = -2 * (β / 2) := by ring
  have hF : Integrable (fun x : Rd d =>
      Real.exp (-2 * (β / 2) * ‖a - x‖ ^ 2) *
        Real.exp (-2 * (β / 2) * ‖(a - z) - x‖ ^ 2)) volume :=
    Riesz.Analysis.integrable_gaussian_product (β / 2) (by positivity) a (a - z)
  have htwo : (4 : ℝ) * (β / 2) = 2 * β := by ring
  have hvalue : (∫ x : Rd d,
      Real.exp (-2 * (β / 2) * ‖a - x‖ ^ 2) *
        Real.exp (-2 * (β / 2) * ‖(a - z) - x‖ ^ 2) ∂volume) =
      Real.exp (-(β / 2) * ‖z‖ ^ 2) * B d (2 * β) := by
    simpa only [sub_sub_cancel, Rd, finrank_euclideanSpace_fin, htwo, B] using
      Riesz.Analysis.integral_gaussian_product (β / 2) (by positivity) a (a - z)
  simp_rw [nonnegativeWindowOverlap, ← ENNReal.ofReal_mul (Real.exp_pos _).le, hshift, hparam]
  rw [← ofReal_integral_eq_lintegral_ofReal hF
    (Filter.Eventually.of_forall (fun x => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)),
    hvalue, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

theorem continuous_originalHeatGaussian (d : ℕ) (t : ℝ) :
    Continuous (originalHeatGaussian d t) := by
  exact continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_id.norm.pow 2)))

theorem originalHeatGaussian_nonneg (d : ℕ) (t : ℝ) (ht : 0 < t) (x : Rd d) :
    0 ≤ originalHeatGaussian d t x := by
  exact mul_nonneg
    (Real.rpow_pos_of_pos (show 0 < 4 * Real.pi * t by positivity) _).le
    (Real.exp_pos _).le

theorem nonnegativeWindowOverlap_originalHeatGaussian
    (d : ℕ) (t : ℝ) (ht : 0 < t) (a z : Rd d) :
    nonnegativeWindowOverlap d
      (fun x => ENNReal.ofReal (originalHeatGaussian d t (a - x))) z =
      ENNReal.ofReal ((8 * Real.pi * t) ^ (-((d : ℝ) / 2))) *
        ENNReal.ofReal (Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)) := by
  have hκ : 0 ≤ (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) :=
    (Real.rpow_pos_of_pos (show 0 < 4 * Real.pi * t by positivity) _).le
  have hparam : (1 / (4 * t)) / 2 = 1 / (8 * t) := by
    field_simp [ht.ne']
    norm_num
  have hpoint (x : Rd d) :
      ENNReal.ofReal (originalHeatGaussian d t (a - x)) *
          ENNReal.ofReal (originalHeatGaussian d t (a - (x + z))) =
        ENNReal.ofReal (((4 * Real.pi * t) ^ (-((d : ℝ) / 2))) ^ 2) *
          (ENNReal.ofReal (Real.exp (-(1 / (4 * t)) * ‖a - x‖ ^ 2)) *
            ENNReal.ofReal (Real.exp (-(1 / (4 * t)) * ‖a - (x + z)‖ ^ 2))) := by
    simp only [originalHeatGaussian, ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hκ]
    ring
  have hscaled : nonnegativeWindowOverlap d
      (fun x => ENNReal.ofReal (originalHeatGaussian d t (a - x))) z =
      ENNReal.ofReal (((4 * Real.pi * t) ^ (-((d : ℝ) / 2))) ^ 2) *
        (ENNReal.ofReal (B d (2 * (1 / (4 * t)))) *
          ENNReal.ofReal (Real.exp (-((1 / (4 * t)) / 2) * ‖z‖ ^ 2))) :=
    (lintegral_congr hpoint).trans
      ((lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
        (congrArg (ENNReal.ofReal (((4 * Real.pi * t) ^ (-((d : ℝ) / 2))) ^ 2) * ·)
          (nonnegativeWindowOverlap_rawGaussian d (1 / (4 * t)) (by positivity) a z)))
  rw [hscaled, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _),
    heatGaussian_second_constant d t ht, hparam]

theorem lintegral_originalHeatGaussian_sq
    (d : ℕ) (t : ℝ) (ht : 0 < t) (a : Rd d) :
    (∫⁻ x, ENNReal.ofReal ((originalHeatGaussian d t (a - x)) ^ 2) ∂volume) =
      ENNReal.ofReal ((8 * Real.pi * t) ^ (-((d : ℝ) / 2))) := by
  simpa only [nonnegativeWindowOverlap, add_zero, norm_zero, zero_pow two_ne_zero,
    mul_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one,
    fun x : Rd d => ENNReal.ofReal_mul (q := originalHeatGaussian d t x)
      (originalHeatGaussian_nonneg d t ht x),
    pow_two] using
      nonnegativeWindowOverlap_originalHeatGaussian d t ht a (0 : Rd d)

theorem lintegral_originalHeatGaussian
    (d : ℕ) (t : ℝ) (ht : 0 < t) (a : Rd d) :
    (∫⁻ x, ENNReal.ofReal (originalHeatGaussian d t (a - x)) ∂volume) = 1 := by
  have hraw : (∫⁻ x : Rd d,
      ENNReal.ofReal (Real.exp (-(1 / (4 * t)) * ‖a - x‖ ^ 2)) ∂volume) =
      ENNReal.ofReal (B d (1 / (4 * t))) := by
    simpa only [norm_sub_rev, neg_mul] using
      lintegral_gaussian_translate d (1 / (4 * t)) (by positivity) a
  have hκ : 0 ≤ (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) :=
    (Real.rpow_pos_of_pos (show 0 < 4 * Real.pi * t by positivity) _).le
  have hB : 0 < B d (1 / (4 * t)) :=
    Real.rpow_pos_of_pos (div_pos Real.pi_pos (by positivity)) _
  simp_rw [originalHeatGaussian, ENNReal.ofReal_mul hκ]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hraw, ← ENNReal.ofReal_mul hκ,
    heatGaussian_constant_eq_inv_B d t ht, inv_mul_cancel₀ hB.ne', ENNReal.ofReal_one]

theorem measurable_originalHeatMass (d : ℕ) (t : ℝ) (a : Rd d) :
    Measurable (originalHeatMass d t a) := by
  exact Measure.measurable_lintegral
    (((continuous_originalHeatGaussian d t).comp
      (continuous_const.sub continuous_id)).measurable.ennreal_ofReal)

theorem lintegral_originalHeatMass (d : ℕ) (P : ConfigurationLaw d)
    (hP : Admissible d P) (t : ℝ) (ht : 0 < t) (a : Rd d) :
    (∫⁻ μ, originalHeatMass d t a μ ∂P) = 1 := by
  exact (originalAdmissible_mean_lintegral d P hP _
    (((continuous_originalHeatGaussian d t).comp
      (continuous_const.sub continuous_id)).measurable.ennreal_ofReal)).trans
        (lintegral_originalHeatGaussian d t ht a)

theorem lintegral_originalHeatGaussian_pair_of_admissible
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a : Rd d) :
    (∫⁻ p, ENNReal.ofReal (originalHeatGaussian d t (a - p.1)) *
      ENNReal.ofReal (originalHeatGaussian d t (a - p.2))
        ∂originalAdmissibleFactorialMeasure d P hP) =
      ENNReal.ofReal ((8 * Real.pi * t) ^ (-((d : ℝ) / 2))) *
        Q d P (1 / (8 * t)) := by
  have hstation :
      (∫⁻ p, ENNReal.ofReal (originalHeatGaussian d t (a - p.1)) *
          ENNReal.ofReal (originalHeatGaussian d t (a - p.2))
            ∂originalAdmissibleFactorialMeasure d P hP) =
        ∫⁻ p, (cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
          nonnegativeWindowOverlap d
            (fun x => ENNReal.ofReal (originalHeatGaussian d t (a - x))) (p.2 - p.1)
              ∂originalAdmissibleFactorialMeasure d P hP := by
    simpa only [mul_one] using lintegral_stationaryPair_window_eq_cube_overlap d
      (originalAdmissibleFactorialMeasure d P hP)
      (originalAdmissibleFactorialMeasure_map_diagAdd_eq_self d P hP)
      (fun x => ENNReal.ofReal (originalHeatGaussian d t (a - x))) (fun _ => 1)
      (((continuous_originalHeatGaussian d t).comp
        (continuous_const.sub continuous_id)).measurable.ennreal_ofReal) measurable_const
  have hpoint (p : Rd d × Rd d) :
      (cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
        nonnegativeWindowOverlap d
          (fun x => ENNReal.ofReal (originalHeatGaussian d t (a - x))) (p.2 - p.1) =
      ENNReal.ofReal ((8 * Real.pi * t) ^ (-((d : ℝ) / 2))) *
        anchoredGaussianKernel d (1 / (8 * t)) p := by
    simp only [nonnegativeWindowOverlap_originalHeatGaussian d t ht a,
      anchoredGaussianKernel, Set.indicator_apply, neg_mul, ite_mul, mul_ite,
      one_mul, zero_mul, mul_zero]
  exact hstation.trans ((lintegral_congr hpoint).trans
    ((lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
      (congrArg (ENNReal.ofReal ((8 * Real.pi * t) ^ (-((d : ℝ) / 2))) * ·)
        (Q_eq_originalAdmissibleFactorialMeasure d P hP (1 / (8 * t))).symm)))

theorem lintegral_originalHeatMass_sq
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a : Rd d) :
    (∫⁻ μ, (originalHeatMass d t a μ) ^ 2 ∂P) =
      ENNReal.ofReal ((8 * Real.pi * t) ^ (-((d : ℝ) / 2))) *
        (Q d P (1 / (8 * t)) + 1) := by
  have hdiag : (∫⁻ x, (ENNReal.ofReal (originalHeatGaussian d t (a - x))) ^ 2 ∂volume) =
      ENNReal.ofReal ((8 * Real.pi * t) ^ (-((d : ℝ) / 2))) :=
    (lintegral_congr (fun x =>
      (ENNReal.ofReal_pow (originalHeatGaussian_nonneg d t ht (a - x)) 2).symm)).trans
        (lintegral_originalHeatGaussian_sq d t ht a)
  simpa only [originalHeatMass, hdiag,
    lintegral_originalHeatGaussian_pair_of_admissible d P hP t ht a, mul_add, mul_one] using
      originalAdmissible_mass_square_expectation d P hP
        (fun x => ENNReal.ofReal (originalHeatGaussian d t (a - x)))
        (((continuous_originalHeatGaussian d t).comp
          (continuous_const.sub continuous_id)).measurable.ennreal_ofReal)

theorem originalHeatMass_memLp_two
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a : Rd d) (hQ : Q d P (1 / (8 * t)) ≠ ∞) :
    MemLp (fun μ => (originalHeatMass d t a μ).toReal) 2 P := by
  have hfinite : (∫⁻ μ, (originalHeatMass d t a μ) ^ 2 ∂P) ≠ ∞ :=
    (lintegral_originalHeatMass_sq d P hP t ht a).trans_ne
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hQ, ENNReal.one_ne_top⟩))
  have hsq : Integrable (fun μ => (originalHeatMass d t a μ).toReal ^ 2) P := by
    simpa only [ENNReal.toReal_pow] using
      integrable_toReal_of_lintegral_ne_top
        ((measurable_originalHeatMass d t a).pow_const 2).aemeasurable hfinite
  exact (memLp_two_iff_integrable_sq
    (measurable_originalHeatMass d t a).ennreal_toReal.aestronglyMeasurable).mpr hsq

theorem integral_originalHeatMass_toReal
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a : Rd d) :
    (∫ μ, (originalHeatMass d t a μ).toReal ∂P) = 1 := by
  have hfinite : (∫⁻ μ, originalHeatMass d t a μ ∂P) ≠ ∞ :=
    (lintegral_originalHeatMass d P hP t ht a).trans_ne ENNReal.one_ne_top
  simpa only [lintegral_originalHeatMass d P hP t ht a, ENNReal.toReal_one] using
    integral_toReal (measurable_originalHeatMass d t a).aemeasurable
      (ae_lt_top (measurable_originalHeatMass d t a) hfinite)

theorem integral_originalHeatMass_toReal_sq
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a : Rd d) (hQ : Q d P (1 / (8 * t)) ≠ ∞) :
    (∫ μ, (originalHeatMass d t a μ).toReal ^ 2 ∂P) =
      (8 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
        ((Q d P (1 / (8 * t))).toReal + 1) := by
  have hfinite : (∫⁻ μ, (originalHeatMass d t a μ) ^ 2 ∂P) ≠ ∞ :=
    (lintegral_originalHeatMass_sq d P hP t ht a).trans_ne
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hQ, ENNReal.one_ne_top⟩))
  simpa only [ENNReal.toReal_pow, lintegral_originalHeatMass_sq d P hP t ht a,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal
      (Real.rpow_pos_of_pos (show 0 < 8 * Real.pi * t by positivity) _).le,
    ENNReal.toReal_add hQ ENNReal.one_ne_top, ENNReal.toReal_one] using
      integral_toReal ((measurable_originalHeatMass d t a).pow_const 2).aemeasurable
        (ae_lt_top ((measurable_originalHeatMass d t a).pow_const 2) hfinite)

theorem originalHeatMass_toReal_eq_integral
    (d : ℕ) (t : ℝ) (ht : 0 < t) (a : Rd d) (μ : Measure (Rd d)) :
    (originalHeatMass d t a μ).toReal =
      ∫ x, originalHeatGaussian d t (a - x) ∂μ := by
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => originalHeatGaussian_nonneg d t ht (a - x)))
    (((continuous_originalHeatGaussian d t).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)).symm

theorem ae_integrable_originalHeatGaussian_of_admissible
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a : Rd d) :
    ∀ᵐ μ ∂P, Integrable (fun x => originalHeatGaussian d t (a - x)) μ := by
  exact (ae_lt_top (measurable_originalHeatMass d t a)
    ((lintegral_originalHeatMass d P hP t ht a).trans_ne ENNReal.one_ne_top)).mono
      (fun μ hμ => (lintegral_ofReal_ne_top_iff_integrable
        (((continuous_originalHeatGaussian d t).comp
          (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun x => originalHeatGaussian_nonneg d t ht (a - x)))).mp hμ.ne)

theorem originalHeatField_memLp_two
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a : Rd d) (hQ : Q d P (1 / (8 * t)) ≠ ∞) :
    MemLp (originalHeatField d t a) 2 P := by
  letI : IsProbabilityMeasure P := hP.1
  exact (originalHeatMass_memLp_two d P hP t ht a hQ).sub (memLp_const (1 : ℝ))

theorem integrable_originalHeatMass_toReal
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a : Rd d) :
    Integrable (fun μ => (originalHeatMass d t a μ).toReal) P := by
  exact integrable_toReal_of_lintegral_ne_top (measurable_originalHeatMass d t a).aemeasurable
    ((lintegral_originalHeatMass d P hP t ht a).trans_ne ENNReal.one_ne_top)

theorem integral_originalHeatField
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a : Rd d) :
    (∫ μ, originalHeatField d t a μ ∂P) = 0 := by
  letI : IsProbabilityMeasure P := hP.1
  simp [originalHeatField,
    integral_sub (integrable_originalHeatMass_toReal d P hP t ht a) (integrable_const (1 : ℝ)),
    integral_originalHeatMass_toReal d P hP t ht a]

theorem integral_originalHeatField_sq
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a : Rd d) (hQ : Q d P (1 / (8 * t)) ≠ ∞) :
    (∫ μ, (originalHeatField d t a μ) ^ 2 ∂P) =
      (8 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
        ((Q d P (1 / (8 * t))).toReal + 1) - 1 := by
  letI : IsProbabilityMeasure P := hP.1
  have hpoly (z : ℝ) : (z - 1) ^ 2 = (z ^ 2 - 2 * z) + 1 := by ring
  have hZint := integrable_originalHeatMass_toReal d P hP t ht a
  have hZsq := (originalHeatMass_memLp_two d P hP t ht a hQ).integrable_sq
  simp_rw [originalHeatField, hpoly]
  rw [integral_add (f := fun μ => (originalHeatMass d t a μ).toReal ^ 2 -
      2 * (originalHeatMass d t a μ).toReal) (g := fun _ => (1 : ℝ))
      (hZsq.sub (hZint.const_mul 2)) (integrable_const (1 : ℝ)),
    integral_sub (f := fun μ => (originalHeatMass d t a μ).toReal ^ 2)
      (g := fun μ => 2 * (originalHeatMass d t a μ).toReal) hZsq (hZint.const_mul 2),
    integral_const_mul,
    integral_originalHeatMass_toReal d P hP t ht a,
    integral_originalHeatMass_toReal_sq d P hP t ht a hQ]
  norm_num
  ring

theorem originalHeatGaussian_le_wideGaussian_of_norm_sub_le_one
    (d : ℕ) (t : ℝ) (ht : 0 < t) (a b x : Rd d) (hba : ‖b - a‖ ≤ 1) :
    originalHeatGaussian d t (b - x) ≤
      (((4 * Real.pi * t) ^ (-((d : ℝ) / 2))) /
        ((4 * Real.pi * (2 * t)) ^ (-((d : ℝ) / 2))) * Real.exp (1 / (4 * t))) *
      originalHeatGaussian d (2 * t) (a - x) := by
  have htri : ‖a - x‖ ≤ ‖b - x‖ + 1 :=
    (show ‖a - x‖ ≤ ‖b - x‖ + ‖b - a‖ from by
      simpa only [dist_eq_norm, norm_sub_rev, add_comm] using dist_triangle a b x).trans
        (add_le_add le_rfl hba)
  have hsq : ‖a - x‖ ^ 2 ≤ 2 * ‖b - x‖ ^ 2 + 2 := by
    nlinarith [mul_self_le_mul_self (norm_nonneg (a - x)) htri,
      sq_nonneg (‖b - x‖ - 1)]
  have hexp : -(1 / (4 * t)) * ‖b - x‖ ^ 2 ≤
      1 / (4 * t) - ((1 / (4 * t)) / 2) * ‖a - x‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ (1 / (4 * t)) / 2 by positivity)]
  have hβ2 : 1 / (4 * (2 * t)) = (1 / (4 * t)) / 2 := by field_simp [ht.ne']
  have hκ2 : 0 < (4 * Real.pi * (2 * t)) ^ (-((d : ℝ) / 2)) := by positivity
  refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (show 0 ≤ (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) by positivity)).trans_eq ?_
  rw [originalHeatGaussian, hβ2, sub_eq_add_neg, Real.exp_add, neg_mul]
  field_simp [hκ2.ne']

theorem continuousAt_originalHeatIntegral
    (d : ℕ) (t : ℝ) (ht : 0 < t) (a : Rd d) (μ : Measure (Rd d))
    (hint : Integrable (fun x => originalHeatGaussian d (2 * t) (a - x)) μ) :
    ContinuousAt (fun b : Rd d => ∫ x, originalHeatGaussian d t (b - x) ∂μ) a := by
  let D : ℝ := (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) /
    (4 * Real.pi * (2 * t)) ^ (-((d : ℝ) / 2)) * Real.exp (1 / (4 * t))
  refine continuousAt_of_dominated (bound := fun x => D * originalHeatGaussian d (2 * t) (a - x))
    ?_ ?_ (hint.const_mul D) ?_
  case refine_2 =>
    filter_upwards [Metric.ball_mem_nhds a (show (0 : ℝ) < 1 by norm_num)] with b hb
    have hba : ‖b - a‖ ≤ 1 := le_of_lt
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hb)
    exact ae_of_all μ (fun x => by
      simpa only [D, Real.norm_eq_abs,
        abs_of_nonneg (originalHeatGaussian_nonneg d t ht (b - x))] using
          originalHeatGaussian_le_wideGaussian_of_norm_sub_le_one d t ht a b x hba)
  case refine_1 =>
    exact Eventually.of_forall (fun b =>
      (((continuous_originalHeatGaussian d t).comp
        (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable))
  exact ae_of_all μ (fun x =>
    ((continuous_originalHeatGaussian d t).comp
      (continuous_id.sub continuous_const)).continuousAt)

theorem ae_continuousAt_originalHeatMass_toReal
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (a : Rd d) :
    ∀ᵐ μ ∂P, ContinuousAt (fun b => (originalHeatMass d t b μ).toReal) a := by
  exact (ae_integrable_originalHeatGaussian_of_admissible d P hP
    (2 * t) (by positivity) a).mono (fun μ hμ => by
      simpa only [originalHeatMass_toReal_eq_integral d t ht] using
        continuousAt_originalHeatIntegral d t ht a μ hμ)

def originalHeatCovariance (d : ℕ) (P : ConfigurationLaw d) (t : ℝ) (z : Rd d) : ℝ :=
  ∫ μ, originalHeatField d t 0 μ * originalHeatField d t z μ ∂P

theorem measurable_originalHeatField (d : ℕ) (t : ℝ) (a : Rd d) :
    Measurable (originalHeatField d t a) :=
  (measurable_originalHeatMass d t a).ennreal_toReal.sub measurable_const

theorem continuous_originalHeatCovariance_of_W_ne_top_pos
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    Continuous (originalHeatCovariance d P t) := by
  letI : IsProbabilityMeasure P := hP.1
  refine continuous_iff_continuousAt.mpr (fun a => ?_)
  let Y : Measure (Rd d) → ℝ := fun μ => (originalHeatMass d (2 * t) a μ).toReal
  let D : ℝ := (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) /
    (4 * Real.pi * (2 * t)) ^ (-((d : ℝ) / 2)) * Real.exp (1 / (4 * t))
  have hD : 0 ≤ D := by positivity
  have hY : MemLp Y 2 P := originalHeatMass_memLp_two d P hP (2 * t)
    (by positivity) a (Q_ne_top_of_W_ne_top_pos d s hs P hW _ (by positivity))
  have hF0 : MemLp (originalHeatField d t 0) 2 P := originalHeatField_memLp_two d P hP t ht 0
    (Q_ne_top_of_W_ne_top_pos d s hs P hW _ (by positivity))
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
    have hXle : (originalHeatMass d t b μ).toReal ≤ D * Y μ := by
      simpa only [Y, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD] using
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ.ne) (hZle b hba μ)
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
      ((measurable_originalHeatField d t 0).mul (measurable_originalHeatField d t b)).aestronglyMeasurable)
  exact (ae_continuousAt_originalHeatMass_toReal d P hP t ht a).mono
    (fun μ hμ => continuousAt_const.mul (hμ.sub continuousAt_const))

theorem originalHeatMass_translate_measure
    (d : ℕ) (t : ℝ) (a b : Rd d) (μ : Measure (Rd d)) :
    originalHeatMass d t a (μ.map (fun x => b + x)) =
      originalHeatMass d t (a - b) μ := by
  have hsub (x : Rd d) : a - (b + x) = (a - b) - x := by abel
  exact (lintegral_map
    (((continuous_originalHeatGaussian d t).comp
      (continuous_const.sub continuous_id)).measurable.ennreal_ofReal)
    (measurable_const.add measurable_id)).trans
      (lintegral_congr (fun x => congrArg
        (fun z => ENNReal.ofReal (originalHeatGaussian d t z)) (hsub x)))

theorem originalHeatField_translate_measure
    (d : ℕ) (t : ℝ) (a b : Rd d) (μ : Measure (Rd d)) :
    originalHeatField d t a (μ.map (fun x => b + x)) =
      originalHeatField d t (a - b) μ :=
  congrArg (fun r : ℝ≥0∞ => r.toReal - 1)
    (originalHeatMass_translate_measure d t a b μ)

theorem integral_originalHeatField_mul_stationary
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (a c b : Rd d) :
    (∫ μ, originalHeatField d t (a + b) μ * originalHeatField d t (c + b) μ ∂P) =
      ∫ μ, originalHeatField d t a μ * originalHeatField d t c μ ∂P := by
  let T : Measure (Rd d) → Measure (Rd d) := fun μ => μ.map (fun x => b + x)
  have hT : Measurable T := Measure.measurable_map _ (measurable_const.add measurable_id)
  have hmap := integral_map (μ := P) hT.aemeasurable
    (((measurable_originalHeatField d t (a + b)).mul
      (measurable_originalHeatField d t (c + b))).aestronglyMeasurable)
  simpa only [hP.2.2.1 b, Pi.mul_apply, T, originalHeatField_translate_measure,
    add_sub_cancel_right] using hmap

theorem integral_originalHeatField_mul_eq_covariance
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (a b : Rd d) :
    (∫ μ, originalHeatField d t a μ * originalHeatField d t b μ ∂P) =
      originalHeatCovariance d P t (b - a) := by
  simpa only [zero_add, sub_add_cancel, originalHeatCovariance] using
    integral_originalHeatField_mul_stationary d P hP t 0 (b - a) a

theorem originalHeatCovariance_neg
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (z : Rd d) :
    originalHeatCovariance d P t (-z) = originalHeatCovariance d P t z := by
  simpa only [zero_sub, originalHeatCovariance] using
    (integral_originalHeatField_mul_eq_covariance d P hP t z 0).symm.trans
      (integral_congr_ae (Eventually.of_forall (fun μ => mul_comm
        (originalHeatField d t z μ) (originalHeatField d t 0 μ))))

theorem positiveDefinite_originalHeatCovariance_of_W_ne_top_pos
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    IsPositiveDefinite (fun z => (originalHeatCovariance d P t z : ℂ)) := by
  refine ⟨fun z => ?_, fun m x c => ?_⟩
  case refine_1 =>
    exact (congrArg Complex.ofReal (originalHeatCovariance_neg d P hP t z)).trans
      (by simp)
  case refine_2 =>
    have hLp (a : Rd d) : MemLp (originalHeatField d t a) 2 P :=
      originalHeatField_memLp_two d P hP t ht a
        (Q_ne_top_of_W_ne_top_pos d s hs P hW _ (by positivity))
    have hsum (a : Fin m → ℂ) :
        (∑ i, ∑ j, starRingEnd ℂ (a i) * a j) =
          (Complex.normSq (∑ k, a k) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
    have hC (i j : Fin m) :
        (originalHeatCovariance d P t (x i - x j) : ℂ) =
          ∫ μ, ((originalHeatField d t (x i) μ * originalHeatField d t (x j) μ : ℝ) : ℂ) ∂P := by
      exact (congrArg Complex.ofReal
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
            ∫ μ, (Complex.normSq (∑ k, c k * (originalHeatField d t (x k) μ : ℂ)) : ℂ) ∂P := by
      exact (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
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

theorem positiveDefinite_nonneg_real_mul
    {V : Type*} [AddGroup V] {φ : V → ℂ}
    (hφ : IsPositiveDefinite φ) (r : ℝ) (hr : 0 ≤ r) :
    IsPositiveDefinite (fun z => (r : ℂ) * φ z) := by
  refine ⟨fun z => ?_, fun m x c => ?_⟩
  case refine_1 =>
    simpa only [map_mul, Complex.conj_ofReal] using
      congrArg (fun w : ℂ => (r : ℂ) * w) (hφ.hermitian z)
  case refine_2 =>
    have hsum : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ((r : ℂ) * φ (x i - x j))) =
        (r : ℂ) * (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j)) := by
      simp only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    simpa only [hsum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using mul_nonneg hr (hφ.nonneg m x c)

theorem exists_finiteMeasure_charFun_of_real_continuous_pd
    (d : ℕ) (C : Rd d → ℝ) (hC : Continuous C)
    (hp : IsPositiveDefinite (fun z => (C z : ℂ))) :
    ∃ σ : FiniteMeasure (Rd d), ∀ z, charFun (σ : Measure (Rd d)) z = (C z : ℂ) := by
  have hC0 : 0 ≤ C 0 := hp.eval_zero_nonneg
  by_cases hzero : C 0 = 0
  case pos =>
    have hvanish (z : Rd d) : (C z : ℂ) = 0 := norm_eq_zero.mp
      (le_antisymm (by simpa only [Complex.ofReal_re, hzero] using hp.bounded_by_zero z)
        (norm_nonneg _))
    exact ⟨0, fun z => by simp only [FiniteMeasure.toMeasure_zero, charFun_zero_measure, hvanish]⟩
  case neg =>
    let φ : Rd d → ℂ := fun z => (((C 0)⁻¹ : ℝ) : ℂ) * (C z : ℂ)
    have hφcont : Continuous φ := continuous_const.mul (Complex.continuous_ofReal.comp hC)
    have hφpd : IsPositiveDefinite φ :=
      positiveDefinite_nonneg_real_mul hp ((C 0)⁻¹) (inv_nonneg.mpr hC0)
    have hφ0 : φ 0 = 1 := by
      simp only [φ, ← Complex.ofReal_mul, inv_mul_cancel₀ hzero, Complex.ofReal_one]
    obtain ⟨π, hπ, _⟩ := bochner_theorem φ hφcont hφpd hφ0
    let v : NNReal := ⟨C 0, hC0⟩
    refine ⟨v • π.toFiniteMeasure, fun z => ?_⟩
    change (∫ k, Complex.exp ((inner ℝ k z : ℝ) * Complex.I) ∂(v • (π : Measure (Rd d)))) = (C z : ℂ)
    rw [integral_smul_nnreal_measure]
    change (C 0 : ℂ) * charFun (π : Measure (Rd d)) z = (C z : ℂ)
    simp only [hπ z, φ, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hzero,
      one_mul]

theorem finiteMeasure_eq_of_charFun_eq (d : ℕ) (σ τ : FiniteMeasure (Rd d))
    (h : ∀ z, charFun (σ : Measure (Rd d)) z = charFun (τ : Measure (Rd d)) z) : σ = τ :=
  FiniteMeasure.toMeasure_injective (Measure.ext_of_charFun (funext h))

/-- The finite spectral measure of the original law's centered heat field.
The characteristic function uses the angular frequency convention of Bochner. -/
def originalHeatSpectrum
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    FiniteMeasure (Rd d) :=
  Classical.choose (exists_finiteMeasure_charFun_of_real_continuous_pd d
    (originalHeatCovariance d P t)
    (continuous_originalHeatCovariance_of_W_ne_top_pos d s hs P hP hW t ht)
    (positiveDefinite_originalHeatCovariance_of_W_ne_top_pos d s hs P hP hW t ht))

theorem charFun_originalHeatSpectrum
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t)
    (z : Rd d) :
    charFun (originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)) z =
      (originalHeatCovariance d P t z : ℂ) :=
  Classical.choose_spec (exists_finiteMeasure_charFun_of_real_continuous_pd d
    (originalHeatCovariance d P t)
    (continuous_originalHeatCovariance_of_W_ne_top_pos d s hs P hP hW t ht)
    (positiveDefinite_originalHeatCovariance_of_W_ne_top_pos d s hs P hP hW t ht)) z

theorem originalHeatCovariance_zero
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (hQ : Q d P (1 / (8 * t)) ≠ ∞) :
    originalHeatCovariance d P t 0 =
      (8 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
        ((Q d P (1 / (8 * t))).toReal + 1) - 1 := by
  simpa only [originalHeatCovariance, pow_two] using
    integral_originalHeatField_sq d P hP t ht 0 hQ

theorem real_mass_originalHeatSpectrum
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    (originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)).real Set.univ =
      originalHeatCovariance d P t 0 :=
  congrArg Complex.re ((charFun_zero _).symm.trans
    (charFun_originalHeatSpectrum d s hs P hP hW t ht 0))

theorem mass_originalHeatSpectrum
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    (originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)) Set.univ =
      ENNReal.ofReal (originalHeatCovariance d P t 0) :=
  (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm.trans
    (congrArg ENNReal.ofReal (real_mass_originalHeatSpectrum d s hs P hP hW t ht))

theorem originalHeatSpectrum_eq_of_exponent
    (d : ℕ) (s r : ℝ) (hs : 0 < s) (hr : 0 < r) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hWs : W d s P ≠ ⊤) (hWr : W d r P ≠ ⊤)
    (t : ℝ) (ht : 0 < t) :
    originalHeatSpectrum d s hs P hP hWs t ht =
      originalHeatSpectrum d r hr P hP hWr t ht :=
  finiteMeasure_eq_of_charFun_eq d _ _ (fun z =>
    (charFun_originalHeatSpectrum d s hs P hP hWs t ht z).trans
      (charFun_originalHeatSpectrum d r hr P hP hWr t ht z).symm)

theorem map_neg_originalHeatSpectrum
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    (originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)).map (fun k => -k) =
      (originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)) := by
  exact Measure.ext_of_charFun (funext (fun z =>
    (show charFun ((originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)).map
        (fun k => -k)) z =
          charFun (originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)) (-z) from by
      simpa only [neg_one_smul] using
        charFun_map_smul (μ := (originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d))) (-1) z).trans
      ((charFun_originalHeatSpectrum d s hs P hP hW t ht (-z)).trans
        ((congrArg Complex.ofReal (originalHeatCovariance_neg d P hP t z)).trans
          (charFun_originalHeatSpectrum d s hs P hP hW t ht z).symm))))

end Riesz.Stationary
