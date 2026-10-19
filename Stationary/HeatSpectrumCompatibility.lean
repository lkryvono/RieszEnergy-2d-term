import Riesz.Stationary.GaussianMoments
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
Gaussian convolution for the actual original simple law, its absolutely
integrable covariance semigroup, and compatibility of the finite heat spectra.
The common angular spectral measure is sigma-finite and locally finite; damping
it by `exp (-(2 * t) * ‖k‖ ^ 2)` recovers the actual heat spectrum for every `t > 0`.
Compact-pair heat removal and singular-energy convergence remain separate.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration
open scoped ENNReal Classical Topology RealInnerProductSpace InnerProductSpace

namespace Riesz.Stationary

theorem gaussian_weighted_complete_square
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (α β : ℝ) (hs : α + β ≠ 0) (a b x : V) :
    α * ‖a - x‖ ^ 2 + β * ‖b - x‖ ^ 2 =
      (α + β) * ‖x - ((α / (α + β)) • a + (β / (α + β)) • b)‖ ^ 2 +
        (α * β / (α + β)) * ‖a - b‖ ^ 2 := by
  simp only [norm_sub_sq_real, norm_add_sq_real, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, inner_add_right,
    real_inner_smul_right, real_inner_comm]
  field_simp [hs]
  ring

theorem lintegral_unequal_rawGaussians
    (d : ℕ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (a b : Rd d) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-α * ‖a - x‖ ^ 2)) *
      ENNReal.ofReal (Real.exp (-β * ‖b - x‖ ^ 2)) ∂volume) =
      ENNReal.ofReal (Real.exp (-(α * β / (α + β)) * ‖a - b‖ ^ 2)) *
        ENNReal.ofReal (B d (α + β)) := by
  have hs : 0 < α + β := add_pos hα hβ
  have hfactor (x : Rd d) :
      Real.exp (-α * ‖a - x‖ ^ 2) * Real.exp (-β * ‖b - x‖ ^ 2) =
        Real.exp (-(α * β / (α + β)) * ‖a - b‖ ^ 2) *
          Real.exp (-(α + β) *
            ‖x - ((α / (α + β)) • a + (β / (α + β)) • b)‖ ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact congrArg Real.exp (by
      nlinarith only [gaussian_weighted_complete_square α β hs.ne' a b x])
  exact (lintegral_congr (fun x =>
    (ENNReal.ofReal_mul (Real.exp_pos (-α * ‖a - x‖ ^ 2)).le).symm.trans
      ((congrArg ENNReal.ofReal (hfactor x)).trans
        (ENNReal.ofReal_mul (Real.exp_pos _).le)))).trans
          ((lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
            (congrArg (fun q : ℝ≥0∞ =>
              ENNReal.ofReal (Real.exp (-(α * β / (α + β)) * ‖a - b‖ ^ 2)) * q)
                (by simpa only [neg_mul] using (lintegral_gaussian_translate d (α + β) hs
                  ((α / (α + β)) • a + (β / (α + β)) • b)))))

theorem heatGaussian_mixed_constant
    (d : ℕ) (t v : ℝ) (ht : 0 < t) (hv : 0 < v) :
    (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
        (4 * Real.pi * v) ^ (-((d : ℝ) / 2)) * B d (1 / (4 * t) + 1 / (4 * v)) =
      (4 * Real.pi * (t + v)) ^ (-((d : ℝ) / 2)) := by
  have hbase : (Real.pi / (1 / (4 * t) + 1 / (4 * v))) /
      ((4 * Real.pi * t) * (4 * Real.pi * v)) = (4 * Real.pi * (t + v))⁻¹ := by
    field_simp [ht.ne', hv.ne', (add_pos ht hv).ne', Real.pi_ne_zero]
    ring
  have heq : (Real.pi / (1 / (4 * t) + 1 / (4 * v))) ^ ((d : ℝ) / 2) /
      ((4 * Real.pi * t) ^ ((d : ℝ) / 2) * (4 * Real.pi * v) ^ ((d : ℝ) / 2)) =
        (4 * Real.pi * (t + v)) ^ (-((d : ℝ) / 2)) := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi * t)
      (by positivity : 0 ≤ 4 * Real.pi * v),
      ← Real.div_rpow (by positivity : 0 ≤ Real.pi / (1 / (4 * t) + 1 / (4 * v)))
        (by positivity : 0 ≤ (4 * Real.pi * t) * (4 * Real.pi * v)),
      hbase, Real.inv_rpow (by positivity : 0 ≤ 4 * Real.pi * (t + v)),
      Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi * (t + v))]
  rw [Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi * t),
    Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi * v)]
  simpa only [B, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using heq

theorem lintegral_originalHeatGaussian_mul
    (d : ℕ) (t v : ℝ) (ht : 0 < t) (hv : 0 < v) (a b : Rd d) :
    (∫⁻ x, ENNReal.ofReal (originalHeatGaussian d t (a - x)) *
      ENNReal.ofReal (originalHeatGaussian d v (b - x)) ∂volume) =
      ENNReal.ofReal (originalHeatGaussian d (t + v) (b - a)) := by
  have htime : (1 / (4 * t)) * (1 / (4 * v)) / (1 / (4 * t) + 1 / (4 * v)) =
      1 / (4 * (t + v)) := by
    field_simp [ht.ne', hv.ne', (add_pos ht hv).ne']
    ring
  have hpoint (x : Rd d) :
      ENNReal.ofReal (originalHeatGaussian d t (a - x)) *
        ENNReal.ofReal (originalHeatGaussian d v (b - x)) =
      ENNReal.ofReal ((4 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
        (4 * Real.pi * v) ^ (-((d : ℝ) / 2))) *
          (ENNReal.ofReal (Real.exp (-(1 / (4 * t)) * ‖a - x‖ ^ 2)) *
            ENNReal.ofReal (Real.exp (-(1 / (4 * v)) * ‖b - x‖ ^ 2))) := by
    rw [originalHeatGaussian, originalHeatGaussian,
      ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.pi * t) ^ (-((d : ℝ) / 2))),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.pi * v) ^ (-((d : ℝ) / 2))),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.pi * t) ^ (-((d : ℝ) / 2)))]
    ring
  have heval := (lintegral_congr (μ := (volume : Measure (Rd d))) hpoint).trans
    ((lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
      (congrArg (fun q : ℝ≥0∞ =>
        ENNReal.ofReal ((4 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
          (4 * Real.pi * v) ^ (-((d : ℝ) / 2))) * q)
            (lintegral_unequal_rawGaussians d (1 / (4 * t)) (1 / (4 * v))
              (by positivity) (by positivity) a b)))
  refine heval.trans ?_
  rw [htime, mul_left_comm
    (ENNReal.ofReal ((4 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
      (4 * Real.pi * v) ^ (-((d : ℝ) / 2))))
    (ENNReal.ofReal (Real.exp (-(1 / (4 * (t + v))) * ‖a - b‖ ^ 2))),
    ← ENNReal.ofReal_mul (by positivity :
      0 ≤ (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) * (4 * Real.pi * v) ^ (-((d : ℝ) / 2))),
    heatGaussian_mixed_constant d t v ht hv,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp only [originalHeatGaussian, norm_sub_rev, mul_comm]

theorem originalHeatGaussian_neg (d : ℕ) (t : ℝ) (x : Rd d) :
    originalHeatGaussian d t (-x) = originalHeatGaussian d t x := by
  simp only [originalHeatGaussian, norm_neg]

theorem lintegral_originalHeatGaussian_convolution
    (d : ℕ) (h t : ℝ) (hh : 0 < h) (ht : 0 < t) (w : Rd d) :
    (∫⁻ x, ENNReal.ofReal (originalHeatGaussian d h x) *
      ENNReal.ofReal (originalHeatGaussian d t (w - x)) ∂volume) =
        ENNReal.ofReal (originalHeatGaussian d (h + t) w) := by
  simpa only [zero_sub, originalHeatGaussian_neg, sub_zero] using
    lintegral_originalHeatGaussian_mul d h t hh ht 0 w

theorem originalHeat_shifted_pair_norm_identity
    (d : ℕ) (a b z : Rd d) :
    ‖a‖ ^ 2 + ‖z - b‖ ^ 2 =
      ‖(1 / 2 : ℝ) • z - a‖ ^ 2 + ‖(1 / 2 : ℝ) • z - b‖ ^ 2 +
        (‖(b - a) - z‖ ^ 2 - ‖b - a‖ ^ 2) / 2 := by
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_left, real_inner_smul_right,
    real_inner_comm]
  ring

theorem originalHeatGaussian_shifted_pair
    (d : ℕ) (t : ℝ) (ht : 0 < t) (a b z : Rd d) :
    originalHeatGaussian d t (-a) * originalHeatGaussian d t (z - b) =
      (originalHeatGaussian d t ((1 / 2 : ℝ) • z - a) *
        originalHeatGaussian d t ((1 / 2 : ℝ) • z - b)) *
          Real.exp (-(1 / (8 * t)) * (‖(b - a) - z‖ ^ 2 - ‖b - a‖ ^ 2)) := by
  have hparam : 1 / (8 * t) = (1 / (4 * t)) / 2 := by
    field_simp [ht.ne']
    norm_num
  have hE :
      Real.exp (-(1 / (4 * t)) * ‖a‖ ^ 2) * Real.exp (-(1 / (4 * t)) * ‖z - b‖ ^ 2) =
        (Real.exp (-(1 / (4 * t)) * ‖(1 / 2 : ℝ) • z - a‖ ^ 2) *
          Real.exp (-(1 / (4 * t)) * ‖(1 / 2 : ℝ) • z - b‖ ^ 2)) *
            Real.exp (-(1 / (8 * t)) * (‖(b - a) - z‖ ^ 2 - ‖b - a‖ ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hparam]
    exact congrArg Real.exp (by
      linear_combination -(1 / (4 * t)) * originalHeat_shifted_pair_norm_identity d a b z)
  simp only [originalHeatGaussian, norm_neg]
  rw [mul_mul_mul_comm ((4 * Real.pi * t) ^ (-((d : ℝ) / 2))) _
    ((4 * Real.pi * t) ^ (-((d : ℝ) / 2))) _, hE]
  ring

theorem nonnegativeWindowOverlap_originalHeatGaussian_corrected
    (d : ℕ) (t : ℝ) (ht : 0 < t) (z w : Rd d) :
    nonnegativeWindowOverlap d
      (fun x => ENNReal.ofReal (originalHeatGaussian d t ((1 / 2 : ℝ) • z - x))) w *
        ENNReal.ofReal (Real.exp (-(1 / (8 * t)) * (‖w - z‖ ^ 2 - ‖w‖ ^ 2))) =
      ENNReal.ofReal (originalHeatGaussian d (2 * t) (w - z)) := by
  rw [nonnegativeWindowOverlap_originalHeatGaussian d t ht, mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  have he : -(1 / (8 * t)) * ‖w‖ ^ 2 +
      -(1 / (8 * t)) * (‖w - z‖ ^ 2 - ‖w‖ ^ 2) =
        -(1 / (8 * t)) * ‖w - z‖ ^ 2 := by ring
  rw [he, originalHeatGaussian, show 4 * Real.pi * (2 * t) = 8 * Real.pi * t by ring,
    show 4 * (2 * t) = 8 * t by ring]
  exact (ENNReal.ofReal_mul (by positivity : 0 ≤ (8 * Real.pi * t) ^ (-((d : ℝ) / 2)))).symm

def originalHeatPairProfile (d : ℕ) (P : ConfigurationLaw d)
    (hP : Admissible d P) (t : ℝ) (z : Rd d) : ℝ≥0∞ :=
  ∫⁻ p, (cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
    ENNReal.ofReal (originalHeatGaussian d (2 * t) ((p.2 - p.1) - z))
      ∂originalAdmissibleFactorialMeasure d P hP

def originalHeatSecondProfile (d : ℕ) (P : ConfigurationLaw d)
    (hP : Admissible d P) (t : ℝ) (z : Rd d) : ℝ≥0∞ :=
  originalHeatPairProfile d P hP t z +
    ENNReal.ofReal (originalHeatGaussian d (2 * t) z)

theorem measurable_originalHeatPairProfile
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P) (t : ℝ) :
    Measurable (originalHeatPairProfile d P hP t) := by
  exact (((measurable_const.indicator (Riesz.Negative.measurableSet_cube d 1)).comp
    (measurable_fst.comp measurable_snd)).mul
      (((continuous_originalHeatGaussian d (2 * t)).comp
        (((continuous_snd.comp continuous_snd).sub
          (continuous_fst.comp continuous_snd)).sub continuous_fst)).measurable.ennreal_ofReal)).lintegral_prod_right'

theorem measurable_originalHeatSecondProfile
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P) (t : ℝ) :
    Measurable (originalHeatSecondProfile d P hP t) :=
  (measurable_originalHeatPairProfile d P hP t).add
    (continuous_originalHeatGaussian d (2 * t)).measurable.ennreal_ofReal

theorem originalHeatPairProfile_eq_pair_lintegral
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (z : Rd d) :
    originalHeatPairProfile d P hP t z =
      ∫⁻ p, ENNReal.ofReal (originalHeatGaussian d t (-p.1)) *
        ENNReal.ofReal (originalHeatGaussian d t (z - p.2))
          ∂originalAdmissibleFactorialMeasure d P hP := by
  let c : Rd d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (originalHeatGaussian d t ((1 / 2 : ℝ) • z - x))
  let g : Rd d → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (Real.exp (-(1 / (8 * t)) * (‖w - z‖ ^ 2 - ‖w‖ ^ 2)))
  have hstation := lintegral_stationaryPair_window_eq_cube_overlap d
    (originalAdmissibleFactorialMeasure d P hP)
    (originalAdmissibleFactorialMeasure_map_diagAdd_eq_self d P hP) c g
    (((continuous_originalHeatGaussian d t).comp
      (continuous_const.sub continuous_id)).measurable.ennreal_ofReal)
    ((Real.continuous_exp.comp (continuous_const.mul
      (((continuous_id.sub continuous_const).norm.pow 2).sub
        (continuous_id.norm.pow 2)))).measurable.ennreal_ofReal)
  have hpoint (p : Rd d × Rd d) :
      ENNReal.ofReal (originalHeatGaussian d t (-p.1)) *
        ENNReal.ofReal (originalHeatGaussian d t (z - p.2)) =
          c p.1 * c p.2 * g (p.2 - p.1) := by
    exact (ENNReal.ofReal_mul (originalHeatGaussian_nonneg d t ht (-p.1))).symm.trans
      ((congrArg ENNReal.ofReal (originalHeatGaussian_shifted_pair d t ht p.1 p.2 z)).trans
        ((ENNReal.ofReal_mul (mul_nonneg
          (originalHeatGaussian_nonneg d t ht ((1 / 2 : ℝ) • z - p.1))
          (originalHeatGaussian_nonneg d t ht ((1 / 2 : ℝ) • z - p.2)))).trans
            (congrArg (fun q : ℝ≥0∞ => q * g (p.2 - p.1))
              (ENNReal.ofReal_mul
                (originalHeatGaussian_nonneg d t ht ((1 / 2 : ℝ) • z - p.1))))))
  exact ((lintegral_congr hpoint).trans (hstation.trans
    (lintegral_congr (fun p => (mul_assoc _ _ _).trans
      (congrArg ((cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 * ·)
        (nonnegativeWindowOverlap_originalHeatGaussian_corrected d t ht z (p.2 - p.1))))))).symm

theorem originalHeatSecondProfile_eq_mass_product_lintegral
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (z : Rd d) :
    originalHeatSecondProfile d P hP t z =
      ∫⁻ μ, originalHeatMass d t 0 μ * originalHeatMass d t z μ ∂P := by
  have hdiag : (∫⁻ x, ENNReal.ofReal (originalHeatGaussian d t (-x)) *
      ENNReal.ofReal (originalHeatGaussian d t (z - x)) ∂volume) =
        ENNReal.ofReal (originalHeatGaussian d (2 * t) z) := by
    simpa only [zero_sub, sub_zero, show t + t = 2 * t by ring] using
      lintegral_originalHeatGaussian_mul d t t ht ht 0 z
  simpa only [originalHeatSecondProfile, originalHeatPairProfile_eq_pair_lintegral d P hP t ht z,
    originalHeatMass, zero_sub, hdiag] using
      (originalAdmissible_mass_product_expectation d P hP
        (fun x => ENNReal.ofReal (originalHeatGaussian d t (-x)))
        (fun x => ENNReal.ofReal (originalHeatGaussian d t (z - x)))
        (((continuous_originalHeatGaussian d t).comp continuous_neg).measurable.ennreal_ofReal)
        (((continuous_originalHeatGaussian d t).comp
          (continuous_const.sub continuous_id)).measurable.ennreal_ofReal)).symm

theorem originalHeatSecondProfile_ne_top
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (hQ : Q d P (1 / (8 * t)) ≠ ∞) (z : Rd d) :
    originalHeatSecondProfile d P hP t z ≠ ∞ := by
  exact (originalHeatSecondProfile_eq_mass_product_lintegral d P hP t ht z).trans_ne
    ((integrable_toReal_iff
      ((measurable_originalHeatMass d t 0).mul
        (measurable_originalHeatMass d t z)).aemeasurable
      (((ae_lt_top (measurable_originalHeatMass d t 0)
        ((lintegral_originalHeatMass d P hP t ht 0).trans_ne ENNReal.one_ne_top)).and
          (ae_lt_top (measurable_originalHeatMass d t z)
            ((lintegral_originalHeatMass d P hP t ht z).trans_ne ENNReal.one_ne_top))).mono
              (fun μ hμ => ENNReal.mul_ne_top hμ.1.ne hμ.2.ne))).mp
      (((originalHeatMass_memLp_two d P hP t ht 0 hQ).integrable_mul
        (originalHeatMass_memLp_two d P hP t ht z hQ)).congr
          (Eventually.of_forall (fun μ => ENNReal.toReal_mul.symm))))

theorem originalHeatCovariance_eq_secondProfile_toReal
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t : ℝ) (ht : 0 < t) (hQ : Q d P (1 / (8 * t)) ≠ ∞) (z : Rd d) :
    originalHeatCovariance d P t z =
      (originalHeatSecondProfile d P hP t z).toReal - 1 := by
  letI : IsProbabilityMeasure P := hP.1
  have hprod : (∫ μ, (originalHeatMass d t 0 μ).toReal * (originalHeatMass d t z μ).toReal ∂P) =
      (originalHeatSecondProfile d P hP t z).toReal := by
    exact (integral_congr_ae (Eventually.of_forall (fun μ => ENNReal.toReal_mul.symm))).trans
      ((integral_toReal
        ((measurable_originalHeatMass d t 0).mul (measurable_originalHeatMass d t z)).aemeasurable
        (ae_lt_top ((measurable_originalHeatMass d t 0).mul (measurable_originalHeatMass d t z))
          ((originalHeatSecondProfile_eq_mass_product_lintegral d P hP t ht z).symm.trans_ne
            (originalHeatSecondProfile_ne_top d P hP t ht hQ z)))).trans
              (congrArg ENNReal.toReal
                (originalHeatSecondProfile_eq_mass_product_lintegral d P hP t ht z).symm))
  simpa only [ProbabilityTheory.covariance, originalHeatCovariance, originalHeatField,
    integral_originalHeatMass_toReal d P hP t ht 0,
    integral_originalHeatMass_toReal d P hP t ht z, Pi.mul_apply, mul_one, hprod] using
      ProbabilityTheory.covariance_eq_sub
        (originalHeatMass_memLp_two d P hP t ht 0 hQ)
        (originalHeatMass_memLp_two d P hP t ht z hQ)

theorem lintegral_originalHeatPairProfile_convolution_centered
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t h : ℝ) (ht : 0 < t) (hh : 0 < h) (z : Rd d) :
    (∫⁻ r, ENNReal.ofReal (originalHeatGaussian d (2 * h) (z - r)) *
      originalHeatPairProfile d P hP t r ∂volume) =
      originalHeatPairProfile d P hP (t + h) z := by
  have hkernel : Measurable (fun q : Rd d × (Rd d × Rd d) =>
      ENNReal.ofReal (originalHeatGaussian d (2 * h) (z - q.1)) *
        ((cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) q.2.1 *
          ENNReal.ofReal (originalHeatGaussian d (2 * t) ((q.2.2 - q.2.1) - q.1)))) :=
    (((continuous_originalHeatGaussian d (2 * h)).comp
      (continuous_const.sub continuous_fst)).measurable.ennreal_ofReal).mul
        (((measurable_const.indicator (Riesz.Negative.measurableSet_cube d 1)).comp
          (measurable_fst.comp measurable_snd)).mul
            (((continuous_originalHeatGaussian d (2 * t)).comp
              (((continuous_snd.comp continuous_snd).sub
                (continuous_fst.comp continuous_snd)).sub continuous_fst)).measurable.ennreal_ofReal))
  have hinner (p : Rd d × Rd d) :
      (∫⁻ r, ENNReal.ofReal (originalHeatGaussian d (2 * h) (z - r)) *
        ((cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
          ENNReal.ofReal (originalHeatGaussian d (2 * t) ((p.2 - p.1) - r))) ∂volume) =
        (cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
          ENNReal.ofReal (originalHeatGaussian d (2 * (t + h)) ((p.2 - p.1) - z)) := by
    exact (lintegral_congr (fun r => mul_left_comm _ _ _)).trans
      ((lintegral_const_mul
        (f := fun r : Rd d => ENNReal.ofReal (originalHeatGaussian d (2 * h) (z - r)) *
          ENNReal.ofReal (originalHeatGaussian d (2 * t) ((p.2 - p.1) - r))) _
        ((((continuous_originalHeatGaussian d (2 * h)).comp
          (continuous_const.sub continuous_id)).measurable.ennreal_ofReal).mul
            (((continuous_originalHeatGaussian d (2 * t)).comp
              (continuous_const.sub continuous_id)).measurable.ennreal_ofReal))).trans
                (congrArg ((cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 * ·)
                  (by simpa only [show 2 * h + 2 * t = 2 * (t + h) by ring] using
                    (lintegral_originalHeatGaussian_mul d (2 * h) (2 * t)
                      (by positivity) (by positivity) z (p.2 - p.1)))))
  exact (lintegral_congr (fun r =>
    (lintegral_const_mul' (μ := originalAdmissibleFactorialMeasure d P hP)
      (ENNReal.ofReal (originalHeatGaussian d (2 * h) (z - r)))
      (fun p : Rd d × Rd d => (cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
        ENNReal.ofReal (originalHeatGaussian d (2 * t) ((p.2 - p.1) - r)))
      ENNReal.ofReal_ne_top).symm)).trans
        ((lintegral_lintegral_swap (μ := (volume : Measure (Rd d)))
          (ν := originalAdmissibleFactorialMeasure d P hP)
          (f := fun r p => ENNReal.ofReal (originalHeatGaussian d (2 * h) (z - r)) *
            ((cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
              ENNReal.ofReal (originalHeatGaussian d (2 * t) ((p.2 - p.1) - r))))
          hkernel.aemeasurable).trans
            (lintegral_congr hinner))

theorem lintegral_originalHeatPairProfile_convolution
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t h : ℝ) (ht : 0 < t) (hh : 0 < h) (z : Rd d) :
    (∫⁻ x, ENNReal.ofReal (originalHeatGaussian d (2 * h) x) *
      originalHeatPairProfile d P hP t (z - x) ∂volume) =
      originalHeatPairProfile d P hP (t + h) z := by
  simpa only [sub_sub_cancel] using
    (lintegral_sub_left_eq_self (μ := (volume : Measure (Rd d)))
      (fun r : Rd d => ENNReal.ofReal (originalHeatGaussian d (2 * h) (z - r)) *
        originalHeatPairProfile d P hP t r) z).trans
          (lintegral_originalHeatPairProfile_convolution_centered d P hP t h ht hh z)

theorem lintegral_originalHeatSecondProfile_convolution
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t h : ℝ) (ht : 0 < t) (hh : 0 < h) (z : Rd d) :
    (∫⁻ x, ENNReal.ofReal (originalHeatGaussian d (2 * h) x) *
      originalHeatSecondProfile d P hP t (z - x) ∂volume) =
      originalHeatSecondProfile d P hP (t + h) z := by
  simp only [originalHeatSecondProfile, mul_add]
  rw [lintegral_add_left
    (f := fun x : Rd d => ENNReal.ofReal (originalHeatGaussian d (2 * h) x) *
      originalHeatPairProfile d P hP t (z - x))
    (((continuous_originalHeatGaussian d (2 * h)).measurable.ennreal_ofReal).mul
      ((measurable_originalHeatPairProfile d P hP t).comp
        (measurable_const.sub measurable_id))),
    lintegral_originalHeatPairProfile_convolution d P hP t h ht hh z,
    lintegral_originalHeatGaussian_convolution d (2 * h) (2 * t)
      (by positivity) (by positivity),
    show 2 * h + 2 * t = 2 * t + 2 * h by ring]

theorem lintegral_originalHeatGaussian_unshifted
    (d : ℕ) (r : ℝ) (hr : 0 < r) :
    (∫⁻ x : Rd d, ENNReal.ofReal (originalHeatGaussian d r x) ∂volume) = 1 := by
  simpa only [zero_sub, originalHeatGaussian_neg] using
    lintegral_originalHeatGaussian d r hr (0 : Rd d)

theorem integrable_originalHeatGaussian (d : ℕ) (r : ℝ) (hr : 0 < r) :
    Integrable (originalHeatGaussian d r) volume := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    (continuous_originalHeatGaussian d r).measurable.aestronglyMeasurable
    (Eventually.of_forall (originalHeatGaussian_nonneg d r hr))).mp
      ((lintegral_originalHeatGaussian_unshifted d r hr).trans_ne ENNReal.one_ne_top)

theorem integral_originalHeatGaussian (d : ℕ) (r : ℝ) (hr : 0 < r) :
    (∫ x : Rd d, originalHeatGaussian d r x ∂volume) = 1 := by
  exact (integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (originalHeatGaussian_nonneg d r hr))
    (continuous_originalHeatGaussian d r).measurable.aestronglyMeasurable).trans
      ((congrArg ENNReal.toReal (lintegral_originalHeatGaussian_unshifted d r hr)).trans
        ENNReal.toReal_one)

theorem originalHeatCovariance_eq_convolution_of_Q_ne_top
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (t h : ℝ) (ht : 0 < t) (hh : 0 < h)
    (hQt : Q d P (1 / (8 * t)) ≠ ∞)
    (hQth : Q d P (1 / (8 * (t + h))) ≠ ∞) (z : Rd d) :
    Integrable (fun x => originalHeatGaussian d (2 * h) x *
      originalHeatCovariance d P t (z - x)) volume ∧
      originalHeatCovariance d P (t + h) z =
        ∫ x, originalHeatGaussian d (2 * h) x *
          originalHeatCovariance d P t (z - x) ∂volume := by
  let G : Rd d → ℝ≥0∞ := fun x => ENNReal.ofReal (originalHeatGaussian d (2 * h) x) *
    originalHeatSecondProfile d P hP t (z - x)
  have hGm : Measurable G :=
    (continuous_originalHeatGaussian d (2 * h)).measurable.ennreal_ofReal.mul
      ((measurable_originalHeatSecondProfile d P hP t).comp
        (measurable_const.sub measurable_id))
  have hconv : (∫⁻ x, G x ∂volume) = originalHeatSecondProfile d P hP (t + h) z :=
    lintegral_originalHeatSecondProfile_convolution d P hP t h ht hh z
  have hGfinite : (∫⁻ x, G x ∂volume) ≠ ∞ := hconv.trans_ne
    (originalHeatSecondProfile_ne_top d P hP (t + h) (add_pos ht hh) hQth z)
  have hGint : Integrable (fun x => (G x).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hGfinite
  have hGmean : (∫ x, (G x).toReal ∂volume) =
      (originalHeatSecondProfile d P hP (t + h) z).toReal :=
    (integral_toReal hGm.aemeasurable (ae_lt_top hGm hGfinite)).trans
      (congrArg ENNReal.toReal hconv)
  have hpoint (x : Rd d) : originalHeatGaussian d (2 * h) x *
      originalHeatCovariance d P t (z - x) = (G x).toReal - originalHeatGaussian d (2 * h) x := by
    simp only [originalHeatCovariance_eq_secondProfile_toReal d P hP t ht hQt (z - x),
      G, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (originalHeatGaussian_nonneg d (2 * h) (by positivity) x),
      mul_sub, mul_one]
  refine ⟨(hGint.sub (integrable_originalHeatGaussian d (2 * h) (by positivity))).congr
    (Eventually.of_forall (fun x => (hpoint x).symm)), ?_⟩
  rw [originalHeatCovariance_eq_secondProfile_toReal d P hP (t + h) (add_pos ht hh) hQth z,
    integral_congr_ae (Eventually.of_forall hpoint),
    integral_sub hGint (integrable_originalHeatGaussian d (2 * h) (by positivity)),
    hGmean, integral_originalHeatGaussian d (2 * h) (by positivity)]

theorem originalHeatCovariance_eq_convolution_of_W_ne_top_pos
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (t h : ℝ) (ht : 0 < t) (hh : 0 < h) (z : Rd d) :
    Integrable (fun x => originalHeatGaussian d (2 * h) x *
      originalHeatCovariance d P t (z - x)) volume ∧
      originalHeatCovariance d P (t + h) z =
        ∫ x, originalHeatGaussian d (2 * h) x *
          originalHeatCovariance d P t (z - x) ∂volume := by
  exact originalHeatCovariance_eq_convolution_of_Q_ne_top d P hP t h ht hh
    (Q_ne_top_of_W_ne_top_pos d s hs P hW _ (by positivity))
    (Q_ne_top_of_W_ne_top_pos d s hs P hW _ (by positivity)) z

theorem integral_originalHeatGaussian_mul_angularExp
    (d : ℕ) (r : ℝ) (hr : 0 < r) (k : Rd d) :
    (∫ x : Rd d, (originalHeatGaussian d r x : ℂ) *
      Complex.exp ((⟪x, k⟫_ℝ : ℂ) * Complex.I) ∂volume) =
        (Real.exp (-r * ‖k‖ ^ 2) : ℂ) := by
  let b : ℝ := 1 / (4 * r)
  have hb : 0 < b := div_pos zero_lt_one (mul_pos (by norm_num) hr)
  have hB : 0 < B d b := Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _
  have hpoint (x : Rd d) :
      (originalHeatGaussian d r x : ℂ) *
          Complex.exp ((⟪x, k⟫_ℝ : ℂ) * Complex.I) =
        (((B d b)⁻¹ : ℝ) : ℂ) * Complex.exp
          (-(b : ℂ) * (‖x‖ : ℂ) ^ 2 + Complex.I * (⟪k, x⟫_ℝ : ℂ)) := by
    simp only [originalHeatGaussian, heatGaussian_constant_eq_inv_B d r hr,
      Complex.ofReal_mul]
    rw [mul_assoc, Complex.ofReal_exp, ← Complex.exp_add, real_inner_comm x k]
    simp only [b, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_comm]
  have hpow : (Real.pi / (b : ℂ)) ^ ((d : ℂ) / 2) = (B d b : ℂ) := by
    simpa only [B, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_ofNat] using
        (Complex.ofReal_cpow (div_pos Real.pi_pos hb).le ((d : ℝ) / 2)).symm
  have hexponent : Complex.I ^ 2 * (‖k‖ : ℂ) ^ 2 / (4 * (b : ℂ)) =
      ((-r * ‖k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.I_sq, b, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
  rw [integral_congr_ae (Eventually.of_forall hpoint), integral_const_mul,
    GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace
      (by simpa only [Complex.ofReal_re] using hb) Complex.I k,
    Fintype.card_fin, hpow, Complex.ofReal_inv, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hB.ne'), one_mul,
    hexponent, ← Complex.ofReal_exp]

theorem charFun_heatWeighted_eq_heatConvolution
    (d : ℕ) (σ : Measure (Rd d)) [IsFiniteMeasure σ]
    (r : ℝ) (hr : 0 < r) (z : Rd d) :
    charFun (σ.withDensity (fun k => ENNReal.ofReal (Real.exp (-r * ‖k‖ ^ 2)))) z =
      ∫ x : Rd d, (originalHeatGaussian d r x : ℂ) * charFun σ (z - x) ∂volume := by
  have hK : Integrable (fun q : Rd d × Rd d =>
      (originalHeatGaussian d r q.1 : ℂ) *
        Complex.exp ((⟪q.2, z - q.1⟫_ℝ : ℂ) * Complex.I)) (volume.prod σ) := by
    refine ((integrable_originalHeatGaussian d r hr).comp_fst σ).mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.comp
        ((continuous_originalHeatGaussian d r).comp continuous_fst)).mul
          (show Continuous (fun q : Rd d × Rd d =>
            Complex.exp ((⟪q.2, z - q.1⟫_ℝ : ℂ) * Complex.I)) from by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall (fun q => by
        simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (originalHeatGaussian_nonneg d r hr q.1), le_refl])
  have hphase (k x : Rd d) :
      (originalHeatGaussian d r x : ℂ) *
          Complex.exp ((⟪k, z - x⟫_ℝ : ℂ) * Complex.I) =
        ((originalHeatGaussian d r x : ℂ) *
          Complex.exp ((⟪x, -k⟫_ℝ : ℂ) * Complex.I)) *
            Complex.exp ((⟪k, z⟫_ℝ : ℂ) * Complex.I) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [inner_sub_right, inner_neg_right, real_inner_comm x k,
      Complex.ofReal_sub, Complex.ofReal_neg]
    ring
  have hinner (k : Rd d) :
      (∫ x : Rd d, (originalHeatGaussian d r x : ℂ) *
        Complex.exp ((⟪k, z - x⟫_ℝ : ℂ) * Complex.I) ∂volume) =
        (Real.exp (-r * ‖k‖ ^ 2) : ℂ) * Complex.exp ((⟪k, z⟫_ℝ : ℂ) * Complex.I) := by
    rw [integral_congr_ae (Eventually.of_forall (hphase k)), integral_mul_const,
      integral_originalHeatGaussian_mul_angularExp d r hr (-k), norm_neg]
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Eventually.of_forall (fun k => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]
  exact (integral_congr_ae (Eventually.of_forall hinner)).symm.trans
    ((integral_integral_swap hK).symm.trans
      (integral_congr_ae (Eventually.of_forall (fun x => by
        simp only [charFun_apply, integral_const_mul]))))

def heatSpectralWeight (d : ℕ) (a : ℝ) (k : Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(2 * a) * ‖k‖ ^ 2))

theorem measurable_heatSpectralWeight (d : ℕ) (a : ℝ) :
    Measurable (heatSpectralWeight d a) := by
  exact (show Continuous (fun k : Rd d => Real.exp (-(2 * a) * ‖k‖ ^ 2)) from
    by fun_prop).measurable.ennreal_ofReal

theorem heatSpectralWeight_add (d : ℕ) (a b : ℝ) :
    heatSpectralWeight d (a + b) = heatSpectralWeight d a * heatSpectralWeight d b := by
  funext k
  exact (congrArg (fun q : ℝ => ENNReal.ofReal (Real.exp q))
    (show -(2 * (a + b)) * ‖k‖ ^ 2 = -(2 * a) * ‖k‖ ^ 2 + -(2 * b) * ‖k‖ ^ 2 by ring)).trans
      ((congrArg ENNReal.ofReal (Real.exp_add _ _)).trans
        (ENNReal.ofReal_mul (Real.exp_pos _).le))

theorem heatSpectralWeight_zero (d : ℕ) : heatSpectralWeight d 0 = 1 := by
  funext k
  simp only [heatSpectralWeight, mul_zero, zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
    Pi.one_apply]

theorem withDensity_heatSpectralWeight_add
    (d : ℕ) (μ : Measure (Rd d)) (a b : ℝ) :
    (μ.withDensity (heatSpectralWeight d a)).withDensity (heatSpectralWeight d b) =
      μ.withDensity (heatSpectralWeight d (a + b)) := by
  rw [← withDensity_mul μ (measurable_heatSpectralWeight d a)
    (measurable_heatSpectralWeight d b), ← heatSpectralWeight_add d a b]

theorem isFiniteMeasure_withDensity_heatSpectralWeight
    (d : ℕ) (μ : Measure (Rd d)) [IsFiniteMeasure μ] (a : ℝ) (ha : 0 ≤ a) :
    IsFiniteMeasure (μ.withDensity (heatSpectralWeight d a)) := by
  exact isFiniteMeasure_withDensity (ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
    ((lintegral_mono (fun k : Rd d => ENNReal.ofReal_le_one.mpr
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg (by norm_num) ha)) (sq_nonneg ‖k‖))))).trans_eq
          (show (∫⁻ _k : Rd d, (1 : ℝ≥0∞) ∂μ) = μ Set.univ by simp)))

theorem originalHeatSpectrum_add_eq_withDensity
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (t h : ℝ) (ht : 0 < t) (hh : 0 < h) :
    (originalHeatSpectrum d s hs P hP hW (t + h) (add_pos ht hh) : Measure (Rd d)) =
      (originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)).withDensity
        (heatSpectralWeight d h) := by
  letI : IsFiniteMeasure
      ((originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)).withDensity
        (heatSpectralWeight d h)) :=
    isFiniteMeasure_withDensity_heatSpectralWeight d _ h hh.le
  refine Measure.ext_of_charFun (funext (fun z => ?_))
  rw [charFun_originalHeatSpectrum,
    show heatSpectralWeight d h = (fun k : Rd d => ENNReal.ofReal (Real.exp (-(2 * h) * ‖k‖ ^ 2)))
      from rfl,
    charFun_heatWeighted_eq_heatConvolution d _ (2 * h) (by positivity) z]
  simp_rw [charFun_originalHeatSpectrum, ← Complex.ofReal_mul]
  exact (congrArg Complex.ofReal
    (originalHeatCovariance_eq_convolution_of_W_ne_top_pos d s hs P hP hW t h ht hh z).2).trans
      integral_complex_ofReal.symm

def originalAngularSpectrum
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) : Measure (Rd d) :=
  (originalHeatSpectrum d s hs P hP hW 1 (by norm_num) : Measure (Rd d)).withDensity
    (heatSpectralWeight d (-1))

instance instSigmaFiniteOriginalAngularSpectrum
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    SigmaFinite (originalAngularSpectrum d s hs P hP hW) := by
  exact SigmaFinite.withDensity_ofReal
    (μ := (originalHeatSpectrum d s hs P hP hW 1 (by norm_num) : Measure (Rd d)))
    (fun k : Rd d => Real.exp (-(2 * (-1 : ℝ)) * ‖k‖ ^ 2))

instance instIsLocallyFiniteMeasureOriginalAngularSpectrum
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) :
    IsLocallyFiniteMeasure (originalAngularSpectrum d s hs P hP hW) := by
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (μ := (originalHeatSpectrum d s hs P hP hW 1 (by norm_num) : Measure (Rd d)))
    (f := fun k : Rd d => Real.exp (-(2 * (-1 : ℝ)) * ‖k‖ ^ 2)) (by fun_prop)

theorem originalAngularSpectrum_withDensity_eq_heatSpectrum
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    (originalAngularSpectrum d s hs P hP hW).withDensity (heatSpectralWeight d t) =
      (originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)) := by
  have hcommon :
      (originalHeatSpectrum d s hs P hP hW t ht : Measure (Rd d)).withDensity
          (heatSpectralWeight d 1) =
        (originalHeatSpectrum d s hs P hP hW 1 (by norm_num) : Measure (Rd d)).withDensity
          (heatSpectralWeight d t) :=
    (originalHeatSpectrum_add_eq_withDensity d s hs P hP hW t 1 ht (by norm_num)).symm.trans
      (by simpa only [add_comm t 1] using
        (originalHeatSpectrum_add_eq_withDensity d s hs P hP hW 1 t (by norm_num) ht))
  simpa only [originalAngularSpectrum, withDensity_heatSpectralWeight_add,
    show t + -1 = -1 + t by ring, show (1 : ℝ) + -1 = 0 by norm_num,
    heatSpectralWeight_zero, withDensity_one] using
      congrArg (fun μ : Measure (Rd d) => μ.withDensity (heatSpectralWeight d (-1))) hcommon.symm

theorem lintegral_originalAngularSpectrum_heatSpectralWeight
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    (∫⁻ k, heatSpectralWeight d t k ∂originalAngularSpectrum d s hs P hP hW) =
      ENNReal.ofReal (originalHeatCovariance d P t 0) := by
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using
    (congrArg (fun μ : Measure (Rd d) => μ Set.univ)
      (originalAngularSpectrum_withDensity_eq_heatSpectrum d s hs P hP hW t ht)).trans
        (mass_originalHeatSpectrum d s hs P hP hW t ht)

theorem lintegral_originalAngularSpectrum_heatSpectralWeight_eq
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    (∫⁻ k, heatSpectralWeight d t k ∂originalAngularSpectrum d s hs P hP hW) =
      ENNReal.ofReal ((8 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
        ((Q d P (1 / (8 * t))).toReal + 1) - 1) := by
  exact (lintegral_originalAngularSpectrum_heatSpectralWeight d s hs P hP hW t ht).trans
    (congrArg ENNReal.ofReal (originalHeatCovariance_zero d P hP t ht
      (Q_ne_top_of_W_ne_top_pos d s hs P hW _ (by positivity))))

theorem originalAngularSpectrum_eq_of_exponent
    (d : ℕ) (s r : ℝ) (hs : 0 < s) (hr : 0 < r) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hWs : W d s P ≠ ⊤) (hWr : W d r P ≠ ⊤) :
    originalAngularSpectrum d s hs P hP hWs =
      originalAngularSpectrum d r hr P hP hWr := by
  exact congrArg (fun σ : FiniteMeasure (Rd d) =>
    (σ : Measure (Rd d)).withDensity (heatSpectralWeight d (-1)))
      (originalHeatSpectrum_eq_of_exponent d s r hs hr P hP hWs hWr 1 (by norm_num))

end Riesz.Stationary
