import Riesz.Stationary.WindowOverlap
import Riesz.Stationary.GaussianCorrection
import Riesz.Stationary.Infimum

/-!
# Multiplicity-preserving translation and negative Gaussian profiles

Factorial translation retains unequal labels at coincident sites. The energy
adapters use the exact original `W` and do not assume a covariance bound.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Configuration

/-- Translation of the factorial functional retains multiplicities. -/
theorem countingFactorialIntegral_translate_allCounting
    (d : ℕ) (a : Rd d) (μ : CountingConfiguration d)
    (f : C_c(Rd d × Rd d, ℝ)) :
    countingFactorialIntegral d (translateCounting d a μ) f =
      countingFactorialIntegral d μ
        (f.comp (Homeomorph.addLeft (a, a)).toCocompactMap) := by
  let t : Rd d → Rd d := fun x => a + x
  have ht : Measurable t := measurable_const.add measurable_id
  change (∫ p, f p ∂(μ.val.map t).prod (μ.val.map t)) -
    (∫ x, f (x, x) ∂μ.val.map t) = _
  rw [Measure.map_prod_map μ.val μ.val ht ht,
    integral_map_of_stronglyMeasurable (f := fun p => f p)
      (ht.prodMap ht) f.continuous.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (f := fun x => f (x, x)) ht
      (f.continuous.comp (continuous_id.prodMk continuous_id)).stronglyMeasurable]
  rfl

/-- The factorial pair measure of any stationary counting law is translation invariant. -/
theorem expectedFactorialMeasure_stationary_allCounting
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hstationary : IsStationary d (P.map Subtype.val)) (a : Rd d) :
    (expectedFactorialMeasure d P hsecond).map
      (fun p : Rd d × Rd d => (a + p.1, a + p.2)) =
        expectedFactorialMeasure d P hsecond := by
  let Γ := expectedFactorialMeasure d P hsecond
  let e : (Rd d × Rd d) ≃ₜ (Rd d × Rd d) := Homeomorph.addLeft (a, a)
  letI : (Γ.map e).Regular := Measure.Regular.map e
  change Γ.map e = Γ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fT : C_c(Rd d × Rd d, ℝ) := f.comp e.toCocompactMap
  calc
    (∫ p, f p ∂Γ.map e) = ∫ p, fT p ∂Γ :=
      integral_map_of_stronglyMeasurable (f := fun p => f p)
        e.continuous.measurable f.continuous.stronglyMeasurable
    _ = ∫ μ, countingFactorialIntegral d μ fT ∂P :=
      integral_expectedFactorialMeasure d P hsecond fT
    _ = ∫ μ, countingFactorialIntegral d (translateCounting d a μ) f ∂P :=
      integral_congr_ae (Eventually.of_forall (fun μ =>
        (countingFactorialIntegral_translate_allCounting d a μ f).symm))
    _ = ∫ μ, countingFactorialIntegral d μ f ∂P.map (translateCounting d a) :=
      (integral_map_of_stronglyMeasurable (measurable_translateCounting d a)
        (continuous_countingFactorialIntegral d f).stronglyMeasurable).symm
    _ = ∫ μ, countingFactorialIntegral d μ f ∂P :=
      congrArg (fun M => ∫ μ, countingFactorialIntegral d μ f ∂M)
        (map_translateCounting_eq_of_isStationary d P hstationary a)
    _ = ∫ p, f p ∂Γ := (integral_expectedFactorialMeasure d P hsecond f).symm

end Riesz.Configuration

namespace Riesz.Stationary

/-- Finite original energy makes the weighted remainder finite for the full lower range. -/
theorem weighted_gaussianRemainder_lintegral_ne_top_of_W_ne_top_of_neg_two_lt
    (d : ℕ) (s : ℝ) (hs_lower : -2 < s) (P : ConfigurationLaw d)
    (hW : W d s P ≠ ⊤) :
    (∫⁻ u in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (u ^ (s / 2 - 1)) * gaussianRemainder d P u) ≠ ∞ := by
  intro hI
  have hγ : ENNReal.ofReal (gamma_s s) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Riesz.Analysis.gamma_s_pos s hs_lower)
  apply hW
  unfold W
  rw [hI, ENNReal.mul_top hγ, EReal.coe_ennreal_top]
  exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)

/-- Every positive heat profile is finite under finite original energy. -/
theorem Q_ne_top_of_W_ne_top_of_neg_two_lt
    (d : ℕ) (s : ℝ) (hs_lower : -2 < s) (P : ConfigurationLaw d)
    (hW : W d s P ≠ ⊤) (u : ℝ) (hu : 0 < u) : Q d P u ≠ ∞ := by
  intro hQu
  have hI := weighted_gaussianRemainder_lintegral_ne_top_of_W_ne_top_of_neg_two_lt
    d s hs_lower P hW
  have hpoint (v : ℝ) (hv : v ∈ Set.Ioo (u / 2) u) :
      ENNReal.ofReal (v ^ (s / 2 - 1)) * gaussianRemainder d P v = ∞ := by
    have hvpos : 0 < v := lt_trans (half_pos hu) hv.1
    have hQv : Q d P v = ∞ := top_unique (hQu ▸ (antitone_Q d P hv.2.le))
    have hw : ENNReal.ofReal (v ^ (s / 2 - 1)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hvpos _)
    rw [gaussianRemainder, hQv, ENNReal.top_sub ENNReal.ofReal_ne_top,
      ENNReal.mul_top hw]
  have hinterval : (volume : Measure ℝ) (Set.Ioo (u / 2) u) ≠ 0 :=
    Real.volume_Ioo.trans_ne (ENNReal.ofReal_ne_zero_iff.mpr
      (sub_pos.mpr (half_lt_self hu)))
  have hle : (∞ : ℝ≥0∞) ≤
      ∫⁻ v in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (v ^ (s / 2 - 1)) * gaussianRemainder d P v := by
    calc
      (∞ : ℝ≥0∞) = ∫⁻ _v in Set.Ioo (u / 2) u, (∞ : ℝ≥0∞) :=
        ((setLIntegral_const (Set.Ioo (u / 2) u) ∞).trans
          (ENNReal.top_mul hinterval)).symm
      _ = ∫⁻ v in Set.Ioo (u / 2) u,
          ENNReal.ofReal (v ^ (s / 2 - 1)) * gaussianRemainder d P v :=
        setLIntegral_congr_fun measurableSet_Ioo (fun v hv => (hpoint v hv).symm)
      _ ≤ _ := lintegral_mono_set (fun v hv => lt_trans (half_pos hu) hv.1)
  exact hI (top_unique hle)

private theorem gaussianRemainder_add_correction_truncated
    (d : ℕ) (P : ConfigurationLaw d) (u : ℝ) (hQ : Q d P u ≠ ∞) :
    ENNReal.ofReal (gaussianCorrection d u) + gaussianRemainder d P u =
      ENNReal.ofReal (max ((Q d P u).toReal + 1 - B d u) 0) := by
  have hrem : gaussianRemainder d P u =
      ENNReal.ofReal ((Q d P u).toReal - max (B d u - 1) 0) := by
    unfold gaussianRemainder
    conv_lhs => rw [← ENNReal.ofReal_toReal hQ]
    exact (ENNReal.ofReal_sub _ (le_max_right (B d u - 1) 0)).symm
  have hmax : ENNReal.ofReal ((Q d P u).toReal - max (B d u - 1) 0) =
      ENNReal.ofReal (max ((Q d P u).toReal - max (B d u - 1) 0) 0) := by simp
  rw [hrem, hmax, gaussianCorrection, ← ENNReal.ofReal_add (le_max_right (1 - B d u) 0)
    (le_max_right ((Q d P u).toReal - max (B d u - 1) 0) 0)]
  congr 1
  have hq : 0 ≤ (Q d P u).toReal := ENNReal.toReal_nonneg
  grind

/-- The original negative energy is exactly its nonnegative truncated Gaussian profile. -/
theorem W_eq_weighted_truncated_profile_neg
    (d : ℕ) (s : ℝ) (hd : 2 ≤ d) (hs_lower : -2 < s) (hs_neg : s < 0)
    (P : ConfigurationLaw d) (hW : W d s P ≠ ⊤) :
    W d s P =
      ((ENNReal.ofReal (gamma_s s) *
        ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) *
          ENNReal.ofReal (max ((Q d P u).toReal + 1 - B d u) 0)) : ℝ≥0∞) := by
  have hIntegral :
      (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) *
        ENNReal.ofReal (gaussianCorrection d u)) +
      (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) *
        gaussianRemainder d P u) =
      ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) *
        ENNReal.ofReal (max ((Q d P u).toReal + 1 - B d u) 0) := by
    have hmeas : Measurable (fun u : ℝ => ENNReal.ofReal (u ^ (s / 2 - 1)) *
        ENNReal.ofReal (gaussianCorrection d u)) :=
      (measurable_id.pow_const _).ennreal_ofReal.mul
        (gaussianCorrection_measurable d).ennreal_ofReal
    rw [← lintegral_add_left hmeas]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [← mul_add, gaussianRemainder_add_correction_truncated d P u
      (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs_lower P hW u hu)]
  have hc0 : 0 ≤ c0 d s :=
    (c0_pos_of_neg d s hd hs_lower (hs_neg.trans_le (Nat.cast_nonneg d)) hs_neg).le
  have hc0coe : (c0 d s : EReal) = (ENNReal.ofReal (c0 d s) : EReal) := by
    simp only [EReal.coe_ennreal_ofReal, max_eq_left hc0]
  unfold W
  rw [hc0coe, ← gamma_correction_lintegral_eq_c0 d s hs_lower hs_neg,
    ← EReal.coe_ennreal_add, ← mul_add, hIntegral]

end Riesz.Stationary
