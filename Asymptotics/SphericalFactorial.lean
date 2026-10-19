import Riesz.Configuration.ExpectedFactorial
import Riesz.Asymptotics.SphericalPerturbation
import Riesz.Asymptotics.SphericalPairMoments
import Riesz.Geometry.GaussianChord

/-! Original-label factorial tests and anchored Gaussian comparisons for the
actual Haar-rotated spherical laws. Coincident unequal labels are retained.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Asymptotics

/-- Remove equal original labels, retaining coincident unequal labels. -/
theorem countingFactorialIntegral_sphereLocalConfiguration_eq_sum
    (d N : ℕ) (R : ℝ) (x : Fin N → Sphere d)
    (U : Problem1.Orthogonal d) (f : C_c(Rd d × Rd d, ℝ)) :
    countingFactorialIntegral d (sphereLocalConfiguration d N R x U) f =
      ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else
        if rotateSphere d U (x i) ∈ northHemisphere d ∧
            rotateSphere d U (x j) ∈ northHemisphere d then
          f (normalInverse d R (rotateSphere d U (x i)).val,
             normalInverse d R (rotateSphere d U (x j)).val)
        else 0 := by
  letI : IsFiniteMeasure (sphereLocalCounting d N R x U) := by
    rw [sphereLocalCounting_eq_tupleCounting]
    exact Riesz.Negative.tupleCounting_isFiniteMeasure d _ _
  have hp :
      (∫ p, f p ∂(sphereLocalCounting d N R x U).prod
        (sphereLocalCounting d N R x U)) =
        ∑ i : Fin N, ∑ j : Fin N,
          if rotateSphere d U (x i) ∈ northHemisphere d ∧
              rotateSphere d U (x j) ∈ northHemisphere d then
            f (normalInverse d R (rotateSphere d U (x i)).val,
               normalInverse d R (rotateSphere d U (x j)).val)
          else 0 := by
    rw [integral_prod _ f.integrable, integral_sphereLocalCounting_eq_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : rotateSphere d U (x i) ∈ northHemisphere d
    · simp only [hemisphereChartTest, if_pos hi]
      rw [integral_sphereLocalCounting_eq_sum]
      simp [hemisphereChartTest, hi]
    · simp [hemisphereChartTest, hi]
  have hd :
      (∫ z, f (z, z) ∂sphereLocalCounting d N R x U) =
        ∑ i : Fin N, if rotateSphere d U (x i) ∈ northHemisphere d then
          f (normalInverse d R (rotateSphere d U (x i)).val,
             normalInverse d R (rotateSphere d U (x i)).val)
        else 0 := by
    simpa only [hemisphereChartTest] using
      (integral_sphereLocalCounting_eq_sum d N R x U (fun z => f (z, z)))
  change
    (∫ p, f p ∂(sphereLocalCounting d N R x U).prod
      (sphereLocalCounting d N R x U)) -
      (∫ z, f (z, z) ∂sphereLocalCounting d N R x U) = _
  rw [hp, hd, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hdiag :
      (∑ j : Fin N, if i = j then
        (if rotateSphere d U (x i) ∈ northHemisphere d ∧
            rotateSphere d U (x j) ∈ northHemisphere d then
          f (normalInverse d R (rotateSphere d U (x i)).val,
             normalInverse d R (rotateSphere d U (x j)).val)
        else 0)
      else 0) =
        if rotateSphere d U (x i) ∈ northHemisphere d then
          f (normalInverse d R (rotateSphere d U (x i)).val,
             normalInverse d R (rotateSphere d U (x i)).val)
        else 0 := by
    simp
  rw [← hdiag, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp

/-- A compact pair cutoff multiplied by the Euclidean Gaussian. -/
def compactGaussianFactorialTest (d : ℕ)
    (χ : C_c(Rd d × Rd d, ℝ)) (u : ℝ) : C_c(Rd d × Rd d, ℝ) := by
  refine ⟨⟨fun p => χ p * Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ)), ?_⟩, ?_⟩
  · exact χ.continuous.mul
      ((((continuous_snd.sub continuous_fst).norm.pow 2).const_mul (-u)).rexp)
  · exact χ.hasCompactSupport.mul_right

theorem compactGaussianFactorialTest_nonneg (d : ℕ)
    (χ : C_c(Rd d × Rd d, ℝ)) (hχ : ∀ p, 0 ≤ χ p) (u : ℝ) :
    ∀ p, 0 ≤ compactGaussianFactorialTest d χ u p := by
  exact fun p => mul_nonneg (hχ p) (Real.exp_nonneg _)

/-- A finite coefficient suffices for the later positive-tail finiteness bound. -/
theorem eventually_compactGaussianFactorial_le_capAnchored
    (d : ℕ) (χ : C_c(Rd d × Rd d, ℝ)) (u T : ℝ)
    (hsupport : tsupport χ ⊆ Metric.closedBall (0 : Rd d) T ×ˢ
      Metric.closedBall (0 : Rd d) T) :
    ∀ᶠ R : ℝ in atTop, ∀ (N : ℕ) (x : Fin N → Sphere d)
        (U : Problem1.Orthogonal d),
      ENNReal.ofReal (countingFactorialIntegral d
        (sphereLocalConfiguration d N R x U) (compactGaussianFactorialTest d χ u)) ≤
        ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) *
          sphereAnchoredGaussianPairSum d N R u T x U := by
  filter_upwards [eventually_normalGaussian_le_sphericalGaussian d u T 1 zero_lt_one,
    eventually_gt_atTop (0 : ℝ)] with R hgaussian hR N x U
  let y : Fin N → Sphere d := fun i => rotateSphere d U (x i)
  let z : Fin N → Rd d := fun i => normalInverse d R (y i).val
  let F : Fin N → Fin N → ℝ := fun i j =>
    if i = j then 0 else
      if y i ∈ northHemisphere d ∧ y j ∈ northHemisphere d then
        compactGaussianFactorialTest d χ u (z i, z j)
      else 0
  let G : Fin N → Fin N → ℝ := fun i j =>
    if i = j then 0 else
      if y i ∈ sphereNormalBall d R T then
        Real.exp (-(u * R ^ 2) * chord d (y i) (y j) ^ 2)
      else 0
  have hGnonneg (i j : Fin N) : 0 ≤ G i j := by
    positivity
  have hfactor : 0 ≤ 2 * ‖χ.toBoundedContinuousFunction‖ := by positivity
  have hχbound (p : Rd d × Rd d) : χ p ≤ ‖χ.toBoundedContinuousFunction‖ :=
    (Real.le_norm_self (χ p)).trans (χ.toBoundedContinuousFunction.norm_coe_le_norm p)
  have hterm (i j : Fin N) : F i j ≤ (2 * ‖χ.toBoundedContinuousFunction‖) * G i j := by
    by_cases hij : i = j
    · simp [F, G, hij]
    · by_cases hnorth : y i ∈ northHemisphere d ∧ y j ∈ northHemisphere d
      · by_cases hs : (z i, z j) ∈ tsupport χ
        · have hb := hsupport hs
          have hiBall : y i ∈ sphereNormalBall d R T := ⟨hnorth.1, hb.1⟩
          have hnormal : normalPoint d R (z i) = y i ∧ normalPoint d R (z j) = y j :=
            ⟨normalPoint_normalInverse d hR hnorth.1,
              normalPoint_normalInverse d hR hnorth.2⟩
          have he : Real.exp (-u * ‖z j - z i‖ ^ (2 : ℕ)) ≤
              2 * Real.exp (-(u * R ^ 2) * chord d (y i) (y j) ^ 2) := by
            simpa only [hnormal.1, hnormal.2, norm_sub_rev, one_add_one_eq_two] using
              hgaussian (z i) hb.1 (z j) hb.2
          have hweight : χ (z i, z j) * Real.exp (-u * ‖z j - z i‖ ^ (2 : ℕ)) ≤
              (2 * ‖χ.toBoundedContinuousFunction‖) *
                Real.exp (-(u * R ^ 2) * chord d (y i) (y j) ^ 2) := by
            nlinarith only [mul_le_mul_of_nonneg_right (hχbound (z i, z j))
              (Real.exp_nonneg (-u * ‖z j - z i‖ ^ (2 : ℕ))),
              mul_le_mul_of_nonneg_left he (norm_nonneg χ.toBoundedContinuousFunction)]
          simpa [F, G, hij, hnorth, hiBall,
            compactGaussianFactorialTest] using hweight
        · simpa [F, hij, hnorth, compactGaussianFactorialTest,
            image_eq_zero_of_notMem_tsupport hs] using mul_nonneg hfactor (hGnonneg i j)
      · simpa [F, hij, hnorth] using mul_nonneg hfactor (hGnonneg i j)
  have hsum : (∑ i : Fin N, ∑ j : Fin N, F i j) ≤
      (2 * ‖χ.toBoundedContinuousFunction‖) * (∑ i : Fin N, ∑ j : Fin N, G i j) := by
    simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm i j))
  have hFsum : countingFactorialIntegral d (sphereLocalConfiguration d N R x U)
      (compactGaussianFactorialTest d χ u) = ∑ i : Fin N, ∑ j : Fin N, F i j := by
    simpa only [F, y, z] using
      countingFactorialIntegral_sphereLocalConfiguration_eq_sum d N R x U
        (compactGaussianFactorialTest d χ u)
  have hGsum : ENNReal.ofReal (∑ i : Fin N, ∑ j : Fin N, G i j) =
      sphereAnchoredGaussianPairSum d N R u T x U := by
    unfold sphereAnchoredGaussianPairSum
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => hGnonneg i j))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hGnonneg i j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> simp_all only [G, y, if_true, if_false, ENNReal.ofReal_zero]
  simpa only [hFsum, ENNReal.ofReal_mul hfactor, hGsum] using
    ENNReal.ofReal_le_ofReal hsum

/-- Haar averaging turns the compact-test bound into a uniform profile bound. -/
theorem eventually_compactGaussianFactorial_mean_le_capConstant
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d) (χ : C_c(Rd d × Rd d, ℝ)) (u T : ℝ)
    (hT : 0 < T)
    (hsupport : tsupport χ ⊆ Metric.closedBall (0 : Rd d) T ×ˢ
      Metric.closedBall (0 : Rd d) T) :
    ∀ᶠ n : ℕ in atTop,
      (∫⁻ μ, ENNReal.ofReal (countingFactorialIntegral d μ
          (compactGaussianFactorialTest d χ u))
        ∂(sphereLocalCountingProbability d (N n) (sphericalRadius d (N n))
          (x n)).toMeasure) ≤
        (ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) *
          ENNReal.ofReal (omega d * Problem1.capConstant d * T ^ d)) *
            ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n) u) := by
  have hR : Tendsto (fun n => sphericalRadius d (N n)) atTop atTop :=
    (sphericalRadius_tendsto_atTop d (by omega)).comp hN
  have hRpi : Tendsto (fun n => Real.pi * sphericalRadius d (N n) / 2) atTop atTop :=
    (Tendsto.const_mul_atTop Real.pi_pos hR).atTop_div_const (by norm_num)
  filter_upwards [hR.eventually
      (eventually_compactGaussianFactorial_le_capAnchored d χ u T hsupport),
    hN.eventually_gt_atTop 0, hRpi.eventually_gt_atTop T] with n hpath hn hcap
  change (∫⁻ μ, ENNReal.ofReal (countingFactorialIntegral d μ
      (compactGaussianFactorialTest d χ u))
    ∂(uniformRotationLaw d).map
      (sphereLocalConfiguration d (N n) (sphericalRadius d (N n)) (x n))) ≤ _
  rw [lintegral_map
    ((continuous_countingFactorialIntegral d
      (compactGaussianFactorialTest d χ u)).measurable.ennreal_ofReal)
    (measurable_sphereLocalConfiguration_fixed d (N n) (sphericalRadius d (N n)) (x n))]
  have hmean := lintegral_mono (μ := uniformRotationLaw d) (hpath (N n) (x n))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    sphereAnchoredGaussianPairSum_mean d (N n) hn u T (x n)] at hmean
  have hcapMean : (N n : ℝ≥0∞) * sphericalMeasure d
      (sphereNormalBall d (sphericalRadius d (N n)) T) ≤
        ENNReal.ofReal (omega d * Problem1.capConstant d * T ^ d) := by
    simpa only [sphereNormalBall] using
      sphericalMeasure_normalBall_mul_le d (N n) hd hn T hT hcap
  simpa only [mul_assoc] using hmean.trans
    (mul_le_mul_right (mul_le_mul_left hcapMean
      (ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n) u)))
      (ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖)))

theorem measurable_sphericalGaussianPairProfile (d N : ℕ)
    (x : Fin N → Sphere d) : Measurable (sphericalGaussianPairProfile d N x) := by
  unfold sphericalGaussianPairProfile
  refine measurable_const.mul (Finset.measurable_fun_sum _ (fun i _ =>
    Finset.measurable_fun_sum _ (fun j _ => ?_)))
  split_ifs <;> fun_prop

/-- Beyond π the subtracted positive-part background vanishes. -/
theorem sphericalGaussianPairProfile_eq_remainder_of_pi_le
    (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (x : Fin N → Sphere d) (u : ℝ) (hu : Real.pi ≤ u) :
    sphericalGaussianPairProfile d N x u =
      sphericalGaussianRemainder d N x u := by
  have hbg : sphericalGaussianBackground d N u ≤ 1 :=
    (sphericalGaussianBackground_le d N hd hN u (Real.pi_pos.trans_le hu)).trans
      (Riesz.Stationary.B_le_one_of_pi_le d u hu)
  simp only [sphericalGaussianRemainder,
    max_eq_right (sub_nonpos.mpr hbg), sub_zero]

/-- Eventually bounded positive scaled energy controls the whole profile tail. -/
theorem eventually_sphericalGaussianPairProfile_tail_lintegral_bounded
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (henergy : ∃ L : ℝ, ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N n) s (x n) ≤ L) :
    ∃ D : ℝ≥0∞, D ≠ ∞ ∧ ∀ᶠ n : ℕ in atTop,
      (∫⁻ u in Set.Ioi Real.pi,
        ENNReal.ofReal (u ^ (s / 2 - 1)) *
          ENNReal.ofReal
            (sphericalGaussianPairProfile d (N n) (x n).val u)) ≤ D := by
  obtain ⟨L, hL⟩ := henergy
  have hgamma : 0 < gamma_s s :=
    Riesz.Analysis.gamma_s_pos s ((by norm_num : (-2 : ℝ) < 0).trans hs)
  have href := ((tendsto_sphericalReferenceConstant d hd s hsd hs.ne').comp hN).eventually
    (lt_mem_nhds (show c0 d s - 1 < c0 d s by linarith))
  refine ⟨ENNReal.ofReal ((L - c0 d s + 1) / gamma_s s), ENNReal.ofReal_ne_top, ?_⟩
  filter_upwards [hL, href, hN.eventually (eventually_gt_atTop (0 : ℕ))]
    with n henergy href hnpos
  change c0 d s - 1 < sphericalReferenceConstant d (N n) s at href
  have hidentity := positive_spherical_remainder_identity
    d (N n) hd hnpos s hs hsd (x n)
  have hscaled :
      scaledSphericalKernelEnergy d (N n) s (x n) =
        sphericalReferenceConstant d (N n) s + gamma_s s *
          ∫ u in Set.Ioi (0 : ℝ),
            u ^ (s / 2 - 1) *
              sphericalGaussianRemainder d (N n) (x n).val u := by
    simpa only [scaledSphericalKernelEnergy] using hidentity.2
  have hbound :
      (∫ u in Set.Ioi (0 : ℝ),
        u ^ (s / 2 - 1) * sphericalGaussianRemainder d (N n) (x n).val u) ≤
        (L - c0 d s + 1) / gamma_s s := by
    apply (le_div_iff₀ hgamma).2
    nlinarith [hscaled]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun u => u ^ (s / 2 - 1) * sphericalGaussianRemainder d (N n) (x n).val u) :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu =>
      mul_nonneg (Real.rpow_nonneg hu.le _)
        (sphericalGaussianRemainder_nonneg d (N n) hd hnpos (x n).val u hu.le))
  have hlintegral :
      (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) *
        ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)) =
      ENNReal.ofReal (∫ u in Set.Ioi (0 : ℝ),
        u ^ (s / 2 - 1) * sphericalGaussianRemainder d (N n) (x n).val u) := by
    rw [ofReal_integral_eq_lintegral_ofReal hidentity.1 hnonneg]
    exact lintegral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun u hu => (ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _)).symm))
  calc
    (∫⁻ u in Set.Ioi Real.pi, ENNReal.ofReal (u ^ (s / 2 - 1)) *
      ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u)) =
        ∫⁻ u in Set.Ioi Real.pi, ENNReal.ofReal (u ^ (s / 2 - 1)) *
          ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u) :=
      setLIntegral_congr_fun measurableSet_Ioi (fun u hu =>
        congrArg (fun a : ℝ => ENNReal.ofReal (u ^ (s / 2 - 1)) * ENNReal.ofReal a)
          (sphericalGaussianPairProfile_eq_remainder_of_pi_le
            d (N n) hd hnpos (x n).val u hu.le))
    _ ≤ ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) *
          ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u) :=
      lintegral_mono' (Measure.restrict_mono_set volume
        (fun _ hu => Real.pi_pos.trans hu)) le_rfl
    _ = ENNReal.ofReal (∫ u in Set.Ioi (0 : ℝ),
          u ^ (s / 2 - 1) * sphericalGaussianRemainder d (N n) (x n).val u) := hlintegral
    _ ≤ ENNReal.ofReal ((L - c0 d s + 1) / gamma_s s) := ENNReal.ofReal_le_ofReal hbound

/-- Fatou uses pointwise eventual profile bounds; their thresholds may depend on
the Gaussian parameter. Only the limiting law needs local second moments. -/
theorem localizedGaussianTail_le_of_eventual_profile_bound
    (d : ℕ)
    (P : ℕ → ProbabilityMeasure (CountingConfiguration d))
    (Q : ProbabilityMeasure (CountingConfiguration d)) (hQ : Tendsto P atTop (𝓝 Q))
    (hsecondQ : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂Q.toMeasure) < ∞)
    (χ : C_c(Rd d × Rd d, ℝ)) (hχ : ∀ p, 0 ≤ χ p)
    (s c : ℝ) (g : ℕ → ℝ → ℝ≥0∞) (hg : ∀ n, Measurable (g n))
    (C D : ℝ≥0∞) (hC : C ≠ ∞)
    (hcomparison : ∀ u ∈ Set.Ioi c, ∀ᶠ n : ℕ in atTop,
      (∫⁻ μ, ENNReal.ofReal
        (countingFactorialIntegral d μ (compactGaussianFactorialTest d χ u))
        ∂(P n).toMeasure) ≤ C * g n u)
    (htail : ∀ᶠ n : ℕ in atTop,
      (∫⁻ u in Set.Ioi c, ENNReal.ofReal (u ^ (s / 2 - 1)) * g n u) ≤ D) :
    (∫⁻ u in Set.Ioi c, ENNReal.ofReal (u ^ (s / 2 - 1)) *
      ∫⁻ p, ENNReal.ofReal (χ p) *
        ENNReal.ofReal (Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ)))
        ∂expectedFactorialMeasure d Q.toMeasure hsecondQ) ≤ C * D := by
  let w : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (u ^ (s / 2 - 1))
  have hw : Measurable w := (measurable_id.pow_const (s / 2 - 1)).ennreal_ofReal
  have htestintegral (u : ℝ) :
      (∫⁻ p, ENNReal.ofReal (χ p) *
        ENNReal.ofReal (Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ)))
        ∂expectedFactorialMeasure d Q.toMeasure hsecondQ) =
      ∫⁻ p, ENNReal.ofReal (compactGaussianFactorialTest d χ u p)
        ∂expectedFactorialMeasure d Q.toMeasure hsecondQ := by
    exact lintegral_congr (fun p => (ENNReal.ofReal_mul (hχ p)).symm)
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioi c) :
      w u * (∫⁻ p, ENNReal.ofReal (χ p) *
        ENNReal.ofReal (Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ)))
        ∂expectedFactorialMeasure d Q.toMeasure hsecondQ) ≤
      atTop.liminf (fun n : ℕ => w u * (C * g n u)) := by
    have hprofile := (htestintegral u).trans_le
      ((lintegral_expectedFactorialMeasure_le_liminf d P Q hQ hsecondQ
        (compactGaussianFactorialTest d χ u) (compactGaussianFactorialTest_nonneg d χ hχ u)).trans
          (Filter.liminf_le_liminf (hcomparison u hu)))
    have hmul :
        w u * atTop.liminf (fun n : ℕ => C * g n u) ≤
        atTop.liminf (fun n : ℕ => w u * (C * g n u)) := by
      simpa only [Pi.mul_def, Filter.liminf_const] using
        (ENNReal.le_liminf_mul
          (u := fun _n : ℕ => w u) (v := fun n : ℕ => C * g n u) (f := atTop))
    exact (mul_le_mul_right hprofile (w u)).trans hmul
  have hmeas (n : ℕ) : Measurable (fun u => w u * (C * g n u)) :=
    hw.mul (measurable_const.mul (hg n))
  have hevent : ∀ᶠ n : ℕ in atTop,
      (∫⁻ u in Set.Ioi c, w u * (C * g n u)) ≤ C * D :=
    htail.mono (fun n hn =>
      (lintegral_congr (fun u => mul_left_comm (w u) C (g n u))).trans_le
        ((lintegral_const_mul' C _ hC).trans_le (mul_le_mul_right hn C)))
  exact (setLIntegral_mono' measurableSet_Ioi hpoint).trans
    ((lintegral_liminf_le hmeas).trans
      (Filter.liminf_le_of_frequently_le' hevent.frequently))

/-- Positive energy bounds exclude collisions in an actual spherical weak limit.
The moment hypothesis is derived from the energy bound. -/
theorem sphereLocalCountingProbability_limit_ae_simple_of_positive_energy_bound
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (henergy : ∃ L : ℝ, ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N n) s (x n) ≤ L)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto
      (fun n => sphereLocalCountingProbability d (N n)
        (sphericalRadius d (N n)) (x n).val) atTop (𝓝 Q)) :
    (∀ᵐ μ ∂Q.toMeasure, IsSimpleConfiguration d μ.val) ∧
      (∀ᵐ μ ∂Q.toMeasure.map
        (fun ν : CountingConfiguration d => ν.val), IsSimpleConfiguration d μ) := by
  let P : ℕ → ProbabilityMeasure (CountingConfiguration d) := fun n =>
    sphereLocalCountingProbability d (N n) (sphericalRadius d (N n)) (x n).val
  have hsfull : -2 < s := by linarith
  have hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ n : ℕ, (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(P n).toMeasure) ≤ C :=
    fun T hT => exists_sphereLocalCountingProbability_ball_second_moment_bound_of_energy_bound
      d hd s hsfull hsd hs.ne' N hN x henergy T hT
  have hsecondQ : ∀ m : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (m : ℝ))) ^ 2 ∂Q.toMeasure) < ∞ :=
    fun m => countingLaw_limit_local_second_moments d P Q hQ hball
      (Metric.closedBall (0 : Rd d) (m : ℝ)) measurableSet_closedBall
      (isCompact_closedBall (0 : Rd d) (m : ℝ)).isBounded
  obtain ⟨D, hD, htail⟩ :=
    eventually_sphericalGaussianPairProfile_tail_lintegral_bounded
      d hd s hs hsd N hN x henergy
  let g : ℕ → ℝ → ℝ≥0∞ := fun n u =>
    ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u)
  have hg : ∀ n : ℕ, Measurable (g n) := fun n =>
    (measurable_sphericalGaussianPairProfile d (N n) (x n).val).ennreal_ofReal
  have hfinite : ∀ χ : C_c(Rd d × Rd d, ℝ), (∀ p, 0 ≤ χ p) →
      (∫⁻ u in Set.Ioi Real.pi, ENNReal.ofReal (u ^ (s / 2 - 1)) *
        ∫⁻ p, ENNReal.ofReal (χ p) *
          ENNReal.ofReal (Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ)))
          ∂expectedFactorialMeasure d Q.toMeasure hsecondQ) < ∞ := by
    intro χ hχ
    obtain ⟨R, hR⟩ := ((χ.hasCompactSupport.image continuous_fst).union
      (χ.hasCompactSupport.image continuous_snd)).isBounded.exists_norm_le
    let T : ℝ := max 1 R
    have hT : 0 < T := zero_lt_one.trans_le (le_max_left 1 R)
    have hsupport : tsupport χ ⊆ Metric.closedBall (0 : Rd d) T ×ˢ
        Metric.closedBall (0 : Rd d) T := fun p hp =>
      ⟨Metric.mem_closedBall.mpr ((dist_zero_right p.1).trans_le
          ((hR p.1 (Or.inl ⟨p, hp, rfl⟩)).trans (le_max_right 1 R))),
        Metric.mem_closedBall.mpr ((dist_zero_right p.2).trans_le
          ((hR p.2 (Or.inr ⟨p, hp, rfl⟩)).trans (le_max_right 1 R)))⟩
    let C : ℝ≥0∞ := ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) *
      ENNReal.ofReal (omega d * Problem1.capConstant d * T ^ d)
    have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hcomparison : ∀ u ∈ Set.Ioi Real.pi, ∀ᶠ n : ℕ in atTop,
        (∫⁻ μ, ENNReal.ofReal
          (countingFactorialIntegral d μ (compactGaussianFactorialTest d χ u))
          ∂(P n).toMeasure) ≤ C * g n u :=
      fun u _ => eventually_compactGaussianFactorial_mean_le_capConstant
        d hd N hN (fun n => (x n).val) χ u T hT hsupport
    exact (localizedGaussianTail_le_of_eventual_profile_bound
      d P Q hQ hsecondQ χ hχ s Real.pi g hg C D hC hcomparison htail).trans_lt
        (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hC hD))
  have hdiag := expectedFactorialMeasure_diagonal_zero_of_pos_gaussian_tail_finite
    d Q.toMeasure hsecondQ s Real.pi hs Real.pi_pos hfinite
  exact ⟨ae_isSimpleConfiguration_of_expectedFactorialMeasure_diagonal_zero
      d Q.toMeasure hsecondQ hdiag,
    ae_isSimpleConfiguration_map_val_of_expectedFactorialMeasure_diagonal_zero
      d Q.toMeasure hsecondQ hdiag⟩

end Riesz.Asymptotics
