import Riesz.Asymptotics.SphericalLocalLaw
import Riesz.Asymptotics.SphericalLocalBounds
import Riesz.Asymptotics.SphericalProfileBound

/-!
# Second moments of the actual spherical local laws

The Gaussian weights use spherical chord distances at the enlarged-sphere
scale. Anchors lie in the normal-coordinate ball, while the second label in
the anchored Gaussian sum ranges over the whole original spherical tuple.
All unequal labels are retained, including when input sites coincide.

The estimates give uniform ball second moments from bounded actual scaled
spherical energies, including the finite prefix of a sequence.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal Topology Classical

namespace Riesz.Asymptotics

/-- The spherical preimage of the normal-coordinate ball. -/
def sphereNormalBall (d : ℕ) (R T : ℝ) : Set (Sphere d) :=
  {y | y ∈ northHemisphere d ∧
    normalInverse d R y.val ∈ Metric.closedBall (0 : Rd d) T}

/-- Ordered unequal original labels whose rotated sites both lie in the ball. -/
def sphereLocalBallPairCount (d N : ℕ) (R T : ℝ) (x : Fin N → Sphere d)
    (U : Problem1.Orthogonal d) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ j : Fin N,
    if i = j then 0 else
      if rotateSphere d U (x i) ∈ sphereNormalBall d R T ∧
        rotateSphere d U (x j) ∈ sphereNormalBall d R T then 1 else 0

/-- The first label is in the normal ball; every unequal second label is kept. -/
def sphereAnchoredGaussianPairSum (d N : ℕ) (R a T : ℝ)
    (x : Fin N → Sphere d) (U : Problem1.Orthogonal d) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ j : Fin N,
    if i = j then 0 else
      if rotateSphere d U (x i) ∈ sphereNormalBall d R T then
        ENNReal.ofReal (Real.exp (-(a * R ^ 2) *
          (chord d (rotateSphere d U (x i)) (rotateSphere d U (x j))) ^ 2))
      else 0

/-- A normal ball has enlarged-sphere chord diameter at most `2T`. -/
theorem sphereNormalBall_scaled_chord_le (d : ℕ) {R T : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hTpi : T < Real.pi * R / 2)
    {y z : Sphere d} (hy : y ∈ sphereNormalBall d R T)
    (hz : z ∈ sphereNormalBall d R T) :
    R * chord d y z ≤ 2 * T := by
  have hcap : sphereNormalBall d R T =
      {v : Sphere d | chord d (normalPoint d R 0) v ≤
        2 * Real.sin (T / (2 * R))} :=
    normalInverse_closedBall_preimage d hR hT.le hTpi
  have hcy : chord d (normalPoint d R 0) y ≤ 2 * Real.sin (T / (2 * R)) :=
    by simpa only [hcap, Set.mem_setOf_eq] using hy
  have hcz : chord d (normalPoint d R 0) z ≤ 2 * Real.sin (T / (2 * R)) :=
    by simpa only [hcap, Set.mem_setOf_eq] using hz
  have hdiam : chord d y z ≤ 2 * Real.sin (T / (2 * R)) +
      2 * Real.sin (T / (2 * R)) := by
    simpa only [chord, Subtype.dist_eq, dist_eq_norm] using
      (dist_triangle y (normalPoint d R 0) z).trans
        (add_le_add (by simpa only [chord, Subtype.dist_eq, dist_eq_norm,
          norm_sub_rev] using hcy)
          (by simpa only [chord, Subtype.dist_eq, dist_eq_norm] using hcz))
  nlinarith [(le_div_iff₀ hR).mp (normalCapRadius_bounds hR hT hTpi).2.2]

/-- The square of the count splits into diagonal and unequal-label terms. -/
theorem sphereLocalCounting_ball_sq_eq (d N : ℕ) (R T : ℝ)
    (x : Fin N → Sphere d) (U : Problem1.Orthogonal d) :
    (sphereLocalCounting d N R x U (Metric.closedBall (0 : Rd d) T)) ^ 2 =
      sphereLocalCounting d N R x U (Metric.closedBall (0 : Rd d) T) +
        sphereLocalBallPairCount d N R T x U := by
  simp only [sphereLocalCounting, Measure.finsetSum_apply, apply_ite,
    Measure.coe_zero, ite_apply, Pi.zero_apply, Measure.dirac_apply' _ measurableSet_closedBall,
    Set.indicator, Pi.one_apply, ← ite_and]
  let b : Fin N → ℝ≥0∞ := fun i =>
    if rotateSphere d U (x i) ∈ northHemisphere d ∧
      normalInverse d R (rotateSphere d U (x i)).val ∈ Metric.closedBall (0 : Rd d) T
    then 1 else 0
  change (∑ i, b i) ^ 2 = (∑ i, b i) + sphereLocalBallPairCount d N R T x U
  have hb (i : Fin N) : b i * b i = b i := by simp [b]
  have hpair : sphereLocalBallPairCount d N R T x U =
      ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else b i * b j := by
    simp only [sphereLocalBallPairCount, b, sphereNormalBall, Set.mem_setOf_eq]
    simp only [mul_ite, mul_one, mul_zero, ← ite_and, and_comm]
  have hterm (i j : Fin N) : b i * b j =
      (if i = j then b i else 0) + (if i = j then 0 else b i * b j) := by
    by_cases hij : i = j
    all_goals simp [hij, hb]
  calc
    (∑ i, b i) ^ 2 = ∑ i, ∑ j, b i * b j := by rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, ((if i = j then b i else 0) +
        (if i = j then 0 else b i * b j)) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))
    _ = (∑ i, b i) + sphereLocalBallPairCount d N R T x U := by
      simp [Finset.sum_add_distrib, hpair]

/-- Local unequal-label pairs are controlled by the spherical Gaussian sum. -/
theorem sphereLocalBallPairCount_le_gaussian (d N : ℕ) {R : ℝ}
    (hR : 0 < R) (a T : ℝ) (ha : 0 ≤ a) (hT : 0 < T)
    (hTpi : T < Real.pi * R / 2)
    (x : Fin N → Sphere d) (U : Problem1.Orthogonal d) :
    sphereLocalBallPairCount d N R T x U ≤
      ENNReal.ofReal (Real.exp (4 * a * T ^ 2)) *
        sphereAnchoredGaussianPairSum d N R a T x U := by
  simp only [sphereLocalBallPairCount, sphereAnchoredGaussianPairSum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  by_cases hij : i = j
  · simp [hij]
  · by_cases hpair : rotateSphere d U (x i) ∈ sphereNormalBall d R T ∧
      rotateSphere d U (x j) ∈ sphereNormalBall d R T
    · have hdiam := sphereNormalBall_scaled_chord_le d hR hT hTpi hpair.1 hpair.2
      have hweight : -(a * R ^ 2) *
          chord d (rotateSphere d U (x i)) (rotateSphere d U (x j)) ^ 2 ≥
          -(4 * a * T ^ 2) := by
        nlinarith [mul_nonneg ha (mul_nonneg (sub_nonneg.mpr hdiam)
          (show 0 ≤ 2 * T + R *
            chord d (rotateSphere d U (x i)) (rotateSphere d U (x j)) from
              by unfold chord; positivity))]
      simpa only [hij, if_false, hpair, hpair.1, and_self, if_true, ← ENNReal.ofReal_mul
        (Real.exp_nonneg _), ← Real.exp_add, ← ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (by linarith :
            0 ≤ 4 * a * T ^ 2 + -(a * R ^ 2) *
              chord d (rotateSphere d U (x i)) (rotateSphere d U (x j)) ^ 2))
    · simp [hij, hpair]

/-- Haar averaging uses only the first label's uniform spherical marginal. -/
theorem sphereAnchoredGaussianPairSum_mean (d N : ℕ) (hN : 0 < N)
    (a T : ℝ) (x : Fin N → Sphere d) :
    (∫⁻ U, sphereAnchoredGaussianPairSum d N (sphericalRadius d N) a T x U
      ∂uniformRotationLaw d) =
      ((N : ℝ≥0∞) * sphericalMeasure d
        (sphereNormalBall d (sphericalRadius d N) T)) *
          ENNReal.ofReal (sphericalGaussianPairProfile d N x a) := by
  have hA : MeasurableSet (sphereNormalBall d (sphericalRadius d N) T) :=
    (northHemisphere_isOpen d).measurableSet.inter
      (measurableSet_closedBall.preimage
        ((normalInverse_continuous d (sphericalRadius d N)).measurable.comp
          measurable_subtype_coe))
  let w : Fin N → Fin N → ℝ≥0∞ := fun i j =>
    if i = j then 0 else ENNReal.ofReal (Real.exp
      (-(a * (sphericalRadius d N) ^ 2) * (chord d (x i) (x j)) ^ 2))
  have hsum (U : Problem1.Orthogonal d) :
      sphereAnchoredGaussianPairSum d N (sphericalRadius d N) a T x U =
        ∑ i : Fin N, if rotateSphere d U (x i) ∈
          sphereNormalBall d (sphericalRadius d N) T then ∑ j : Fin N, w i j else 0 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : rotateSphere d U (x i) ∈ sphereNormalBall d (sphericalRadius d N) T
    all_goals simp [hi, w, rotateSphere_chord]
  have heval (i : Fin N) :
      (∫⁻ U, if rotateSphere d U (x i) ∈ sphereNormalBall d (sphericalRadius d N) T
        then ∑ j : Fin N, w i j else 0 ∂uniformRotationLaw d) =
          (∑ j : Fin N, w i j) *
            sphericalMeasure d (sphereNormalBall d (sphericalRadius d N) T) :=
    ((uniformRotationLaw_measurePreserving d (x i)).lintegral_comp
      ((show Measurable (fun _ : Sphere d => ∑ j : Fin N, w i j) from
        measurable_const).indicator hA)).trans (lintegral_indicator_const hA _)
  have hnormal : (N : ℝ) * sphericalGaussianPairProfile d N x a =
      ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else Real.exp
        (-(a * (sphericalRadius d N) ^ 2) * (chord d (x i) (x j)) ^ 2) := by
    simp only [sphericalGaussianPairProfile, ← mul_assoc,
      mul_inv_cancel₀ (show (N : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hN.ne'), one_mul]
  have hnormalENN : (N : ℝ≥0∞) * ENNReal.ofReal (sphericalGaussianPairProfile d N x a) =
      ∑ i : Fin N, ∑ j : Fin N, w i j := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N), hnormal]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    simp only [apply_ite, ENNReal.ofReal_zero, w]
  simp_rw [hsum]
  rw [lintegral_finsetSum Finset.univ (fun i _ =>
    measurable_const.ite (hA.preimage (uniformRotationLaw_measurePreserving d (x i)).measurable)
      measurable_const)]
  simp only [heval, ← Finset.sum_mul, ← hnormalENN]
  ac_rfl

/-- Exact Gaussian-profile control of the actual counting law's ball second moment. -/
theorem sphereLocalCountingProbability_ball_second_moment_le
    (d N : ℕ) (hN : 0 < N) (a T : ℝ) (ha : 0 ≤ a) (hT : 0 < T)
    (hTpi : T < Real.pi * sphericalRadius d N / 2)
    (x : Fin N → Sphere d) :
    (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
      ∂(sphereLocalCountingProbability d N (sphericalRadius d N) x).toMeasure) ≤
      ((N : ℝ≥0∞) * sphericalMeasure d
        (sphereNormalBall d (sphericalRadius d N) T)) *
          (1 + ENNReal.ofReal (Real.exp (4 * a * T ^ 2) *
            sphericalGaussianPairProfile d N x a)) := by
  simp only [sphereLocalCountingProbability, ProbabilityMeasure.coe_mk,
    lintegral_map
      (f := fun μ : CountingConfiguration d => (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2)
      (((Measure.measurable_coe measurableSet_closedBall).comp measurable_subtype_coe).pow_const 2)
      (measurable_sphereLocalConfiguration_fixed d N (sphericalRadius d N) x),
    sphereLocalConfiguration]
  simp_rw [sphereLocalCounting_ball_sq_eq]
  rw [lintegral_add_left
    (f := fun U => sphereLocalCounting d N (sphericalRadius d N) x U
      (Metric.closedBall (0 : Rd d) T)) ((Measure.measurable_coe
    (show MeasurableSet (Metric.closedBall (0 : Rd d) T) from measurableSet_closedBall)).comp
    (measurable_sphereLocalCounting_fixed d N (sphericalRadius d N) x)),
    sphereLocalCounting_mean d N (sphericalRadius d N) x _ measurableSet_closedBall]
  have hpair := lintegral_mono (μ := uniformRotationLaw d) (sphereLocalBallPairCount_le_gaussian d N
    (sphericalRadius_pos d N hN) a T ha hT hTpi x)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    sphereAnchoredGaussianPairSum_mean d N hN a T x] at hpair
  simpa only [sphereNormalBall, mul_add, mul_one,
    ENNReal.ofReal_mul (Real.exp_nonneg _), mul_left_comm, mul_assoc, add_comm] using
      add_le_add_left hpair ((N : ℝ≥0∞) * sphericalMeasure d
        (sphereNormalBall d (sphericalRadius d N) T))

/-- A bound for the finite prefix, independent of the enlargement or profile. -/
theorem sphereLocalCountingProbability_ball_second_moment_le_count_sq
    (d N : ℕ) (R T : ℝ) (x : Fin N → Sphere d) :
    (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
      ∂(sphereLocalCountingProbability d N R x).toMeasure) ≤
        (N : ℝ≥0∞) ^ 2 := by
  have hcount (U : Problem1.Orthogonal d) :
      sphereLocalCounting d N R x U (Metric.closedBall (0 : Rd d) T) ≤ (N : ℝ≥0∞) := by
    simp only [sphereLocalCounting, Measure.finsetSum_apply, apply_ite,
      Measure.coe_zero, ite_apply, Pi.zero_apply, Measure.dirac_apply' _ measurableSet_closedBall,
      Set.indicator, Pi.one_apply, ← ite_and]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] using Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => show (if rotateSphere d U (x i) ∈ northHemisphere d ∧
          normalInverse d R (rotateSphere d U (x i)).val ∈ Metric.closedBall (0 : Rd d) T
          then (1 : ℝ≥0∞) else 0) ≤ 1 from by split <;> norm_num)
  simp only [sphereLocalCountingProbability, ProbabilityMeasure.coe_mk,
    lintegral_map
      (f := fun μ : CountingConfiguration d => (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2)
      (((Measure.measurable_coe measurableSet_closedBall).comp measurable_subtype_coe).pow_const 2)
      (measurable_sphereLocalConfiguration_fixed d N R x), sphereLocalConfiguration]
  simpa only [lintegral_const, measure_univ, mul_one] using
    lintegral_mono (μ := uniformRotationLaw d) (fun U => pow_le_pow_left' (hcount U) 2)

/-- A prescribed-scale profile bound and the certified coarse cap bound suffice. -/
theorem sphereLocalCountingProbability_ball_second_moment_le_of_profile_le
    (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (a T M : ℝ) (ha : 0 ≤ a) (hT : 0 < T)
    (hTpi : T < Real.pi * sphericalRadius d N / 2)
    (x : Fin N → Sphere d) (hprofile : sphericalGaussianPairProfile d N x a ≤ M) :
    (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
      ∂(sphereLocalCountingProbability d N (sphericalRadius d N) x).toMeasure) ≤
        ENNReal.ofReal (omega d * Problem1.capConstant d * T ^ d *
          (1 + Real.exp (4 * a * T ^ 2) * M)) := by
  have hcap := sphericalMeasure_normalBall_mul_le d N hd hN T hT hTpi
  have hM : 0 ≤ M := (sphericalGaussianPairProfile_nonneg d N x a).trans hprofile
  have hw : 1 + ENNReal.ofReal (Real.exp (4 * a * T ^ 2) *
      sphericalGaussianPairProfile d N x a) ≤
      ENNReal.ofReal (1 + Real.exp (4 * a * T ^ 2) * M) := by
    rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg (Real.exp_nonneg _) hM),
      ENNReal.ofReal_one]
    exact add_le_add_right (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hprofile (Real.exp_nonneg _))) 1
  exact (sphereLocalCountingProbability_ball_second_moment_le d N hN a T ha hT hTpi x).trans
    ((mul_le_mul' hcap hw).trans_eq (ENNReal.ofReal_mul
      (mul_nonneg (mul_nonneg (sphericalArea_pos d).le
        (Problem1.cap_constant_positive d hd).le) (pow_nonneg hT.le d))).symm)

/-- Eventual profile control gives uniform second moments, including the finite prefix. -/
theorem exists_sphereLocalCountingProbability_ball_second_moment_bound
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ)
    (x : ∀ n, Fin (N n) → Sphere d) (hN : Tendsto N atTop atTop)
    (a M : ℝ) (ha : 0 ≤ a)
    (hprofile : ∀ᶠ n in atTop, sphericalGaussianPairProfile d (N n) (x n) a ≤ M)
    (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(sphereLocalCountingProbability d (N n) (sphericalRadius d (N n))
          (x n)).toMeasure) ≤ C := by
  have hR : Tendsto (fun n => Real.pi * sphericalRadius d (N n) / 2) atTop atTop :=
    (Tendsto.const_mul_atTop Real.pi_pos
      ((sphericalRadius_tendsto_atTop d (by omega)).comp hN)).atTop_div_const (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (((hN.eventually_gt_atTop 0).and (hR.eventually_gt_atTop T)).and hprofile)
  refine ⟨(∑ n ∈ Finset.range K, (N n : ℝ≥0∞) ^ 2) +
    ENNReal.ofReal (omega d * Problem1.capConstant d * T ^ d *
      (1 + Real.exp (4 * a * T ^ 2) * M)), ?_, ?_⟩
  · simp
  · intro n
    by_cases hn : K ≤ n
    · exact (sphereLocalCountingProbability_ball_second_moment_le_of_profile_le d (N n)
        hd (hK n hn).1.1 a T M ha hT (hK n hn).1.2 (x n) (hK n hn).2).trans
          (le_add_of_nonneg_left zero_le)
    · exact ((sphereLocalCountingProbability_ball_second_moment_le_count_sq d (N n)
        (sphericalRadius d (N n)) T (x n)).trans
          (Finset.single_le_sum (f := fun j => (N j : ℝ≥0∞) ^ 2)
            (fun _ _ => zero_le) (Finset.mem_range.mpr (not_le.mp hn)))).trans
            (le_add_of_nonneg_right zero_le)

/-- Bounded actual scaled energies give uniform local second moments. -/
theorem exists_sphereLocalCountingProbability_ball_second_moment_bound_of_energy_bound
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : -2 < s) (hsd : s < (d : ℝ)) (hsne : s ≠ 0)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (henergy : ∃ L : ℝ, ∀ᶠ n in atTop,
      scaledSphericalKernelEnergy d (N n) s (x n) ≤ L)
    (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(sphereLocalCountingProbability d (N n) (sphericalRadius d (N n))
          (x n).val).toMeasure) ≤ C := by
  obtain ⟨M, hprofile⟩ := eventually_sphericalGaussianPairProfile_one_bounded
    d hd s hs hsd hsne N hN x henergy
  exact exists_sphereLocalCountingProbability_ball_second_moment_bound
    d hd N (fun n => (x n).val) hN 1 M (by norm_num) hprofile T hT

end Riesz.Asymptotics
