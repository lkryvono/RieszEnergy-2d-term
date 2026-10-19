import Riesz.Asymptotics.SphericalTightness
import Riesz.Asymptotics.SphericalIntensity
import Riesz.Configuration.Translations
import Riesz.Geometry.TranslationRotations
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! Compact-test errors for small rotations of the actual spherical local law.
All sums retain the original labels, including repeated sites.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Asymptotics

/-- A test on the normal chart, extended by zero over the other hemisphere. -/
def hemisphereChartTest (d : ℕ) (R : ℝ) (g : Rd d → ℝ) (y : Sphere d) : ℝ :=
  if y ∈ northHemisphere d then g (normalInverse d R y.val) else 0

theorem integral_sphereLocalCounting_eq_sum (d N : ℕ) (R : ℝ)
    (x : Fin N → Sphere d) (U : Problem1.Orthogonal d) (g : Rd d → ℝ) :
    (∫ z, g z ∂sphereLocalCounting d N R x U) =
      ∑ i, hemisphereChartTest d R g (rotateSphere d U (x i)) := by
  rw [sphereLocalCounting, integral_finsetSum_measure]
  · simp only [hemisphereChartTest, apply_ite (fun μ : Measure (Rd d) => ∫ z, g z ∂μ),
      integral_dirac, integral_zero_measure]
  · intro i hi
    split_ifs <;> first | exact integrable_dirac (by simp) | simp

/-- A small spherical rotation changes a compact chart test only on a fixed cap,
and changes each label there by an arbitrarily small amount. -/
theorem eventually_hemisphereChartTest_rotation_error (d : ℕ) (a : Rd d)
    (f : C_c(Rd d, ℝ)) (S : ℝ)
    (hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) S) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t → ∀ y : Sphere d,
      ‖hemisphereChartTest d t⁻¹ f (rotateSphere d (normalTranslationOrthogonal d a t) y) -
        hemisphereChartTest d t⁻¹ (fun z => f (a + z)) y‖ₑ ≤
      ENNReal.ofReal ε *
        (if y ∈ northHemisphere d ∧
          ‖normalInverse d t⁻¹ y.val‖ ≤ S + ‖a‖ + 1 then 1 else 0) := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (f.hasCompactSupport.uniformContinuous_of_continuous f.continuous) ε hε
  filter_upwards [normalTranslationAxis_ne_mem_nhds d a,
    eventually_rotate_cap_subset d a (S + ‖a‖ + 1),
    eventually_translation_cap_preimage_subset d a S,
    Metric.tendstoUniformlyOn_iff.mp
      (normalTranslationCoordinates_tendstoUniformlyOn d a
        (isCompact_closedBall (0 : Rd d) (S + ‖a‖ + 1))) δ hδ]
    with t haxis hforward hback hdist ht y
  by_cases hlocal : y ∈ northHemisphere d ∧
    ‖normalInverse d t⁻¹ y.val‖ ≤ S + ‖a‖ + 1
  · have hrot := (hforward ht y hlocal.1 hlocal.2).1
    simp only [hemisphereChartTest, if_pos hlocal.1, if_pos hrot, if_pos hlocal, mul_one]
    have hpoint : normalPoint d t⁻¹ (normalInverse d t⁻¹ y.val) = y :=
      normalPoint_normalInverse d (inv_pos.mpr ht) hlocal.1
    have hcoord := normalInverse_rotate_normalPoint d a
      (normalInverse d t⁻¹ y.val) ht.ne' haxis
    rw [hpoint] at hcoord
    have hz : normalInverse d t⁻¹ y.val ∈ Metric.closedBall (0 : Rd d) (S + ‖a‖ + 1) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hlocal.2
    have he := hclose (hdist (normalInverse d t⁻¹ y.val) hz)
    simpa only [hcoord, ← ofReal_norm, dist_eq_norm, norm_sub_rev] using
      ENNReal.ofReal_le_ofReal he.le
  · have hzeroRot : hemisphereChartTest d t⁻¹ f
        (rotateSphere d (normalTranslationOrthogonal d a t) y) = 0 := by
      by_cases hy : rotateSphere d (normalTranslationOrthogonal d a t) y ∈ northHemisphere d
      · simp only [hemisphereChartTest, if_pos hy]
        by_contra hn
        have hs : ‖normalInverse d t⁻¹
            (rotateSphere d (normalTranslationOrthogonal d a t) y).val‖ ≤ S := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hf (subset_tsupport f hn)
        exact hlocal ⟨(hback ht y hy hs).1, (hback ht y hy hs).2.le⟩
      · simp [hemisphereChartTest, hy]
    have hzeroTrans : hemisphereChartTest d t⁻¹ (fun z => f (a + z)) y = 0 := by
      by_cases hy : y ∈ northHemisphere d
      · simp only [hemisphereChartTest, if_pos hy]
        by_contra hn
        have hs : ‖a + normalInverse d t⁻¹ y.val‖ ≤ S := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hf (subset_tsupport f hn)
        have hnadd : ‖normalInverse d t⁻¹ y.val‖ ≤ ‖a + normalInverse d t⁻¹ y.val‖ + ‖a‖ := by
          simpa using norm_sub_le (a + normalInverse d t⁻¹ y.val) a
        exact hlocal ⟨hy, (hnadd.trans (add_le_add hs le_rfl)).trans
          (le_add_of_nonneg_right zero_le_one)⟩
      · simp [hemisphereChartTest, hy]
    simp [hzeroRot, hzeroTrans, hlocal]

theorem sphereLocalCounting_closedBall_eq_sum (d N : ℕ) (R S : ℝ)
    (x : Fin N → Sphere d) (U : Problem1.Orthogonal d) :
    sphereLocalCounting d N R x U (Metric.closedBall (0 : Rd d) S) =
      ∑ i, if rotateSphere d U (x i) ∈ northHemisphere d ∧
        ‖normalInverse d R (rotateSphere d U (x i)).val‖ ≤ S then 1 else 0 := by
  simp only [sphereLocalCounting, Measure.finsetSum_apply, apply_ite,
    Measure.coe_zero, ite_apply, Pi.zero_apply,
    Measure.dirac_apply' _ measurableSet_closedBall, Set.indicator, Pi.one_apply,
    Metric.mem_closedBall, dist_zero_right, ← ite_and]

theorem eventually_sphereLocalCounting_rotation_translation_error (d : ℕ) (a : Rd d)
    (f : C_c(Rd d, ℝ)) (S : ℝ)
    (hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) S) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t → ∀ (N : ℕ) (x : Fin N → Sphere d)
        (U : Problem1.Orthogonal d),
      ‖(∫ z, f z ∂sphereLocalCounting d N t⁻¹ x
          (normalTranslationOrthogonal d a t * U)) -
        (∫ z, translatedCountingTest d a f z ∂sphereLocalCounting d N t⁻¹ x U)‖ₑ ≤
      ENNReal.ofReal ε *
        sphereLocalCounting d N t⁻¹ x U (Metric.closedBall 0 (S + ‖a‖ + 1)) := by
  filter_upwards [eventually_hemisphereChartTest_rotation_error d a f S hf ε hε]
    with t herror ht N x U
  simp only [integral_sphereLocalCounting_eq_sum, translatedCountingTest_apply,
    rotateSphere_mul, sphereLocalCounting_closedBall_eq_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  exact (enorm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => herror ht (rotateSphere d U (x i))))

/-- The actual spherical producer is asymptotically translation equivariant on
every compact test, in Haar mean. -/
theorem tendsto_sphereLocalCounting_rotation_translation_L1
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d) (a : Rd d) (f : C_c(Rd d, ℝ)) :
    Tendsto (fun n => ∫⁻ U,
      ‖(∫ z, f z ∂sphereLocalCounting d (N n) (sphericalRadius d (N n)) (x n)
          (normalTranslationOrthogonal d a ((sphericalRadius d (N n))⁻¹) * U)) -
        (∫ z, translatedCountingTest d a f z ∂sphereLocalCounting d (N n)
          (sphericalRadius d (N n)) (x n) U)‖ₑ ∂uniformRotationLaw d) atTop (𝓝 0) := by
  obtain ⟨S, hS⟩ := f.hasCompactSupport.isBounded.exists_norm_le
  have hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) (max 1 S) := fun z hz => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hS z hz).trans (le_max_right 1 S)
  obtain ⟨C, hCfinite, hC⟩ := exists_sphereLocalCountingProbability_ball_mean_bound d hd
    (max 1 S + ‖a‖ + 1) (by positivity)
  have hCHaar (M : ℕ) (y : Fin M → Sphere d) :
      (∫⁻ U, sphereLocalCounting d M (sphericalRadius d M) y U
        (Metric.closedBall 0 (max 1 S + ‖a‖ + 1)) ∂uniformRotationLaw d) ≤ C := by
    simpa only [sphereLocalCounting_mean, sphereLocalCountingProbability_mean,
      measurableSet_closedBall] using hC M y
  have ht : Tendsto (fun n => (sphericalRadius d (N n))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((sphericalRadius_tendsto_atTop d (by omega)).comp hN)
  have hpos : ∀ᶠ n in atTop, 0 < (sphericalRadius d (N n))⁻¹ :=
    (hN.eventually (eventually_gt_atTop 0)).mono
      (fun n hn => inv_pos.mpr (sphericalRadius_pos d (N n) hn))
  refine ENNReal.tendsto_nhds_zero.mpr ?_
  intro η hη
  obtain ⟨δ, hδ, hδC⟩ := ENNReal.exists_nnreal_pos_mul_lt hCfinite hη.ne'
  filter_upwards [ht.eventually
    (eventually_sphereLocalCounting_rotation_translation_error d a f (max 1 S) hf
      (δ : ℝ) (by exact_mod_cast hδ)), hpos] with n hn hnpos
  have hb := hn hnpos (N n) (x n)
  simp only [inv_inv] at hb
  calc
    _ ≤ ∫⁻ U, ENNReal.ofReal (δ : ℝ) *
        sphereLocalCounting d (N n) (sphericalRadius d (N n)) (x n) U
          (Metric.closedBall 0 (max 1 S + ‖a‖ + 1)) ∂uniformRotationLaw d := lintegral_mono hb
    _ ≤ η := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact (mul_le_mul_right (hCHaar (N n) (x n)) _).trans
        (by simpa only [ENNReal.ofReal_coe_nnreal] using hδC.le)

/-- Coordinatewise convergence in measure suffices for a finite family of real tests. -/
theorem tendstoInMeasure_finite_real_pi {Ω J ι : Type*} [MeasurableSpace Ω]
    [Fintype J] {P : Measure Ω} {l : Filter ι}
    {F : ι → Ω → J → ℝ} {g : Ω → J → ℝ}
    (h : ∀ j, TendstoInMeasure P (fun n ω => F n ω j) l (fun ω => g ω j)) :
    TendstoInMeasure P F l g := by
  intro ε hε
  have hsum : Tendsto (fun n => ∑ j, P {ω | ε ≤ edist (F n ω j) (g ω j)}) l (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ => h j ε hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le) ?_
  intro n
  have hset : {ω | ε ≤ edist (F n ω) (g ω)} =
      ⋃ j, {ω | ε ≤ edist (F n ω j) (g ω j)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, edist_pi_def,
      Finset.le_sup_iff hε, Finset.mem_univ, true_and]
  simpa only [hset] using measure_iUnion_fintype_le P (fun j => {ω | ε ≤ edist (F n ω j) (g ω j)})

theorem tendstoInMeasure_sphereLocalCounting_rotation_translation
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d) (a : Rd d) (f : C_c(Rd d, ℝ)) :
    TendstoInMeasure (uniformRotationLaw d) (fun n U =>
      (∫ z, translatedCountingTest d a f z ∂sphereLocalCounting d (N n)
        (sphericalRadius d (N n)) (x n) U) -
      (∫ z, f z ∂sphereLocalCounting d (N n) (sphericalRadius d (N n)) (x n)
        (normalTranslationOrthogonal d a ((sphericalRadius d (N n))⁻¹) * U))) atTop 0 := by
  have hbase (n : ℕ) := measurable_sphereLocalConfiguration_fixed d (N n)
    (sphericalRadius d (N n)) (x n)
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    (fun n => (((measurable_countingIntegral d (translatedCountingTest d a f)).comp (hbase n)).sub
      ((measurable_countingIntegral d f).comp ((hbase n).comp
        (measurable_const_mul (normalTranslationOrthogonal d a ((sphericalRadius d (N n))⁻¹)))))).aestronglyMeasurable)
    aestronglyMeasurable_zero
  simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply, Pi.zero_apply, sub_zero,
    Function.comp_apply, sphereLocalConfiguration, ← ofReal_norm, norm_sub_rev] using
    tendsto_sphereLocalCounting_rotation_translation_L1 d hd N hN x a f

/-- Every weak limit of the actual rotated spherical counting laws is stationary
under the translations appearing in the Showcase. -/
theorem sphereLocalCountingProbability_limit_stationary
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d) (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto (fun n => sphereLocalCountingProbability d (N n)
      (sphericalRadius d (N n)) (x n)) atTop (𝓝 Q)) :
    IsStationary d (Q.toMeasure.map Subtype.val) := by
  let C (n : ℕ) := sphereLocalConfiguration d (N n) (sphericalRadius d (N n)) (x n)
  have hC (n : ℕ) : Measurable (C n) :=
    measurable_sphereLocalConfiguration_fixed d (N n) (sphericalRadius d (N n)) (x n)
  have hbase : TendstoInDistribution C atTop id (fun _ => uniformRotationLaw d) Q.toMeasure := by
    refine ⟨fun n => (hC n).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id, C, sphereLocalCountingProbability,
      ← ProbabilityMeasure.val_eq_to_measure, Subtype.coe_eta] using hQ
  apply isStationary_map_val_of_countingTestCode_finset
  intro a I
  let A (n : ℕ) := normalTranslationOrthogonal d a ((sphericalRadius d (N n))⁻¹)
  let V : CountingConfiguration d → (I → ℝ) := fun μ => I.restrict (countingTestCode d μ)
  have hV : Continuous V := I.continuous_restrict.comp (continuous_countingTestCode d)
  have hlaw (n : ℕ) : (uniformRotationLaw d).map (fun U => C n (A n * U)) =
      (uniformRotationLaw d).map (C n) := by
    change (uniformRotationLaw d).map (C n ∘ (fun U => A n * U)) = _
    rw [← Measure.map_map (hC n) (measurable_const_mul (A n)),
      uniformRotationLaw_map_mul_left]
  have hrot : TendstoInDistribution (fun n U => C n (A n * U)) atTop id
      (fun _ => uniformRotationLaw d) Q.toMeasure := by
    refine ⟨fun n => ((hC n).comp (measurable_const_mul (A n))).aemeasurable,
      measurable_id.aemeasurable, ?_⟩
    simpa only [hlaw] using hbase.tendsto
  let X (n : ℕ) (U : Problem1.Orthogonal d) := V (C n (A n * U))
  let Y (n : ℕ) (U : Problem1.Orthogonal d) := V (translateCounting d a (C n U))
  have hX : TendstoInDistribution X atTop V (fun _ => uniformRotationLaw d) Q.toMeasure :=
    hrot.continuous_comp hV
  have hY : TendstoInDistribution Y atTop (V ∘ translateCounting d a)
      (fun _ => uniformRotationLaw d) Q.toMeasure :=
    hbase.continuous_comp (hV.comp (continuous_translateCounting d a))
  have herror : TendstoInMeasure (uniformRotationLaw d) (Y - X) atTop 0 := by
    apply tendstoInMeasure_finite_real_pi
    intro i
    change TendstoInMeasure (uniformRotationLaw d) (fun n U =>
      (∫ z, countingTest d i.val z ∂(translateCounting d a (C n U)).val) -
      (∫ z, countingTest d i.val z ∂(C n (A n * U)).val)) atTop 0
    simpa only [integral_translateCounting, C, A, sphereLocalConfiguration] using
      tendstoInMeasure_sphereLocalCounting_rotation_translation d hd N hN x a (countingTest d i.val)
  exact (tendstoInDistribution_unique Y
    (tendstoInDistribution_of_tendstoInMeasure_sub Y V hX herror hY.forall_aemeasurable) hY).symm

/-- The exact limiting first mean follows without an additional stationarity
assumption. The second moments are those already obtained from bounded energies. -/
theorem sphereLocalCountingProbability_limit_mean_eq_volume_unconditional
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d) (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto (fun n => sphereLocalCountingProbability d (N n)
      (sphericalRadius d (N n)) (x n)) atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(sphereLocalCountingProbability d (N n) (sphericalRadius d (N n)) (x n)).toMeasure) ≤ C) :
    (Q.toMeasure.map Subtype.val).join = volume := by
  exact sphereLocalCountingProbability_limit_mean_eq_volume d hd N hN x Q hQ hball
    (sphereLocalCountingProbability_limit_stationary d hd N hN x Q hQ)

end Riesz.Asymptotics
