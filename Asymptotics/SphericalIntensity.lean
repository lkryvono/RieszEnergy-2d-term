import Riesz.Asymptotics.SphericalLimitMoments
import Riesz.Asymptotics.SphericalLocalLaw
import Riesz.Geometry.SmallCaps
import Riesz.Stationary.MeanMeasure

/-!
# Intensity of spherical local limits

Compact-test expectations and the sharp normal-unit-ball mean identify the
mean density of a stationary weak limit, without continuity of ball counts.
-/

noncomputable section

open MeasureTheory Filter Set RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal NNReal Topology Classical CompactlySupported

namespace Riesz.Asymptotics

/-- A nonnegative compact-test expectation is its integral against the first
mean measure. The identity also holds when the extended expectation is infinite. -/
theorem countingLaw_nonneg_test_expectation_eq_meanIntegral (d : ℕ)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (f : C_c(Rd d, ℝ)) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ μ, (∫ x, f x ∂μ.val) ∂Q.toMeasure) =
      ∫ x, f x ∂(Q.toMeasure.map Subtype.val).join := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun μ : CountingConfiguration d =>
      integral_nonneg (μ := μ.val) hf0))
    (measurable_countingIntegral d f).aestronglyMeasurable]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0)
    f.continuous.measurable.aestronglyMeasurable]
  rw [Measure.lintegral_join (f := fun x : Rd d => ENNReal.ofReal (f x))
      f.continuous.measurable.ennreal_ofReal.aemeasurable,
    lintegral_map (Measure.measurable_lintegral (show
      Measurable (fun x : Rd d => ENNReal.ofReal (f x)) from
        f.continuous.measurable.ennreal_ofReal))
      measurable_subtype_coe]
  congr 1
  exact lintegral_congr (fun μ => ofReal_integral_eq_lintegral_ofReal
    (f.integrable (μ := μ.val)) (Eventually.of_forall hf0))

/-- Finite ball second moments make the first mean measure locally finite. -/
theorem countingLaw_mean_isFiniteMeasureOnCompacts_of_second_moment_bound (d : ℕ)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2 ∂Q.toMeasure) ≤ C) :
    IsFiniteMeasureOnCompacts (Q.toMeasure.map Subtype.val).join := by
  letI : IsProbabilityMeasure (Q.toMeasure.map Subtype.val) :=
    Q.toMeasure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  exact Riesz.Stationary.join_isFiniteMeasureOnCompacts d _
    (countingLaw_limit_ambient_local_second_moments d (fun _ => Q) Q tendsto_const_nhds
      (fun T hT => by
        obtain ⟨C, hC, hbound⟩ := hball T hT
        exact ⟨C, hC, fun _ => hbound⟩))

/-- Nonnegative compact-test convergence and the unit-ball mass fix a constant
limiting density. Inner and outer bumps avoid a boundary-count continuity lemma. -/
theorem smul_volume_eq_volume_of_nonneg_compact_test_limits (d : ℕ)
    (P : ℕ → Measure (Rd d)) [∀ n, IsFiniteMeasureOnCompacts (P n)] (c : ℝ≥0)
    (htest : ∀ f : C_c(Rd d, ℝ), (∀ x, 0 ≤ f x) →
      Tendsto (fun n => ∫ x, f x ∂P n) atTop
        (𝓝 (∫ x, f x ∂(c • (volume : Measure (Rd d))))))
    (hunit : Tendsto (fun n => (P n).real (Metric.closedBall (0 : Rd d) 1)) atTop
      (𝓝 ((volume : Measure (Rd d)).real (Metric.closedBall (0 : Rd d) 1)))) :
    c • (volume : Measure (Rd d)) = volume := by
  let v := (volume : Measure (Rd d)).real (Metric.closedBall (0 : Rd d) 1)
  have hv : 0 < v := ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_closedBall_pos (volume : Measure (Rd d)) 0 zero_lt_one))
    (measure_closedBall_lt_top (μ := (volume : Measure (Rd d)))).ne
  have hinner (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
      (c : ℝ) * (volume : Measure (Rd d)).real (Metric.closedBall 0 r) ≤ v := by
    obtain ⟨g, hg1, hgc, hgs, hgr⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen
        (isCompact_closedBall (0 : Rd d) r) Metric.isOpen_ball
        (Metric.closedBall_subset_ball hr1)
    let f : C_c(Rd d, ℝ) := ⟨g, hgc⟩
    have hf0 : ∀ x, 0 ≤ f x := fun x => (hgr x).1
    have hpre (n : ℕ) : (∫ x, f x ∂P n) ≤
        (P n).real (Metric.closedBall (0 : Rd d) 1) :=
      (ENNReal.ofReal_le_iff_le_toReal
        (measure_closedBall_lt_top (μ := P n)).ne).mp
          (integral_le_measure (fun x _ => (hgr x).2)
            (fun x hx => le_of_eq (image_eq_zero_of_notMem_tsupport
              (f := (g : Rd d → ℝ))
              (fun ht => hx (Metric.ball_subset_closedBall (hgs ht))))))
    have hlim : (∫ x, f x ∂(c • (volume : Measure (Rd d)))) ≤ v :=
      le_of_tendsto_of_tendsto (htest f hf0) hunit (Eventually.of_forall hpre)
    have hlow : (c • (volume : Measure (Rd d))).real (Metric.closedBall 0 r) ≤
        ∫ x, f x ∂(c • (volume : Measure (Rd d))) := by
      simpa only [measureReal_def, ENNReal.toReal_ofReal
        (integral_nonneg (μ := c • (volume : Measure (Rd d))) hf0)] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top
          ((f.integrable (μ := c • (volume : Measure (Rd d)))).measure_le_integral
            (Eventually.of_forall hf0) (fun x hx => (hg1 hx).ge))
    rw [measureReal_nnreal_smul_apply] at hlow
    exact hlow.trans hlim
  have houter (R : ℝ) (hR : 1 < R) :
      v ≤ (c : ℝ) * (volume : Measure (Rd d)).real (Metric.closedBall 0 R) := by
    obtain ⟨g, hg1, hgc, hgs, hgr⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen
        (isCompact_closedBall (0 : Rd d) 1) Metric.isOpen_ball
        (Metric.closedBall_subset_ball hR)
    let f : C_c(Rd d, ℝ) := ⟨g, hgc⟩
    have hf0 : ∀ x, 0 ≤ f x := fun x => (hgr x).1
    have hpre (n : ℕ) : (P n).real (Metric.closedBall (0 : Rd d) 1) ≤
        ∫ x, f x ∂P n := by
      simpa only [measureReal_def, ENNReal.toReal_ofReal
        (integral_nonneg (μ := P n) hf0)] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top
          ((f.integrable (μ := P n)).measure_le_integral
            (Eventually.of_forall hf0) (fun x hx => (hg1 hx).ge))
    have hlim : v ≤ ∫ x, f x ∂(c • (volume : Measure (Rd d))) :=
      le_of_tendsto_of_tendsto hunit (htest f hf0) (Eventually.of_forall hpre)
    have hupp : (∫ x, f x ∂(c • (volume : Measure (Rd d)))) ≤
        (c • (volume : Measure (Rd d))).real (Metric.closedBall 0 R) :=
      (ENNReal.ofReal_le_iff_le_toReal
        (measure_closedBall_lt_top (μ := c • (volume : Measure (Rd d)))).ne).mp
          (integral_le_measure (fun x _ => (hgr x).2)
            (fun x hx => le_of_eq (image_eq_zero_of_notMem_tsupport
              (f := (g : Rd d → ℝ))
              (fun ht => hx (Metric.ball_subset_closedBall (hgs ht))))))
    rw [measureReal_nnreal_smul_apply] at hupp
    exact hlim.trans hupp
  have hscale : Continuous (fun r : ℝ => (c : ℝ) * (r ^ Module.finrank ℝ (Rd d) * v)) := by
    fun_prop
  have hleft : (c : ℝ) * v ≤ v := by
    apply le_of_tendsto (f := fun r : ℝ => (c : ℝ) * (r ^ Module.finrank ℝ (Rd d) * v))
      (x := 𝓝[<] (1 : ℝ))
      (by simpa only [one_pow, one_mul] using
        (hscale.tendsto 1).mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsLT (a := (0 : ℝ)) zero_lt_one] with r hr
    simpa only [Measure.addHaar_real_closedBall' (volume : Measure (Rd d)) 0 hr.1.le] using
      hinner r hr.1 hr.2
  have hright : v ≤ (c : ℝ) * v := by
    apply ge_of_tendsto (f := fun R : ℝ => (c : ℝ) * (R ^ Module.finrank ℝ (Rd d) * v))
      (x := 𝓝[>] (1 : ℝ))
      (by simpa only [one_pow, one_mul] using
        (hscale.tendsto 1).mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with R hR
    simpa only [Measure.addHaar_real_closedBall' (volume : Measure (Rd d)) 0
      (zero_lt_one.trans hR).le] using houter R hR
  have hc : c = 1 := NNReal.coe_injective
    ((mul_eq_right₀ hv.ne').mp (le_antisymm hleft hright))
  simp only [hc, one_smul]

/-- A stationary weak limit has intensity one once the prelimit unit-ball mean
has the Euclidean value and local count squares are uniformly bounded. -/
theorem countingLaw_limit_mean_eq_volume_of_unitBall (d : ℕ)
    (P : ℕ → ProbabilityMeasure (CountingConfiguration d))
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto P atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2 ∂(P n).toMeasure) ≤ C)
    (hstationary : IsStationary d (Q.toMeasure.map Subtype.val))
    (hunit : Tendsto (fun n =>
      (∫⁻ μ, μ.val (Metric.closedBall (0 : Rd d) 1) ∂(P n).toMeasure).toReal) atTop
      (𝓝 ((volume : Measure (Rd d)).real (Metric.closedBall (0 : Rd d) 1)))) :
    (Q.toMeasure.map Subtype.val).join = volume := by
  let M (n : ℕ) := ((P n).toMeasure.map Subtype.val).join
  letI (n : ℕ) : IsFiniteMeasureOnCompacts (M n) :=
    countingLaw_mean_isFiniteMeasureOnCompacts_of_second_moment_bound d (P n)
      (fun T hT => by
        obtain ⟨C, hC, hbound⟩ := hball T hT
        exact ⟨C, hC, hbound n⟩)
  letI : IsProbabilityMeasure (Q.toMeasure.map Subtype.val) :=
    Q.toMeasure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  obtain ⟨c, hc⟩ := Riesz.Stationary.join_eq_smul_volume d _ hstationary
    (countingLaw_limit_ambient_local_second_moments d P Q hQ hball)
  rw [hc]
  apply smul_volume_eq_volume_of_nonneg_compact_test_limits d M c
  · intro f hf0
    have heq (Q' : ProbabilityMeasure (CountingConfiguration d)) :=
      countingLaw_nonneg_test_expectation_eq_meanIntegral d Q' f hf0
    simpa only [heq, hc, M] using
      countingLaw_nonneg_test_expectations_tendsto d P Q hQ hball f hf0
  · simpa only [M, measureReal_def, Measure.join_apply measurableSet_closedBall,
      lintegral_map (Measure.measurable_coe measurableSet_closedBall) measurable_subtype_coe]
      using hunit

/-- The exact Haar first mean and the sharp cap normalization give the unit-ball
mean limit for every diverging sequence of spherical point counts. -/
theorem sphereLocalCountingProbability_unitBall_mean_tendsto (d : ℕ) (hd : 2 ≤ d)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d) :
    Tendsto (fun n => (∫⁻ μ, μ.val (Metric.closedBall (0 : Rd d) 1)
      ∂(sphereLocalCountingProbability d (N n) (sphericalRadius d (N n)) (x n)).toMeasure).toReal)
      atTop (𝓝 ((volume : Measure (Rd d)).real (Metric.closedBall (0 : Rd d) 1))) := by
  simpa only [Function.comp_def,
    sphereLocalCountingProbability_mean d _ _ _ _ measurableSet_closedBall,
    ENNReal.toReal_mul, ENNReal.toReal_natCast] using
      (tendsto_enlargedSphere_normalUnitBall_mean d hd).comp hN

/-- Actual spherical local limits have the exact Showcase first mean, provided
stationarity has been established. No simplicity hypothesis is used here. -/
theorem sphereLocalCountingProbability_limit_mean_eq_volume (d : ℕ) (hd : 2 ≤ d)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto
      (fun n => sphereLocalCountingProbability d (N n) (sphericalRadius d (N n)) (x n))
      atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(sphereLocalCountingProbability d (N n) (sphericalRadius d (N n)) (x n)).toMeasure) ≤ C)
    (hstationary : IsStationary d (Q.toMeasure.map Subtype.val)) :
    (Q.toMeasure.map Subtype.val).join = volume := by
  exact countingLaw_limit_mean_eq_volume_of_unitBall d _ Q hQ hball hstationary
    (sphereLocalCountingProbability_unitBall_mean_tendsto d hd N hN x)

end Riesz.Asymptotics
