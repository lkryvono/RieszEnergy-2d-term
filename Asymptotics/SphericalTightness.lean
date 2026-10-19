import Riesz.Asymptotics.SphericalLocalLaw
import Riesz.Asymptotics.SphericalLocalBounds
import Riesz.Configuration.Tightness

/-!
# Tightness of the actual spherical local laws

Coarse cap bounds control all point counts, including the finite prefix before
the cap estimate applies. No sharp intensity limit or second-moment hypothesis
is needed for this extraction step.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Asymptotics

/-- A compact test is bounded by the count in a ball containing its support. -/
theorem countingIntegral_ofReal_le_ball (d n : ℕ) (μ : CountingConfiguration d)
    (f : C_c(Rd d, ℝ))
    (hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ)) :
    ENNReal.ofReal (∫ x, f x ∂μ.val) ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        μ.val (Metric.closedBall (0 : Rd d) (n : ℝ)) := by
  have hbound : |∫ x, f x ∂μ.val| ≤
      ‖f.toBoundedContinuousFunction‖ *
        μ.val.real (Metric.closedBall (0 : Rd d) (n : ℝ)) := by
    simpa using countingIntegral_sub_le d n μ f 0 ‖f.toBoundedContinuousFunction‖ hf
      (by simp) (fun x => by simpa only [CompactlySupportedContinuousMap.zero_apply, sub_zero,
        Real.norm_eq_abs, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply]
        using f.toBoundedContinuousFunction.norm_coe_le_norm x)
  exact (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hbound)).trans
    ((ENNReal.ofReal_mul (norm_nonneg _)).trans_le
      (mul_le_mul_right ENNReal.ofReal_toReal_le _))

/-- Uniform ball-count means for the actual spherical laws, at every point count. -/
theorem exists_sphereLocalCountingProbability_ball_mean_bound (d : ℕ) (hd : 2 ≤ d)
    (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (N : ℕ) (x : Fin N → Sphere d),
      (∫⁻ μ, μ.val (Metric.closedBall (0 : Rd d) T)
        ∂(sphereLocalCountingProbability d N (sphericalRadius d N) x).toMeasure) ≤ C := by
  have hR : Tendsto (fun N : ℕ => Real.pi * sphericalRadius d N / 2) atTop atTop :=
    (Filter.Tendsto.const_mul_atTop Real.pi_pos
      (sphericalRadius_tendsto_atTop d (by omega))).atTop_div_const (by norm_num)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
    ((eventually_gt_atTop (0 : ℕ)).and (hR.eventually_gt_atTop T))
  refine ⟨(K : ℝ≥0∞) + ENNReal.ofReal (omega d * Problem1.capConstant d * T ^ d),
    ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.ofReal_ne_top⟩, ?_⟩
  intro N x
  by_cases hNK : K ≤ N
  · exact ((sphereLocalCountingProbability_mean d N (sphericalRadius d N) x _
      measurableSet_closedBall).trans_le
        (sphericalMeasure_normalBall_mul_le d N hd (hK N hNK).1 T hT
          (hK N hNK).2)).trans (le_add_of_nonneg_left zero_le)
  · exact ((sphereLocalCountingProbability_mean_le_count d N (sphericalRadius d N) x _
      measurableSet_closedBall).trans
        (show (N : ℝ≥0∞) ≤ (K : ℝ≥0∞) from Nat.cast_le.mpr (not_le.mp hNK).le)).trans
      (le_add_of_nonneg_right zero_le)

/-- Uniform compact-cutoff first moments on the actual spherical counting laws. -/
theorem exists_sphereLocalCountingProbability_cutoff_moment_bounds
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℕ → ℝ≥0∞, (∀ j, C j ≠ ∞) ∧
      ∀ (N : ℕ) (x : Fin N → Sphere d) (j : ℕ),
        (∫⁻ μ, ENNReal.ofReal (∫ y, countingMassCutoff d j y ∂μ.val)
          ∂(sphereLocalCountingProbability d N (sphericalRadius d N) x).toMeasure) ≤ C j := by
  have hsingle (j : ℕ) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (N : ℕ) (x : Fin N → Sphere d),
        (∫⁻ μ, ENNReal.ofReal (∫ y, countingMassCutoff d j y ∂μ.val)
          ∂(sphereLocalCountingProbability d N (sphericalRadius d N) x).toMeasure) ≤ C := by
    obtain ⟨R, hR⟩ := (countingMassCutoff d j).hasCompactSupport.isBounded.exists_norm_le
    obtain ⟨k, hk⟩ := exists_nat_ge (max 1 R)
    have hf : tsupport (countingMassCutoff d j) ⊆
        Metric.closedBall (0 : Rd d) (k : ℝ) :=
      fun y hy => by simpa only [Metric.mem_closedBall, dist_zero_right] using
        (hR y hy).trans ((le_max_right 1 R).trans hk)
    obtain ⟨C, hC, hmom⟩ := exists_sphereLocalCountingProbability_ball_mean_bound d hd
      (k : ℝ) (lt_of_lt_of_le zero_lt_one ((le_max_left 1 R).trans hk))
    refine ⟨ENNReal.ofReal ‖(countingMassCutoff d j).toBoundedContinuousFunction‖ * C,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC, fun N x => ?_⟩
    exact (lintegral_mono (fun μ => countingIntegral_ofReal_le_ball d k μ
      (countingMassCutoff d j) hf)).trans
      ((lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans_le
        (mul_le_mul_right (hmom N x)
          (ENNReal.ofReal ‖(countingMassCutoff d j).toBoundedContinuousFunction‖)))
  choose C hC hmom using hsingle
  exact ⟨C, hC, fun N x j => hmom j N x⟩

/-- Every sequence of the actual spherical local laws has a weakly convergent subsequence. -/
theorem exists_sphereLocalCountingProbability_tendsto_subseq
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (x : ∀ n, Fin (N n) → Sphere d) :
    ∃ (Q : ProbabilityMeasure (CountingConfiguration d)) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto
        ((fun n => sphereLocalCountingProbability d (N n) (sphericalRadius d (N n)) (x n)) ∘ φ)
        atTop (𝓝 Q) := by
  exact (exists_sphereLocalCountingProbability_cutoff_moment_bounds d hd).elim
    (fun C hC => exists_tendsto_subseq_of_countingMassCutoff_lintegral_le d
      (fun n => sphereLocalCountingProbability d (N n) (sphericalRadius d (N n)) (x n))
      C hC.1 (fun n j => hC.2 (N n) (x n) j))

end Riesz.Asymptotics
