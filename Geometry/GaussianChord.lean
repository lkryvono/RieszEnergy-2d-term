import Riesz.Geometry.TranslationRotations

/-! Compact Gaussian comparison in normal coordinates. The continuous centered
chart includes inverse radius zero, so compactness gives a multiplicative
Gaussian comparison without surface-area or derivative estimates.
-/

noncomputable section

open Filter Set RieszShowcase
open scoped Topology

namespace Riesz.Geometry

/-- The flat centered chart preserves squared Euclidean distance. -/
theorem normalCenteredVector_zero_sub_norm_sq (d : ℕ) (x y : Rd d) :
    ‖normalCenteredVector d 0 x - normalCenteredVector d 0 y‖ ^ 2 = ‖x - y‖ ^ 2 := by
  rw [normalCenteredVector_zero, normalCenteredVector_zero]
  have hsub : euclideanCons d 0 x - euclideanCons d 0 y = euclideanCons d 0 (x - y) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [euclideanCons]
  simp [hsub, euclideanCons_norm_sq]

/-- Exact chord rescaling, with no hemisphere or compact-support restriction. -/
theorem normalPoint_scaled_chord_sq (d : ℕ) {R : ℝ} (hR : R ≠ 0) (x y : Rd d) :
    R ^ 2 * chord d (normalPoint d R x) (normalPoint d R y) ^ 2 =
      ‖normalCenteredVector d R⁻¹ x - normalCenteredVector d R⁻¹ y‖ ^ 2 := by
  change R ^ 2 * ‖normalUnitVector d R⁻¹ x - normalUnitVector d R⁻¹ y‖ ^ 2 = _
  rw [normalUnitVector_eq_centered, normalUnitVector_eq_centered,
    add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

/-- The Gaussian ratio tends to one uniformly on each compact pair set. -/
theorem normalGaussianRatio_tendstoUniformlyOn (d : ℕ) (u : ℝ)
    {K : Set (Rd d)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun t p => Real.exp (u *
        (‖normalCenteredVector d t p.1 - normalCenteredVector d t p.2‖ ^ (2 : ℕ) -
          ‖p.1 - p.2‖ ^ (2 : ℕ))))
      (fun _ => 1) (𝓝 (0 : ℝ)) (K ×ˢ K) := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  letI : CompactSpace (K ×ˢ K) := isCompact_iff_compactSpace.mp (hK.prod hK)
  have hx := (normalCenteredVector_joint_continuous d).comp
      (show Continuous (fun p : ℝ × (K ×ˢ K) => (p.1, p.2.val.1)) by fun_prop)
  have hy := (normalCenteredVector_joint_continuous d).comp
      (show Continuous (fun p : ℝ × (K ×ˢ K) => (p.1, p.2.val.2)) by fun_prop)
  have hflat := (show Continuous (fun p : ℝ × (K ×ˢ K) =>
      p.2.val.1 - p.2.val.2) by fun_prop).norm.pow 2
  have hc := (((hx.sub hy).norm.pow 2).sub hflat).const_mul u |>.rexp
  have ht := Continuous.tendstoUniformly
    (fun t (p : K ×ˢ K) => Real.exp (u *
      (‖normalCenteredVector d t p.val.1 - normalCenteredVector d t p.val.2‖ ^ (2 : ℕ) -
        ‖p.val.1 - p.val.2‖ ^ (2 : ℕ)))) hc (0 : ℝ)
  simpa only [normalCenteredVector_zero_sub_norm_sq, sub_self, mul_zero,
    Real.exp_zero, Function.comp_def] using ht

/-- Compact Euclidean Gaussian tests are eventually bounded by spherical tests
with a multiplicative constant arbitrarily close to one. -/
theorem eventually_normalGaussian_le_sphericalGaussian (d : ℕ) (u T ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ x ∈ Metric.closedBall (0 : Rd d) T,
      ∀ y ∈ Metric.closedBall (0 : Rd d) T,
        Real.exp (-u * ‖x - y‖ ^ (2 : ℕ)) ≤
          (1 + ε) * Real.exp (-(u * R ^ (2 : ℕ)) *
            chord d (normalPoint d R x) (normalPoint d R y) ^ (2 : ℕ)) := by
  have hevent := (Metric.tendstoUniformlyOn_iff.mp
    (normalGaussianRatio_tendstoUniformlyOn d u (isCompact_closedBall (0 : Rd d) T))) ε hε
  filter_upwards [tendsto_inv_atTop_zero.eventually hevent, eventually_gt_atTop (0 : ℝ)]
    with R hratio hR
  intro x hx y hy
  have hdist := hratio (x, y) ⟨hx, hy⟩
  rw [Real.dist_eq, abs_sub_lt_iff] at hdist
  have hbound : Real.exp (u *
      (‖normalCenteredVector d R⁻¹ x - normalCenteredVector d R⁻¹ y‖ ^ (2 : ℕ) -
        ‖x - y‖ ^ (2 : ℕ))) ≤ 1 + ε := by linarith [hdist.2]
  calc
    Real.exp (-u * ‖x - y‖ ^ (2 : ℕ)) =
        Real.exp (u * (‖normalCenteredVector d R⁻¹ x -
          normalCenteredVector d R⁻¹ y‖ ^ (2 : ℕ) - ‖x - y‖ ^ (2 : ℕ))) *
        Real.exp (-u * ‖normalCenteredVector d R⁻¹ x -
          normalCenteredVector d R⁻¹ y‖ ^ (2 : ℕ)) := ?_
    _ ≤ (1 + ε) * Real.exp (-u * ‖normalCenteredVector d R⁻¹ x -
        normalCenteredVector d R⁻¹ y‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hbound (Real.exp_nonneg _)
    _ = _ := ?_
  · rw [← Real.exp_add]
    congr 1
    ring
  rw [← normalPoint_scaled_chord_sq d hR.ne' x y]
  congr 2
  ring

end Riesz.Geometry
