import Riesz.Configuration.Compactness
import Mathlib.Topology.Algebra.Module.Basic

/-! Compact containment for the existing vague counting-configuration topology. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Configuration

/-- The full compact-test image is closed, including integer multiplicities. -/
theorem isClosed_range_countingCompactTest (d : ℕ) :
    IsClosed (Set.range (countingCompactTest d)) := by
  apply isClosed_of_closure_subset
  intro y hy
  have hlin : y ∈ Set.range ((↑) : (C_c(Rd d, ℝ) →ₗ[ℝ] ℝ) → (C_c(Rd d, ℝ) → ℝ)) := by
    apply (LinearMap.isClosed_range_coe (C_c(Rd d, ℝ)) ℝ (RingHom.id ℝ)).closure_subset_iff.mpr ?_ hy
    rintro _ ⟨μ, rfl⟩
    exact ⟨(CompactlySupportedContinuousMap.integralPositiveLinearMap μ.val).toLinearMap, rfl⟩
  rcases hlin with ⟨L, rfl⟩
  have hpos : ∀ f : C_c(Rd d, ℝ), 0 ≤ f → 0 ≤ L f := by
    intro f hf
    apply (isClosed_le continuous_const (continuous_apply f)).closure_subset_iff.mpr ?_ hy
    rintro _ ⟨μ, rfl⟩
    exact (CompactlySupportedContinuousMap.integralPositiveLinearMap μ.val).map_nonneg hf
  let Λ := PositiveLinearMap.mk₀ L hpos
  let μ := RealRMK.rieszMeasure Λ
  let l := Filter.comap (countingCompactTest d) (𝓝 (⇑L))
  haveI : l.NeBot := Filter.comap_neBot_iff_frequently.mpr (mem_closure_iff_frequently.mp hy)
  have hint : ∀ f : C_c(Rd d, ℝ), ∫ x, f x ∂μ = L f :=
    fun f => RealRMK.integral_rieszMeasure Λ f
  have hcount : IsCountingConfiguration d μ := by
    apply isCountingConfiguration_of_tendsto_integral d id l μ
    intro f
    rw [hint f]
    exact ((continuous_apply f).tendsto (⇑L)).comp Filter.tendsto_comap
  exact ⟨⟨μ, hcount⟩, funext hint⟩

/-- Cutoff bounds uniformly bound every compact-test coordinate. -/
theorem exists_countingIntegral_bound (d : ℕ) (M : ℕ → ℝ) (f : C_c(Rd d, ℝ)) :
    ∃ C : ℝ, ∀ μ : CountingConfiguration d,
      (∀ j, ∫ x, countingMassCutoff d j x ∂μ.val ≤ M j) →
      |∫ x, f x ∂μ.val| ≤ C := by
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ) :=
    fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using (hR x hx).trans hn
  refine ⟨‖f.toBoundedContinuousFunction‖ * max 0 (M n), ?_⟩
  intro μ hμ
  have hbound : |∫ x, f x ∂μ.val| ≤
      ‖f.toBoundedContinuousFunction‖ * μ.val.real (Metric.closedBall (0 : Rd d) (n : ℝ)) := by
    simpa using countingIntegral_sub_le d n μ f 0 ‖f.toBoundedContinuousFunction‖ hf
      (by simp) (fun x => by simpa only [CompactlySupportedContinuousMap.zero_apply, sub_zero,
        Real.norm_eq_abs, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply]
        using f.toBoundedContinuousFunction.norm_coe_le_norm x)
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (((countingMass_le_cutoff d n μ (countingMassCutoff d n) (countingMassCutoff_spec d n).1
      (countingMassCutoff_spec d n).2).trans (hμ n)).trans (le_max_right 0 (M n)))
    (norm_nonneg _))

/-- Bounds on continuous compact mass cutoffs give compact sets in the existing vague topology. -/
theorem isCompact_countingMassCutoff_le (d : ℕ) (M : ℕ → ℝ) :
    IsCompact {μ : CountingConfiguration d |
      ∀ j, ∫ x, countingMassCutoff d j x ∂μ.val ≤ M j} := by
  choose C hC using exists_countingIntegral_bound d M
  apply (countingCompactTest_isEmbedding d).isCompact_iff.mpr
  have himage : countingCompactTest d ''
      {μ : CountingConfiguration d | ∀ j, ∫ x, countingMassCutoff d j x ∂μ.val ≤ M j} =
      Set.range (countingCompactTest d) ∩
        {z : C_c(Rd d, ℝ) → ℝ | ∀ j, z (countingMassCutoff d j) ≤ M j} := by
    ext z
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      exact ⟨Set.mem_range_self μ, hμ⟩
    · rintro ⟨⟨μ, rfl⟩, hμ⟩
      exact ⟨μ, hμ, rfl⟩
  have hclosed : IsClosed (countingCompactTest d ''
      {μ : CountingConfiguration d | ∀ j, ∫ x, countingMassCutoff d j x ∂μ.val ≤ M j}) := by
    rw [himage]
    exact (isClosed_range_countingCompactTest d).inter
      (by
        simpa only [Set.setOf_forall] using
          (isClosed_iInter (fun j => isClosed_le (continuous_apply (countingMassCutoff d j))
            (continuous_const (y := M j)))))
  apply (isCompact_pi_infinite (fun f => isCompact_Icc (a := -(C f)) (b := C f))).of_isClosed_subset hclosed
  rintro _ ⟨μ, hμ, rfl⟩ f
  exact abs_le.mp (hC f μ hμ)

end Riesz.Configuration
