import Riesz.Negative.ReverseCubeLocalization
import Riesz.Configuration.Compactness
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# The actual compact signed input of the reverse cube construction

All signed measures here come from finite cutoffs. The identities are
deterministic and conditional on the stated cube input and good event.
-/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Configuration
open scoped ENNReal Classical CompactlySupported

namespace Riesz.Negative

private theorem finiteDensity_toSignedMeasure
    (d : ℕ) (ρ ν : Measure (Rd d)) [IsFiniteMeasure ν]
    (f : Rd d → ℝ) (hf : Integrable f ρ)
    (hnonneg : 0 ≤ᵐ[ρ] f)
    (hν : ν = ρ.withDensity (fun x => ENNReal.ofReal (f x))) :
    ν.toSignedMeasure = ρ.withDensityᵥ f := by
  ext E hE
  rw [Measure.toSignedMeasure_apply_measurable hE, withDensityᵥ_apply hf hE]
  change (ν E).toReal = _
  rw [hν, withDensity_apply _ hE]
  exact (integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hnonneg)
    hf.1.restrict).symm

private theorem integrableOn_cube_of_nonneg_le (d m : ℕ) (f : Rd d → ℝ)
    (hf : Measurable f) (C : ℝ)
    (hbound : ∀ x ∈ cube d (m : ℝ), 0 ≤ f x ∧ f x ≤ C) :
    IntegrableOn f (cube d (m : ℝ)) volume := by
  letI := cube_background_isFiniteMeasure d m
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_cube d (m : ℝ))] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound x hx).1] using (hbound x hx).2

/-- On the good event, clipping leaves exactly the intended signed density. -/
theorem cubeRepairedDiffuse_toSignedMeasure_on_good
    (d m : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hi : CubeRepairInputHypotheses d m χ h δ H)
    (μ : Measure (Rd d)) (hg : μ ∈ cubeRepairGoodEvent d m χ δ H) :
    (cubeRepairedDiffuse d m χ h μ : Measure (Rd d)).toSignedMeasure =
      (volume.restrict (cube d (m : ℝ))).withDensityᵥ
        (cubeRepairRawDensity d m χ h μ) := by
  have hχi := integrableOn_cube_of_nonneg_le d m χ hi.cutoff_measurable
    (1 - δ) hi.cutoff_bounds
  have hhi := integrableOn_cube_of_nonneg_le d m h hi.correction_measurable
    (H / (m : ℝ) ^ d) hi.correction_bounds
  letI := cube_background_isFiniteMeasure d m
  refine finiteDensity_toSignedMeasure d _ _ _
    (((integrable_const (1 : ℝ)).sub hχi).sub
      (hhi.const_mul (cubeCutoffDiscrepancy d m χ μ))) ?_
    (cubeRepairedDiffuse_eq_on_good d m χ h δ H hi μ hg)
  filter_upwards [ae_restrict_mem (measurableSet_cube d (m : ℝ))] with x hx
  exact (half_pos hi.slack_pos).le.trans
    (cubeRepairRawDensity_bounds d m χ h δ H hi μ hg x hx).1

/-- The actual finite input has exactly the neutralized cutoff signed density.
No injectivity assumption on the finite atomic labels is needed here. -/
theorem cubeLabeledRepairedInput_signed_identity
    (d m a : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hi : CubeRepairInputHypotheses d m χ h δ H)
    (μ : Measure (Rd d)) (hg : μ ∈ cubeRepairGoodEvent d m χ δ H)
    (x : Fin a → Rd d) :
    letI := cube_background_isFiniteMeasure d m
    let ρ := volume.restrict (cube d (m : ℝ))
    (cubeLabeledRepairedInput d m a χ h μ x : Measure (Rd d)).toSignedMeasure -
        ρ.toSignedMeasure =
      (weightedAtomicMeasure d a x (fun i => χ (x i))).toSignedMeasure -
        ρ.withDensityᵥ χ - cubeCutoffDiscrepancy d m χ μ • ρ.withDensityᵥ h := by
  letI := cube_background_isFiniteMeasure d m
  have hχi := integrableOn_cube_of_nonneg_le d m χ hi.cutoff_measurable
    (1 - δ) hi.cutoff_bounds
  have hhi := integrableOn_cube_of_nonneg_le d m h hi.correction_measurable
    (H / (m : ℝ) ^ d) hi.correction_bounds
  have hone : (volume.restrict (cube d (m : ℝ))).withDensityᵥ
      (fun _ : Rd d => (1 : ℝ)) =
      (volume.restrict (cube d (m : ℝ))).toSignedMeasure :=
    (finiteDensity_toSignedMeasure d _ _ _ (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall (fun _ => zero_le_one)) (by simp)).symm
  change (weightedAtomicMeasure d a x (fun i => χ (x i)) +
      (cubeRepairedDiffuse d m χ h μ : Measure (Rd d))).toSignedMeasure - _ = _
  rw [Measure.toSignedMeasure_add,
    cubeRepairedDiffuse_toSignedMeasure_on_good d m χ h δ H hi μ hg]
  change (weightedAtomicMeasure d a x (fun i => χ (x i))).toSignedMeasure +
      (volume.restrict (cube d (m : ℝ))).withDensityᵥ
        ((fun _ : Rd d => (1 : ℝ)) - χ - cubeCutoffDiscrepancy d m χ μ • h) - _ = _
  rw [withDensityᵥ_sub ((integrable_const (1 : ℝ)).sub hχi)
      (hhi.smul (cubeCutoffDiscrepancy d m χ μ)),
    withDensityᵥ_sub (integrable_const (1 : ℝ)) hχi, withDensityᵥ_smul, hone]
  abel

/-- A supported integrable signed density is unchanged by restriction. -/
theorem withDensityVec_restrict_eq_of_support_subset
    (d : ℕ) (μ : Measure (Rd d)) (S : Set (Rd d)) (hS : MeasurableSet S)
    (f : Rd d → ℝ) (hf : Integrable f μ) (hsupport : Function.support f ⊆ S) :
    (μ.restrict S).withDensityᵥ f = μ.withDensityᵥ f := by
  ext E hE
  rw [withDensityᵥ_apply hf.restrict hE, withDensityᵥ_apply hf hE]
  rw [Measure.restrict_comm hE, ← integral_indicator hS]
  rw [Set.indicator_eq_self.mpr hsupport]

/-- A nonnegative compact cutoff has its usual signed vector density. -/
theorem cutoffMeasure_toSignedMeasure (d : ℕ) (μ : Measure (Rd d))
    [IsFiniteMeasureOnCompacts μ] (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) :
    (cutoffMeasure d μ χ : Measure (Rd d)).toSignedMeasure = μ.withDensityᵥ χ := by
  exact finiteDensity_toSignedMeasure d _ _ _ χ.integrable
    (Filter.Eventually.of_forall hχ) rfl

private theorem nonneg_of_support_subset (d : ℕ) (f : Rd d → ℝ)
    (S : Set (Rd d)) (hs : Function.support f ⊆ S)
    (hf : ∀ x ∈ S, 0 ≤ f x) : ∀ x, 0 ≤ f x := by
  intro x
  exact le_of_not_gt (fun hx => (not_le_of_gt hx) (hf x (hs (ne_of_lt hx))))

/-- The good-event cube input is exactly the finite compact neutralized input.
The ambient counting measure may be infinite and may have repeated sites. -/
theorem cubeLabeledRepairedInput_compact_signed_identity
    (d m a : ℕ) (χ h : C_c(Rd d, ℝ)) (δ H : ℝ)
    (hi : CubeRepairInputHypotheses d m χ h δ H)
    (hχsupp : tsupport χ ⊆ cube d (m : ℝ))
    (hhsupp : tsupport h ⊆ cube d (m : ℝ))
    (μ : CountingConfiguration d)
    (hg : μ.val ∈ cubeRepairGoodEvent d m χ δ H)
    (x : Fin a → Rd d) (hlabels : tupleCounting d a x = μ.val.restrict (cube d (m : ℝ))) :
    letI := cube_background_isFiniteMeasure d m
    (cubeLabeledRepairedInput d m a χ h μ.val x : Measure (Rd d)).toSignedMeasure -
        (volume.restrict (cube d (m : ℝ))).toSignedMeasure =
      (cutoffMeasure d μ.val χ : Measure (Rd d)).toSignedMeasure -
        (cutoffMeasure d volume χ : Measure (Rd d)).toSignedMeasure -
        cubeCutoffDiscrepancy d m χ μ.val •
          (cutoffMeasure d volume h : Measure (Rd d)).toSignedMeasure := by
  have hχs : Function.support (χ : Rd d → ℝ) ⊆ cube d (m : ℝ) :=
    (subset_tsupport χ).trans hχsupp
  have hhs : Function.support (h : Rd d → ℝ) ⊆ cube d (m : ℝ) :=
    (subset_tsupport h).trans hhsupp
  have hχ0 := nonneg_of_support_subset d χ _ hχs
    (fun y hy => (hi.cutoff_bounds y hy).1)
  have hh0 := nonneg_of_support_subset d h _ hhs
    (fun y hy => (hi.correction_bounds y hy).1)
  have hA : weightedAtomicMeasure d a x (fun i => χ (x i)) =
      (cutoffMeasure d μ.val χ : Measure (Rd d)) := by
    rw [← (cubeRepairedDiffuse_labeled_inputs d m a χ h δ H hi μ.val hg x hlabels).2.2.1,
      ← withDensity_indicator (measurableSet_cube d (m : ℝ))]
    change μ.val.withDensity _ = μ.val.withDensity (fun y => ENNReal.ofReal (χ y))
    congr 1
    exact Set.indicator_eq_self.mpr
      (fun y hy => hχs (fun h0 => hy (by simp [h0])))
  letI := cube_background_isFiniteMeasure d m
  rw [cubeLabeledRepairedInput_signed_identity d m a χ h δ H hi μ.val hg x,
    Measure.toSignedMeasure_congr hA,
    cutoffMeasure_toSignedMeasure d volume χ hχ0,
    cutoffMeasure_toSignedMeasure d volume h hh0]
  rw [withDensityVec_restrict_eq_of_support_subset d volume _
      (measurableSet_cube d (m : ℝ)) χ χ.integrable hχs,
    withDensityVec_restrict_eq_of_support_subset d volume _
      (measurableSet_cube d (m : ℝ)) h h.integrable hhs]

end Riesz.Negative
