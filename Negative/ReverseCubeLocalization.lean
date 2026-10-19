import Riesz.Negative.RandomRepairedInput
import Riesz.Configuration.LocalSimplicity

/-!
# Concrete repaired inputs for the reverse cube comparison

The cutoff density is clipped only to define a finite positive measure on every
ambient input. On the good event the clipping is inactive. This module does not
import the inactive `RepairedDiffuseInput` draft.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

/-- The cutoff point mass, extended to arbitrary ambient input measures. -/
def cubeCutoffMass (d m : ℕ) (χ : Rd d → ℝ) (μ : Measure (Rd d)) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (χ x) ∂μ.restrict (cube d (m : ℝ))).toReal

/-- The cutoff discrepancy on finite simple cube restrictions. -/
def cubeCutoffDiscrepancy (d m : ℕ) (χ : Rd d → ℝ) (μ : Measure (Rd d)) : ℝ :=
  cubeCutoffMass d m χ μ - ∫ x in cube d (m : ℝ), χ x ∂volume

/-- The good event before discretizing the repaired cube input. -/
def cubeRepairGoodEvent (d m : ℕ) (χ : Rd d → ℝ) (δ H : ℝ) :
    Set (Measure (Rd d)) :=
  {μ | |cubeCutoffDiscrepancy d m χ μ| ≤ δ * (m : ℝ) ^ d / (2 * H)}

/-- The unmodified diffuse density on the good event. -/
def cubeRepairRawDensity (d m : ℕ) (χ h : Rd d → ℝ)
    (μ : Measure (Rd d)) (x : Rd d) : ℝ :=
  1 - χ x - cubeCutoffDiscrepancy d m χ μ * h x

/-- A globally bounded extension of the repaired diffuse density. -/
def cubeRepairDensity (d m : ℕ) (χ h : Rd d → ℝ)
    (μ : Measure (Rd d)) (x : Rd d) : ℝ≥0∞ :=
  min 2 (ENNReal.ofReal (cubeRepairRawDensity d m χ h μ x))

/-- The positive diffuse measure defined for every ambient input. -/
def cubeRepairedDiffuseMeasure (d m : ℕ) (χ h : Rd d → ℝ)
    (μ : Measure (Rd d)) : Measure (Rd d) :=
  (volume.restrict (cube d (m : ℝ))).withDensity (cubeRepairDensity d m χ h μ)

/-- Cutoff hypotheses scaled to the cube of side `m`. -/
structure CubeRepairInputHypotheses (d m : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ) : Prop where
  side_pos : 0 < m
  cutoff_measurable : Measurable χ
  correction_measurable : Measurable h
  slack_pos : 0 < δ
  slack_lt_one : δ < 1
  correction_bound_pos : 0 < H
  cutoff_bounds : ∀ x ∈ cube d (m : ℝ), 0 ≤ χ x ∧ χ x ≤ 1 - δ
  correction_bounds : ∀ x ∈ cube d (m : ℝ),
    0 ≤ h x ∧ h x ≤ H / (m : ℝ) ^ d
  correction_integral : (∫ x in cube d (m : ℝ), h x ∂volume) = 1

theorem measurable_cubeCutoffDiscrepancy (d m : ℕ) (χ : Rd d → ℝ)
    (hχ : Measurable χ) : Measurable (cubeCutoffDiscrepancy d m χ) := by
  exact (ENNReal.measurable_toReal.comp
    ((Measure.measurable_lintegral hχ.ennreal_ofReal).comp
      (Riesz.Configuration.measurable_restrict d _ (measurableSet_cube d _)))).sub
        measurable_const

theorem measurableSet_cubeRepairGoodEvent (d m : ℕ) (χ : Rd d → ℝ)
    (hχ : Measurable χ) (δ H : ℝ) :
    MeasurableSet (cubeRepairGoodEvent d m χ δ H) := by
  simpa only [cubeRepairGoodEvent, Real.norm_eq_abs] using
    measurableSet_le (measurable_cubeCutoffDiscrepancy d m χ hχ).norm measurable_const

theorem cubeRepairedDiffuseMeasure_le (d m : ℕ) (χ h : Rd d → ℝ)
    (μ : Measure (Rd d)) :
    cubeRepairedDiffuseMeasure d m χ h μ ≤
      (2 : ℝ≥0∞) • volume.restrict (cube d (m : ℝ)) := by
  simpa only [cubeRepairedDiffuseMeasure, withDensity_const] using
    (withDensity_mono
      (μ := (volume : Measure (Rd d)).restrict (cube d (m : ℝ)))
      (f := cubeRepairDensity d m χ h μ) (g := fun _ => 2)
      (Filter.Eventually.of_forall (fun x => min_le_left 2
        (ENNReal.ofReal (cubeRepairRawDensity d m χ h μ x)))))

theorem cubeRepairedDiffuseMeasure_isFiniteMeasure (d m : ℕ) (χ h : Rd d → ℝ)
    (μ : Measure (Rd d)) :
    IsFiniteMeasure (cubeRepairedDiffuseMeasure d m χ h μ) := by
  letI := cube_background_isFiniteMeasure d m
  exact isFiniteMeasure_of_le ((2 : NNReal) • volume.restrict (cube d (m : ℝ)))
    (cubeRepairedDiffuseMeasure_le d m χ h μ)

def cubeRepairedDiffuse (d m : ℕ) (χ h : Rd d → ℝ)
    (μ : Measure (Rd d)) : FiniteMeasure (Rd d) :=
  ⟨cubeRepairedDiffuseMeasure d m χ h μ,
    cubeRepairedDiffuseMeasure_isFiniteMeasure d m χ h μ⟩

theorem measurable_cubeRepairedDiffuse (d m : ℕ) (χ h : Rd d → ℝ)
    (hχ : Measurable χ) (hh : Measurable h) :
    Measurable (cubeRepairedDiffuse d m χ h) := by
  letI := cube_background_isFiniteMeasure d m
  refine Measurable.subtype_mk ?_
  exact measurable_withDensity
    (measurable_const.min (((measurable_const.sub (hχ.comp measurable_snd)).sub
      (((measurable_cubeCutoffDiscrepancy d m χ hχ).comp measurable_fst).mul
        (hh.comp measurable_snd))).ennreal_ofReal))

theorem cubeRepairRawDensity_bounds (d m : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H) (μ : Measure (Rd d))
    (hgood : μ ∈ cubeRepairGoodEvent d m χ δ H) :
    ∀ x ∈ cube d (m : ℝ),
      δ / 2 ≤ cubeRepairRawDensity d m χ h μ x ∧
        cubeRepairRawDensity d m χ h μ x ≤ 2 := by
  intro x hx
  have hV : 0 < (m : ℝ) ^ d := pow_pos (Nat.cast_pos.mpr hinput.side_pos) d
  have hcancel : (δ * (m : ℝ) ^ d / (2 * H)) * (H / (m : ℝ) ^ d) = δ / 2 := by
    field_simp [hV.ne', hinput.correction_bound_pos.ne']
  have herr : |cubeCutoffDiscrepancy d m χ μ| * h x ≤ δ / 2 :=
    (mul_le_mul hgood (hinput.correction_bounds x hx).2
      (hinput.correction_bounds x hx).1
      (div_nonneg (mul_nonneg hinput.slack_pos.le hV.le)
        (mul_nonneg (by norm_num) hinput.correction_bound_pos.le))).trans_eq hcancel
  have hlo := mul_le_mul_of_nonneg_right
    (neg_abs_le (cubeCutoffDiscrepancy d m χ μ)) (hinput.correction_bounds x hx).1
  have hhi := mul_le_mul_of_nonneg_right
    (le_abs_self (cubeCutoffDiscrepancy d m χ μ)) (hinput.correction_bounds x hx).1
  dsimp only [cubeRepairRawDensity]
  constructor
  · nlinarith [(hinput.cutoff_bounds x hx).2]
  · nlinarith [(hinput.cutoff_bounds x hx).1, hinput.slack_lt_one]

theorem cubeRepairedDiffuse_eq_on_good (d m : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H) (μ : Measure (Rd d))
    (hgood : μ ∈ cubeRepairGoodEvent d m χ δ H) :
    (cubeRepairedDiffuse d m χ h μ : Measure (Rd d)) =
      (volume.restrict (cube d (m : ℝ))).withDensity
        (fun x => ENNReal.ofReal (cubeRepairRawDensity d m χ h μ x)) := by
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_cube d (m : ℝ))] with x hx
  exact min_eq_right (by simpa using (ENNReal.ofReal_le_ofReal
    (cubeRepairRawDensity_bounds d m χ h δ H hinput μ hgood x hx).2))

theorem cubeRepairedDiffuse_lower_on_good (d m : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H) (μ : Measure (Rd d))
    (hgood : μ ∈ cubeRepairGoodEvent d m χ δ H) :
    ENNReal.ofReal (δ / 2) • volume.restrict (cube d (m : ℝ)) ≤
      (cubeRepairedDiffuse d m χ h μ : Measure (Rd d)) := by
  rw [cubeRepairedDiffuse_eq_on_good d m χ h δ H hinput μ hgood,
    ← withDensity_const]
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem (measurableSet_cube d (m : ℝ))] with x hx
  exact ENNReal.ofReal_le_ofReal
    (cubeRepairRawDensity_bounds d m χ h δ H hinput μ hgood x hx).1

private theorem integrableOn_cube_of_nonneg_le (d m : ℕ) (f : Rd d → ℝ)
    (hf : Measurable f) (C : ℝ)
    (hbound : ∀ x ∈ cube d (m : ℝ), 0 ≤ f x ∧ f x ≤ C) :
    IntegrableOn f (cube d (m : ℝ)) volume := by
  letI := cube_background_isFiniteMeasure d m
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_cube d (m : ℝ))] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound x hx).1] using (hbound x hx).2

theorem cubeRepairedDiffuse_mass_on_good (d m : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H) (μ : Measure (Rd d))
    (hgood : μ ∈ cubeRepairGoodEvent d m χ δ H) :
    ((cubeRepairedDiffuse d m χ h μ).mass : ℝ) =
      (m : ℝ) ^ d - (∫ x in cube d (m : ℝ), χ x ∂volume) -
        cubeCutoffDiscrepancy d m χ μ := by
  letI := cube_background_isFiniteMeasure d m
  have hχi := integrableOn_cube_of_nonneg_le d m χ hinput.cutoff_measurable
    (1 - δ) hinput.cutoff_bounds
  have hhi := integrableOn_cube_of_nonneg_le d m h hinput.correction_measurable
    (H / (m : ℝ) ^ d) hinput.correction_bounds
  have hrawmeas : Measurable (cubeRepairRawDensity d m χ h μ) :=
    (measurable_const.sub hinput.cutoff_measurable).sub
      (measurable_const.mul hinput.correction_measurable)
  have hrawnonneg : 0 ≤ᵐ[volume.restrict (cube d (m : ℝ))]
      cubeRepairRawDensity d m χ h μ := by
    filter_upwards [ae_restrict_mem (measurableSet_cube d (m : ℝ))] with x hx
    exact (half_pos hinput.slack_pos).le.trans
      (cubeRepairRawDensity_bounds d m χ h δ H hinput μ hgood x hx).1
  change ((cubeRepairedDiffuse d m χ h μ : Measure (Rd d)) Set.univ).toReal = _
  rw [cubeRepairedDiffuse_eq_on_good d m χ h δ H hinput μ hgood,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← integral_eq_lintegral_of_nonneg_ae hrawnonneg hrawmeas.aestronglyMeasurable]
  simp only [cubeRepairRawDensity]
  rw [integral_sub (f := fun x => 1 - χ x)
    (g := fun x => cubeCutoffDiscrepancy d m χ μ * h x)
    ((integrable_const (1 : ℝ)).sub hχi)
    (hhi.const_mul (cubeCutoffDiscrepancy d m χ μ))]
  rw [integral_sub (f := fun _ => (1 : ℝ)) (g := χ) (integrable_const _) hχi,
    integral_const_mul, hinput.correction_integral, mul_one, integral_const]
  simp [measureReal_def, volume_cube]

theorem cubeRepairedDiffuse_on_good (d m : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H) (μ : Measure (Rd d))
    (hgood : μ ∈ cubeRepairGoodEvent d m χ δ H) :
    (cubeRepairedDiffuse d m χ h μ : Measure (Rd d)) =
        (volume.restrict (cube d (m : ℝ))).withDensity
          (fun x => ENNReal.ofReal (cubeRepairRawDensity d m χ h μ x)) ∧
      ENNReal.ofReal (δ / 2) • volume.restrict (cube d (m : ℝ)) ≤
        (cubeRepairedDiffuse d m χ h μ : Measure (Rd d)) ∧
      ((cubeRepairedDiffuse d m χ h μ).mass : ℝ) =
        (m : ℝ) ^ d - (∫ x in cube d (m : ℝ), χ x ∂volume) -
          cubeCutoffDiscrepancy d m χ μ :=
  ⟨cubeRepairedDiffuse_eq_on_good d m χ h δ H hinput μ hgood,
    cubeRepairedDiffuse_lower_on_good d m χ h δ H hinput μ hgood,
    cubeRepairedDiffuse_mass_on_good d m χ h δ H hinput μ hgood⟩

private theorem tupleCounting_withDensity (d a : ℕ) (x : Fin a → Rd d) (χ : Rd d → ℝ) :
    (tupleCounting d a x).withDensity (fun y => ENNReal.ofReal (χ y)) =
      weightedAtomicMeasure d a x (fun i => χ (x i)) := by
  ext D hD
  rw [withDensity_apply _ hD, ← lintegral_indicator hD]
  simp only [tupleCounting, weightedAtomicMeasure, lintegral_finsetSum_measure,
    lintegral_dirac, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hD]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hi : x i ∈ D
  · simp [hi]
  · simp [hi]

theorem cubeRepairedDiffuse_labeled_inputs (d m a : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H) (μ : Measure (Rd d))
    (hgood : μ ∈ cubeRepairGoodEvent d m χ δ H) (x : Fin a → Rd d)
    (hlabels : tupleCounting d a x = μ.restrict (cube d (m : ℝ))) :
    (∀ i, x i ∈ cube d (m : ℝ)) ∧
      (∀ i, 0 ≤ χ (x i) ∧ χ (x i) ≤ 1) ∧
      (μ.restrict (cube d (m : ℝ))).withDensity (fun y => ENNReal.ofReal (χ y)) =
        weightedAtomicMeasure d a x (fun i => χ (x i)) ∧
      (∑ i, χ (x i)) + ((cubeRepairedDiffuse d m χ h μ).mass : ℝ) = (m ^ d : ℕ) := by
  have hx : ∀ i, x i ∈ cube d (m : ℝ) := by
    apply (tupleCounting_compl_eq_zero_iff d a x _ (measurableSet_cube d (m : ℝ))).mp
    simp [hlabels, Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl]
  have hw : ∀ i, 0 ≤ χ (x i) ∧ χ (x i) ≤ 1 := fun i =>
    ⟨(hinput.cutoff_bounds (x i) (hx i)).1,
      (hinput.cutoff_bounds (x i) (hx i)).2.trans (by linarith [hinput.slack_pos])⟩
  refine ⟨hx, hw, hlabels ▸ tupleCounting_withDensity d a x χ, ?_⟩
  have hcut : cubeCutoffMass d m χ μ = ∑ i, χ (x i) := by
    simp [cubeCutoffMass, ← hlabels, tupleCounting, lintegral_finsetSum_measure,
      ENNReal.toReal_sum, fun i => (hw i).1]
  rw [cubeRepairedDiffuse_mass_on_good d m χ h δ H hinput μ hgood,
    cubeCutoffDiscrepancy, hcut, Nat.cast_pow]
  ring

theorem randomRepairedHalfUnitBranch_cube_input (d m a k : ℕ) (hd : 2 ≤ d)
    (r : ℝ) (hr : 0 < r) (hsize : (m : ℝ) = (2 : ℝ) ^ k * r)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H) (μ : Measure (Rd d))
    (hgood : μ ∈ cubeRepairGoodEvent d m χ δ H) (x : Fin a → Rd d)
    (hinj : Function.Injective x)
    (hlabels : tupleCounting d a x = μ.restrict (cube d (m : ℝ))) :
    (∀ᵐ p ∂randomRepairedInputMarks (halfUnitDiffuseCount d m),
      (IsSimpleConfiguration d
        (randomRepairedHalfUnitBranch d a m k r x (fun i => χ (x i))
          (cubeRepairedDiffuse d m χ h μ) p) ∧
        randomRepairedHalfUnitBranch d a m k r x (fun i => χ (x i))
          (cubeRepairedDiffuse d m χ h μ) p Set.univ = (m ^ d : ℕ)) ∧
      randomRepairedHalfUnitBranch d a m k r x (fun i => χ (x i))
        (cubeRepairedDiffuse d m χ h μ) p (cube d (m : ℝ))ᶜ = 0) ∧
      (∀ D : Set (Rd d), MeasurableSet D →
        (∫⁻ p, randomRepairedHalfUnitBranch d a m k r x (fun i => χ (x i))
          (cubeRepairedDiffuse d m χ h μ) p D
          ∂randomRepairedInputMarks (halfUnitDiffuseCount d m)) =
          ((μ.restrict (cube d (m : ℝ))).withDensity
            (fun y => ENNReal.ofReal (χ y)) +
            (cubeRepairedDiffuse d m χ h μ : Measure (Rd d))) D) := by
  obtain ⟨hx, hw, hweighted, hmass⟩ :=
    cubeRepairedDiffuse_labeled_inputs d m a χ h δ H hinput μ hgood x hlabels
  refine ⟨randomRepairedHalfUnitBranch_spec d a m k hd r hr hsize x hinj hx
    (fun i => χ (x i)) hw (cubeRepairedDiffuse d m χ h μ) (ENNReal.ofReal (δ / 2))
    (ENNReal.ofReal_pos.mpr (half_pos hinput.slack_pos))
    (cubeRepairedDiffuse_lower_on_good d m χ h δ H hinput μ hgood)
    (cubeRepairedDiffuseMeasure_le d m χ h μ) (m ^ d) hmass, ?_⟩
  intro D hD
  simpa only [hweighted] using randomRepairedHalfUnitBranch_full_mean d a m k hd r x
    (fun i => χ (x i)) hw (cubeRepairedDiffuse d m χ h μ)
    (cubeRepairedDiffuseMeasure_le d m χ h μ) D hD

theorem randomRepairedHalfUnitBranch_expected_error_le (d m a k : ℕ) (hd : 2 ≤ d)
    (r q : ℝ) (hr : 1 ≤ r) (hq : 0 < q) (hq_two : q < 2)
    (hsize : (m : ℝ) = (2 : ℝ) ^ k * r)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H) (μ : Measure (Rd d))
    (hgood : μ ∈ cubeRepairGoodEvent d m χ δ H) (x : Fin a → Rd d)
    (hinj : Function.Injective x)
    (hlabels : tupleCounting d a x = μ.restrict (cube d (m : ℝ))) :
    let ν := cubeRepairedDiffuse d m χ h μ
    let νs := halfUnitDiffuseMeasures d m ν
    let f := fun p : (Fin (halfUnitDiffuseCount d m) → unitInterval) ×
        (Fin (a + halfUnitDiffuseCount d m) → ℝ) =>
      Riesz.Analysis.signedDiscrepancyEnergy q
        (sampledRoundingDiscrepancy d a (halfUnitDiffuseCount d m) x
          (fun i => χ (x i)) νs p.1 p.2)
    let state := randomRepairedInputState d a (halfUnitDiffuseCount d m) k r x
      (fun i => χ (x i)) νs
    Integrable (f ∘ state) (randomRepairedInputMarks (halfUnitDiffuseCount d m)) ∧
      (∫ p, f (state p) ∂randomRepairedInputMarks (halfUnitDiffuseCount d m)) ≤
        (8 * (Real.sqrt d * (1 / 2)) ^ q / q + 2 * cubeRoundingConstant d q) *
          (r ^ q * (totalFractionalBudget (fun i => χ (x i)) + (ν.mass : ℝ)) +
            (m : ℝ) ^ d * r ^ (q - (d : ℝ))) := by
  dsimp only
  obtain ⟨hx, hw, _, hmass⟩ :=
    cubeRepairedDiffuse_labeled_inputs d m a χ h δ H hinput μ hgood x hlabels
  have hinputs := halfUnitDiffuseMeasures_sampling_inputs d m hd
    (cubeRepairedDiffuse d m χ h μ) (ENNReal.ofReal (δ / 2))
    (ENNReal.ofReal_pos.mpr (half_pos hinput.slack_pos))
    (cubeRepairedDiffuse_lower_on_good d m χ h δ H hinput μ hgood)
    (cubeRepairedDiffuseMeasure_le d m χ h μ)
  have hmasss : (∑ i, χ (x i)) +
      ∑ i, ((halfUnitDiffuseMeasures d m (cubeRepairedDiffuse d m χ h μ) i).mass : ℝ) =
      (m ^ d : ℕ) := by
    simpa only [halfUnitDiffuseMeasures_mass_sum d m (cubeRepairedDiffuse d m χ h μ)
      (cubeRepairedDiffuseMeasure_le d m χ h μ)] using hmass
  have hqd : q < (d : ℝ) := hq_two.trans_le (by exact_mod_cast hd)
  obtain ⟨hν, hνmass, hνatom, hνsupport, hνdisjoint, hνcube, hνdiam⟩ := hinputs
  have hb := sampledRoundingDiscrepancy_expected_energy_le_mass d a
    (halfUnitDiffuseCount d m) k r q (Real.sqrt d * (1 / 2)) hr hq hq_two hqd
    (by positivity) x hinj (by simpa only [← hsize] using hx)
    (fun i => χ (x i)) hw (halfUnitDiffuseMeasures d m (cubeRepairedDiffuse d m χ h μ))
    hν hνmass hνatom (halfUnitDiffuseRegions d m) hνsupport hνdisjoint
    (by simpa only [← hsize] using hνcube) hνdiam (m ^ d) hmasss
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp (cube_isBounded d (m : ℝ)).closure
  have hi := sampledRoundingDiscrepancy_marks_integrable d a (halfUnitDiffuseCount d m)
    k r q L (zero_lt_one.trans_le hr) hq hq_two x hinj
    (by simpa only [← hsize] using hx) (fun i => χ (x i)) hw
    (halfUnitDiffuseMeasures d m (cubeRepairedDiffuse d m χ h μ))
    hν hνmass hνatom (halfUnitDiffuseRegions d m) hνsupport hνdisjoint
    (by simpa only [← hsize] using hνcube) (m ^ d) hmasss
    (closure (cube d (m : ℝ))) isClosed_closure.measurableSet
    (by simpa only [← hsize] using (subset_closure : cube d (m : ℝ) ⊆ _))
    (fun y hy z hz => by simpa only [dist_eq_norm] using hL hy hz)
  have hmap : MeasurePreserving
      (randomRepairedInputState d a (halfUnitDiffuseCount d m) k r x (fun i => χ (x i))
        (halfUnitDiffuseMeasures d m (cubeRepairedDiffuse d m χ h μ)))
      (randomRepairedInputMarks (halfUnitDiffuseCount d m))
      (sampledRoundingMarks d a (halfUnitDiffuseCount d m) k r x (fun i => χ (x i))
        (halfUnitDiffuseMeasures d m (cubeRepairedDiffuse d m χ h μ))) :=
    ⟨measurable_randomRepairedInputState _ _ _ _ _ _ _ _,
      randomRepairedInputState_map _ _ _ _ _ _ _ _⟩
  refine ⟨hmap.integrable_comp_of_integrable hi, ?_⟩
  rw [← hmap.map_eq, integral_map hmap.measurable.aemeasurable
    (hmap.map_eq.symm ▸ hi.aestronglyMeasurable)] at hb
  simpa only [← hsize, halfUnitDiffuseMeasures_mass_sum d m
    (cubeRepairedDiffuse d m χ h μ) (cubeRepairedDiffuseMeasure_le d m χ h μ)] using hb

/-- The actual finite positive input used before sampling and rounding. -/
def cubeLabeledRepairedInput (d m a : ℕ) (χ h : Rd d → ℝ) (μ : Measure (Rd d))
    (x : Fin a → Rd d) : FiniteMeasure (Rd d) :=
  ⟨weightedAtomicMeasure d a x (fun i => χ (x i)) +
    (cubeRepairedDiffuse d m χ h μ : Measure (Rd d)), inferInstance⟩

theorem samplingRoundingInput_cubeRepaired (d m a : ℕ) (χ h : Rd d → ℝ)
    (μ : Measure (Rd d)) (x : Fin a → Rd d) :
    samplingRoundingInput d a (halfUnitDiffuseCount d m) x (fun i => χ (x i))
      (halfUnitDiffuseMeasures d m (cubeRepairedDiffuse d m χ h μ)) =
        (cubeLabeledRepairedInput d m a χ h μ x : Measure (Rd d)) := by
  exact congrArg (weightedAtomicMeasure d a x (fun i => χ (x i)) + ·)
    (halfUnitDiffuseMeasures_sum d m (cubeRepairedDiffuse d m χ h μ)
      (cubeRepairedDiffuseMeasure_le d m χ h μ))

/-- Fixed good inputs obey the physical centered cube-energy estimate.
The stationary localization limit and good-event gluing are separate targets. -/
theorem randomRepairedHalfUnitBranch_expected_D_q_le (d m a k : ℕ) (hd : 2 ≤ d)
    (r q τ : ℝ) (hr : 1 ≤ r) (hq : 0 < q) (hq_two : q < 2) (hτ : 0 < τ)
    (hsize : (m : ℝ) = (2 : ℝ) ^ k * r)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H) (μ : Measure (Rd d))
    (hgood : μ ∈ cubeRepairGoodEvent d m χ δ H) (x : Fin a → Rd d)
    (hinj : Function.Injective x)
    (hlabels : tupleCounting d a x = μ.restrict (cube d (m : ℝ))) :
    letI := cube_background_isFiniteMeasure d m
    let ν := cubeRepairedDiffuse d m χ h μ
    let I := cubeLabeledRepairedInput d m a χ h μ x
    let F := randomRepairedHalfUnitBranch d a m k r x (fun i => χ (x i)) ν
    Integrable (fun p => D_q d q m (F p))
      (randomRepairedInputMarks (halfUnitDiffuseCount d m)) ∧
      (∫ p, D_q d q m (F p) ∂randomRepairedInputMarks (halfUnitDiffuseCount d m)) ≤
        (1 + τ) * Riesz.Analysis.signedDiscrepancyEnergy q
          ((I : Measure (Rd d)).toSignedMeasure -
            (volume.restrict (cube d (m : ℝ))).toSignedMeasure) +
        (1 + τ⁻¹) * ((8 * (Real.sqrt d * (1 / 2)) ^ q / q +
          2 * cubeRoundingConstant d q) *
          (r ^ q * (totalFractionalBudget (fun i => χ (x i)) + (ν.mass : ℝ)) +
            (m : ℝ) ^ d * r ^ (q - (d : ℝ)))) := by
  letI := cube_background_isFiniteMeasure d m
  let ν := cubeRepairedDiffuse d m χ h μ
  let I := cubeLabeledRepairedInput d m a χ h μ x
  let F := randomRepairedHalfUnitBranch d a m k r x (fun i => χ (x i)) ν
  let ρ : Measure (Rd d) := volume.restrict (cube d (m : ℝ))
  have hbranch := randomRepairedHalfUnitBranch_cube_input d m a k hd r
    (zero_lt_one.trans_le hr) hsize χ h δ H hinput μ hgood x hinj hlabels
  obtain ⟨_, _, hweighted, _⟩ :=
    cubeRepairedDiffuse_labeled_inputs d m a χ h δ H hinput μ hgood x hlabels
  have hmean (D : Set (Rd d)) (hD : MeasurableSet D) :
      (∫⁻ p, F p D ∂randomRepairedInputMarks (halfUnitDiffuseCount d m)) =
        (I : Measure (Rd d)) D := by
    change (∫⁻ p, F p D ∂randomRepairedInputMarks (halfUnitDiffuseCount d m)) =
      (weightedAtomicMeasure d a x (fun i => χ (x i)) + (ν : Measure (Rd d))) D
    simpa only [F, ν, hweighted] using hbranch.2 D hD
  have hspec : ∀ᵐ p ∂randomRepairedInputMarks (halfUnitDiffuseCount d m),
      (IsSimpleConfiguration d (F p) ∧ F p Set.univ = (m ^ d : ℕ)) ∧
        F p (cube d (m : ℝ))ᶜ = 0 := hbranch.1
  clear hbranch hweighted
  have hImass : (I : Measure (Rd d)) Set.univ = (m ^ d : ℕ) := by
    rw [← hmean Set.univ MeasurableSet.univ,
      lintegral_congr_ae (hspec.mono (fun p hp => hp.1.2))]
    simp
  have hIsupport : (I : Measure (Rd d)) (cube d (m : ℝ))ᶜ = 0 := by
    rw [← hmean _ (measurableSet_cube d (m : ℝ)).compl,
      lintegral_congr_ae (hspec.mono (fun p hp => hp.2)), lintegral_zero]
  letI : ∀ p, IsFiniteMeasure (F p) := fun p =>
    inferInstanceAs (IsFiniteMeasure (weightedAtomicMeasure d (a + halfUnitDiffuseCount d m)
      (sampledAtomicSites d a (halfUnitDiffuseCount d m) x (halfUnitDiffuseMeasures d m ν) p.1)
      (randomRepairedInputState d a (halfUnitDiffuseCount d m) k r x
        (fun i => χ (x i)) (halfUnitDiffuseMeasures d m ν) p).2))
  letI : IsFiniteMeasure ρ := cube_background_isFiniteMeasure d m
  have hρmass : ρ Set.univ = (m ^ d : ℕ) := cube_background_mass d m
  have hρsupport : ρ (cube d (m : ℝ))ᶜ = 0 := by
    simp only [ρ, Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
      Set.compl_inter_self, measure_empty]
  let S := closure (cube d (m : ℝ))
  have hS : IsCompact S := (cube_isBounded d (m : ℝ)).isCompact_closure
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp hS.isBounded
  have hdiam : ∀ y ∈ S, ∀ z ∈ S, ‖y - z‖ ≤ L := fun y hy z hz => by
    simpa only [dist_eq_norm] using hL hy hz
  have hIS : (I : Measure (Rd d)) Sᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr subset_closure) hIsupport
  have hρS : ρ Sᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr subset_closure) hρsupport
  have hspecS : ∀ᵐ p ∂randomRepairedInputMarks (halfUnitDiffuseCount d m),
      F p Sᶜ = 0 ∧ F p Set.univ = (m ^ d : ℕ) := hspec.mono (fun p hp =>
        ⟨measure_mono_null (Set.compl_subset_compl.mpr subset_closure) hp.2, hp.1.2⟩)
  have hF : Measurable F := measurable_randomRepairedInputBranch d a
    (halfUnitDiffuseCount d m) k r x (fun i => χ (x i)) (halfUnitDiffuseMeasures d m ν)
  have htotal := finiteDifferenceDiscrepancy_integrable
    (randomRepairedInputMarks (halfUnitDiffuseCount d m)) d (m ^ d) q L hq hq_two
    F hF ρ hρmass S hS.measurableSet hρS hdiam hspecS
  have hphys : (fun p => D_q d q m (F p)) =ᵐ[
      randomRepairedInputMarks (halfUnitDiffuseCount d m)]
      (fun p => Riesz.Analysis.signedDiscrepancyEnergy q
        ((F p).toSignedMeasure - ρ.toSignedMeasure)) := by
    filter_upwards [hspecS] with p hp
    rw [Riesz.Analysis.D_q_eq_kernel_quadratic d m q L hq.le (F p)
      (Riesz.Analysis.ae_distance_le_of_concentrated (F p) (F p) S L hp.1 hp.1 hdiam)
      (Riesz.Analysis.ae_distance_le_of_concentrated (F p) ρ S L hp.1 hρS hdiam)
      (Riesz.Analysis.ae_distance_le_of_concentrated ρ ρ S L hρS hρS hdiam)]
    exact (Riesz.Analysis.signedDiscrepancyEnergy_sub_toSignedMeasure q L hq hq_two
      (F p) ρ (congrArg ENNReal.toReal (hp.2.trans hρmass.symm)) S hS.measurableSet
      hp.1 hρS hdiam).symm
  have herror := randomRepairedHalfUnitBranch_expected_error_le d m a k hd r q hr hq
    hq_two hsize χ h δ H hinput μ hgood x hinj hlabels
  simp only [sampledRoundingDiscrepancy, samplingRoundingInput_cubeRepaired] at herror
  let E := fun p => Riesz.Analysis.signedDiscrepancyEnergy q
    ((F p).toSignedMeasure - (I : Measure (Rd d)).toSignedMeasure)
  change Integrable E (randomRepairedInputMarks (halfUnitDiffuseCount d m)) ∧
    (∫ p, E p ∂randomRepairedInputMarks (halfUnitDiffuseCount d m)) ≤ _ at herror
  have hpoint : (fun p => Riesz.Analysis.signedDiscrepancyEnergy q
      ((F p).toSignedMeasure - ρ.toSignedMeasure)) ≤ᵐ[
      randomRepairedInputMarks (halfUnitDiffuseCount d m)]
      (fun p => (1 + τ) * Riesz.Analysis.signedDiscrepancyEnergy q
        ((I : Measure (Rd d)).toSignedMeasure - ρ.toSignedMeasure) + (1 + τ⁻¹) * E p) := by
    filter_upwards [hspecS] with p hp
    have hy := Riesz.Analysis.signedDiscrepancyEnergy_young q τ hq hq_two hτ
      ((I : Measure (Rd d)).toSignedMeasure - ρ.toSignedMeasure)
      ((F p).toSignedMeasure - (I : Measure (Rd d)).toSignedMeasure)
      (Riesz.Analysis.toSignedMeasure_sub_mass_zero (I : Measure (Rd d)) ρ
        (congrArg ENNReal.toReal (hImass.trans hρmass.symm)))
      (Riesz.Analysis.toSignedMeasure_sub_mass_zero (F p) (I : Measure (Rd d))
        (congrArg ENNReal.toReal (hp.2.trans hImass.symm))) S hS
      (Riesz.Analysis.toSignedMeasure_sub_concentrated (I : Measure (Rd d)) ρ S
        hS.measurableSet hIS hρS)
      (Riesz.Analysis.toSignedMeasure_sub_concentrated (F p) (I : Measure (Rd d)) S
        hS.measurableSet hp.1 hIS)
    have hsum : ((I : Measure (Rd d)).toSignedMeasure - ρ.toSignedMeasure) +
        ((F p).toSignedMeasure - (I : Measure (Rd d)).toSignedMeasure) =
        (F p).toSignedMeasure - ρ.toSignedMeasure := by abel
    simpa only [hsum, E] using hy
  have hb := integral_mono_ae htotal
    ((integrable_const ((1 + τ) * Riesz.Analysis.signedDiscrepancyEnergy q
      ((I : Measure (Rd d)).toSignedMeasure - ρ.toSignedMeasure))).add
        (herror.1.const_mul (1 + τ⁻¹))) hpoint
  simp only [Pi.add_apply] at hb
  rw [integral_add (f := fun _ => (1 + τ) * Riesz.Analysis.signedDiscrepancyEnergy q
      ((I : Measure (Rd d)).toSignedMeasure - ρ.toSignedMeasure))
    (g := fun p => (1 + τ⁻¹) * E p) (integrable_const _)
      (herror.1.const_mul (1 + τ⁻¹)), integral_const, integral_const_mul] at hb
  simp only [probReal_univ, one_smul] at hb
  refine ⟨htotal.congr hphys.symm, ?_⟩
  rw [integral_congr_ae hphys]
  exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left herror.2
    (le_of_lt (add_pos zero_lt_one (inv_pos.mpr hτ)))))

end Riesz.Negative
