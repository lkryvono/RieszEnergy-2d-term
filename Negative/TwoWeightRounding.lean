import Riesz.Analysis.NegativeGaussian

/-! The elementary two-weight random replacement in the paper's rounding lemma.
The finite iteration and its conditional-energy telescoping are separate steps. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

def roundingUp (u v : ℝ) : ℝ := min (1 - u) v

def roundingDown (u v : ℝ) : ℝ := min u (1 - v)

/-- The two possible transfers, with the paper's mean-preserving probabilities. -/
def twoWeightTransferLaw (u v : ℝ) : Measure ℝ :=
  ENNReal.ofReal (roundingDown u v / (roundingUp u v + roundingDown u v)) •
    Measure.dirac (roundingUp u v) +
  ENNReal.ofReal (roundingUp u v / (roundingUp u v + roundingDown u v)) •
    Measure.dirac (-roundingDown u v)

def fractionalBudget (u : ℝ) : ℝ := u * (1 - u)

def unitDipole (d : ℕ) (x y : Rd d) : SignedMeasure (Rd d) :=
  (Measure.dirac x).toSignedMeasure - (Measure.dirac y).toSignedMeasure

theorem measurable_roundingSteps :
    Measurable (fun p : ℝ × ℝ => roundingUp p.1 p.2) ∧
      Measurable (fun p : ℝ × ℝ => roundingDown p.1 p.2) := by
  exact ⟨(measurable_const.sub measurable_fst).min measurable_snd,
    measurable_fst.min (measurable_const.sub measurable_snd)⟩

/-- The law depends measurably on the input weights, including at their boundaries. -/
theorem measurable_twoWeightTransferLaw :
    Measurable (fun p : ℝ × ℝ => twoWeightTransferLaw p.1 p.2) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  simp only [twoWeightTransferLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact ((measurable_roundingSteps.2.div (measurable_roundingSteps.1.add
    measurable_roundingSteps.2)).ennreal_ofReal.mul
      ((Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp measurable_roundingSteps.1))).add
    ((measurable_roundingSteps.1.div (measurable_roundingSteps.1.add
      measurable_roundingSteps.2)).ennreal_ofReal.mul
        ((Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp measurable_roundingSteps.2.neg)))

theorem signedDiscrepancyEnergy_neg (d : ℕ) (q : ℝ) (η : SignedMeasure (Rd d)) :
    Riesz.Analysis.signedDiscrepancyEnergy q (-η) =
      Riesz.Analysis.signedDiscrepancyEnergy q η := by
  simp only [Riesz.Analysis.signedDiscrepancyEnergy, Riesz.Analysis.signedKernelQuadratic,
    SignedMeasure.toJordanDecomposition_neg, JordanDecomposition.neg_posPart,
    JordanDecomposition.neg_negPart]
  ring

theorem signedDiscrepancyEnergy_smul_nonneg (d : ℕ) (q t : ℝ) (ht : 0 ≤ t)
    (η : SignedMeasure (Rd d)) :
    Riesz.Analysis.signedDiscrepancyEnergy q (t • η) =
      t ^ 2 * Riesz.Analysis.signedDiscrepancyEnergy q η := by
  simp only [Riesz.Analysis.signedDiscrepancyEnergy, Riesz.Analysis.signedKernelQuadratic,
    SignedMeasure.toJordanDecomposition_smul_real,
    JordanDecomposition.real_smul_posPart_nonneg _ t ht,
    JordanDecomposition.real_smul_negPart_nonneg _ t ht]
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal t ht]
  ring

theorem signedDiscrepancyEnergy_smul (d : ℕ) (q t : ℝ) (η : SignedMeasure (Rd d)) :
    Riesz.Analysis.signedDiscrepancyEnergy q (t • η) =
      t ^ 2 * Riesz.Analysis.signedDiscrepancyEnergy q η := by
  by_cases ht : t < 0
  · rw [show t • η = -((-t) • η) by rw [neg_smul t η, neg_neg], signedDiscrepancyEnergy_neg,
      signedDiscrepancyEnergy_smul_nonneg d q (-t) (neg_nonneg.mpr ht.le), neg_sq]
  · exact signedDiscrepancyEnergy_smul_nonneg d q t (le_of_not_gt ht) η

theorem unitDipole_jordan_parts (d : ℕ) (x y : Rd d) (hxy : x ≠ y) :
    (unitDipole d x y).toJordanDecomposition.posPart = Measure.dirac x ∧
      (unitDipole d x y).toJordanDecomposition.negPart = Measure.dirac y := by
  let J : JordanDecomposition (Rd d) := ⟨Measure.dirac x, Measure.dirac y,
    ⟨{x}ᶜ, (measurableSet_singleton x).compl, by simp, by simp [Ne.symm hxy]⟩⟩
  exact ⟨congrArg JordanDecomposition.posPart
    (JordanDecomposition.toJordanDecomposition_toSignedMeasure J),
    congrArg JordanDecomposition.negPart
      (JordanDecomposition.toJordanDecomposition_toSignedMeasure J)⟩

theorem unitDipole_energy (d : ℕ) (q : ℝ) (hq : 0 < q) (x y : Rd d) (hxy : x ≠ y) :
    Riesz.Analysis.signedDiscrepancyEnergy q (unitDipole d x y) = 2 * ‖x - y‖ ^ q / q := by
  simp only [Riesz.Analysis.signedDiscrepancyEnergy, Riesz.Analysis.signedKernelQuadratic,
    (unitDipole_jordan_parts d x y hxy).1, (unitDipole_jordan_parts d x y hxy).2,
    Measure.dirac_prod_dirac, integral_dirac, sub_self, norm_zero, Real.zero_rpow hq.ne', norm_sub_rev]
  ring

theorem twoSiteIncrement_energy (d : ℕ) (q : ℝ) (hq : 0 < q) (t : ℝ)
    (x y : Rd d) (hxy : x ≠ y) :
    Riesz.Analysis.signedDiscrepancyEnergy q (t • unitDipole d x y) =
      2 * t ^ 2 * ‖x - y‖ ^ q / q := by
  rw [signedDiscrepancyEnergy_smul, unitDipole_energy d q hq x y hxy]
  ring

theorem unitDipole_mass_zero (d : ℕ) (x y : Rd d) :
    unitDipole d x y Set.univ = 0 := by
  simp [unitDipole, Measure.toSignedMeasure_sub_apply MeasurableSet.univ]

theorem roundingSteps_pos (u v : ℝ) (hu : 0 < u) (hu_one : u < 1)
    (hv : 0 < v) (hv_one : v < 1) :
    0 < roundingUp u v ∧ 0 < roundingDown u v := by
  exact ⟨lt_min (sub_pos.mpr hu_one) hv, lt_min hu (sub_pos.mpr hv_one)⟩

theorem twoWeightTransferLaw_isProbability (u v : ℝ) (hu : 0 < u) (hu_one : u < 1)
    (hv : 0 < v) (hv_one : v < 1) :
    IsProbabilityMeasure (twoWeightTransferLaw u v) := by
  refine ⟨?_⟩
  simp only [twoWeightTransferLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  have hpos := roundingSteps_pos u v hu hu_one hv hv_one
  rw [← ENNReal.ofReal_add (div_pos hpos.2 (add_pos hpos.1 hpos.2)).le
    (div_pos hpos.1 (add_pos hpos.1 hpos.2)).le, ← add_div,
    add_comm (roundingDown u v), div_self (add_pos hpos.1 hpos.2).ne', ENNReal.ofReal_one]

theorem roundingOutcome_valid (u v : ℝ) (hu : 0 ≤ u) (hu_one : u ≤ 1)
    (hv : 0 ≤ v) (hv_one : v ≤ 1) (t : ℝ)
    (ht : t = roundingUp u v ∨ t = -roundingDown u v) :
    0 ≤ u + t ∧ u + t ≤ 1 ∧ 0 ≤ v - t ∧ v - t ≤ 1 ∧
      (u + t = 0 ∨ u + t = 1 ∨ v - t = 0 ∨ v - t = 1) ∧
      (u + t) + (v - t) = u + v := by
  grind [roundingUp, roundingDown]

theorem twoWeightTransferLaw_support (u v : ℝ) (hu : 0 < u) (hu_one : u < 1)
    (hv : 0 < v) (hv_one : v < 1) :
    ∀ᵐ t ∂twoWeightTransferLaw u v,
      0 ≤ u + t ∧ u + t ≤ 1 ∧ 0 ≤ v - t ∧ v - t ≤ 1 ∧
        (u + t = 0 ∨ u + t = 1 ∨ v - t = 0 ∨ v - t = 1) ∧
        (u + t) + (v - t) = u + v := by
  unfold twoWeightTransferLaw
  exact ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure (by simpa only [ae_dirac_eq, Filter.eventually_pure] using
        (roundingOutcome_valid u v hu.le hu_one.le hv.le hv_one.le _ (Or.inl rfl))) _,
     Measure.ae_smul_measure (by simpa only [ae_dirac_eq, Filter.eventually_pure] using
        (roundingOutcome_valid u v hu.le hu_one.le hv.le hv_one.le _ (Or.inr rfl))) _⟩

theorem integrable_twoWeightTransferLaw (u v : ℝ) (f : ℝ → ℝ) :
    Integrable f (twoWeightTransferLaw u v) := by
  exact integrable_add_measure.mpr
    ⟨(integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top,
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top⟩

theorem integral_twoWeightTransferLaw (u v : ℝ) (hu : 0 < u) (hu_one : u < 1)
    (hv : 0 < v) (hv_one : v < 1) (f : ℝ → ℝ) :
    (∫ t, f t ∂twoWeightTransferLaw u v) =
      roundingDown u v / (roundingUp u v + roundingDown u v) * f (roundingUp u v) +
      roundingUp u v / (roundingUp u v + roundingDown u v) * f (-roundingDown u v) := by
  unfold twoWeightTransferLaw
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  have hpos := roundingSteps_pos u v hu hu_one hv hv_one
  rw [ENNReal.toReal_ofReal (div_pos hpos.2 (add_pos hpos.1 hpos.2)).le,
    ENNReal.toReal_ofReal (div_pos hpos.1 (add_pos hpos.1 hpos.2)).le, smul_eq_mul, smul_eq_mul]

theorem twoWeightTransferLaw_moments (u v : ℝ) (hu : 0 < u) (hu_one : u < 1)
    (hv : 0 < v) (hv_one : v < 1) :
    (∫ t, t ∂twoWeightTransferLaw u v) = 0 ∧
      (∫ t, t ^ 2 ∂twoWeightTransferLaw u v) = roundingUp u v * roundingDown u v := by
  rw [integral_twoWeightTransferLaw u v hu hu_one hv hv_one,
    integral_twoWeightTransferLaw u v hu hu_one hv hv_one]
  constructor <;> field_simp [(add_pos (roundingSteps_pos u v hu hu_one hv hv_one).1
    (roundingSteps_pos u v hu hu_one hv hv_one).2).ne']
  ring

theorem twoWeightTransferLaw_budget (u v : ℝ) (hu : 0 < u) (hu_one : u < 1)
    (hv : 0 < v) (hv_one : v < 1) :
    (∫ t, fractionalBudget (u + t) + fractionalBudget (v - t) ∂twoWeightTransferLaw u v) =
      fractionalBudget u + fractionalBudget v - 2 * roundingUp u v * roundingDown u v := by
  rw [integral_twoWeightTransferLaw u v hu hu_one hv hv_one]
  unfold fractionalBudget
  field_simp [(add_pos (roundingSteps_pos u v hu hu_one hv hv_one).1
    (roundingSteps_pos u v hu hu_one hv hv_one).2).ne']
  ring

theorem twoWeightTransferLaw_centered_test (u v : ℝ) (hu : 0 < u) (hu_one : u < 1)
    (hv : 0 < v) (hv_one : v < 1) (a b : ℝ) :
    (∫ t, t * (a - b) ∂twoWeightTransferLaw u v) = 0 := by
  rw [integral_mul_const, (twoWeightTransferLaw_moments u v hu hu_one hv hv_one).1, zero_mul]

theorem twoWeightTransferLaw_expected_energy (d : ℕ) (q : ℝ) (hq : 0 < q)
    (u v : ℝ) (hu : 0 < u) (hu_one : u < 1) (hv : 0 < v) (hv_one : v < 1)
    (x y : Rd d) (hxy : x ≠ y) :
    (∫ t, Riesz.Analysis.signedDiscrepancyEnergy q (t • unitDipole d x y)
      ∂twoWeightTransferLaw u v) = 2 * roundingUp u v * roundingDown u v * ‖x - y‖ ^ q / q := by
  simp_rw [twoSiteIncrement_energy d q hq _ x y hxy]
  rw [integral_div, integral_mul_const, integral_const_mul,
    (twoWeightTransferLaw_moments u v hu hu_one hv hv_one).2]
  ring

theorem twoWeightTransferLaw_energy_budget_bound (d : ℕ) (q D : ℝ) (hq : 0 < q)
    (u v : ℝ) (hu : 0 < u) (hu_one : u < 1) (hv : 0 < v) (hv_one : v < 1)
    (x y : Rd d) (hxy : x ≠ y) (hdiam : ‖x - y‖ ≤ D) :
    (∫ t, Riesz.Analysis.signedDiscrepancyEnergy q (t • unitDipole d x y)
      ∂twoWeightTransferLaw u v) ≤ D ^ q / q *
        (fractionalBudget u + fractionalBudget v -
          ∫ t, fractionalBudget (u + t) + fractionalBudget (v - t) ∂twoWeightTransferLaw u v) := by
  rw [twoWeightTransferLaw_expected_energy d q hq u v hu hu_one hv hv_one x y hxy,
    twoWeightTransferLaw_budget u v hu hu_one hv hv_one]
  have hpower := Real.rpow_le_rpow (norm_nonneg (x - y)) hdiam hq.le
  convert mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hq).mpr hpower)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (roundingSteps_pos u v hu hu_one hv hv_one).1.le)
      (roundingSteps_pos u v hu hu_one hv hv_one).2.le) using 1
  all_goals first | rfl | ring

/-- The replacement law preserves the mean and total weight, reaches an endpoint,
and pays for its variance by decreasing the fractional budget. -/
theorem two_weight_replacement (u v : ℝ) (hu : 0 < u) (hu_one : u < 1)
    (hv : 0 < v) (hv_one : v < 1) :
    ∃ P : Measure ℝ, IsProbabilityMeasure P ∧
      (∀ᵐ t ∂P, 0 ≤ u + t ∧ u + t ≤ 1 ∧ 0 ≤ v - t ∧ v - t ≤ 1 ∧
        (u + t = 0 ∨ u + t = 1 ∨ v - t = 0 ∨ v - t = 1) ∧
        (u + t) + (v - t) = u + v) ∧
      Integrable (fun t => t) P ∧ (∫ t, t ∂P) = 0 ∧
      Integrable (fun t => t ^ 2) P ∧
      (∫ t, t ^ 2 ∂P) = roundingUp u v * roundingDown u v ∧
      (∫ t, fractionalBudget (u + t) + fractionalBudget (v - t) ∂P) =
        fractionalBudget u + fractionalBudget v - 2 * roundingUp u v * roundingDown u v := by
  exact ⟨twoWeightTransferLaw u v, twoWeightTransferLaw_isProbability u v hu hu_one hv hv_one,
    twoWeightTransferLaw_support u v hu hu_one hv hv_one,
    integrable_twoWeightTransferLaw u v _, (twoWeightTransferLaw_moments u v hu hu_one hv hv_one).1,
    integrable_twoWeightTransferLaw u v _, (twoWeightTransferLaw_moments u v hu hu_one hv hv_one).2,
    twoWeightTransferLaw_budget u v hu hu_one hv hv_one⟩

theorem twoWeightTransferLaw_weight_means (u v : ℝ) (hu : 0 < u) (hu_one : u < 1)
    (hv : 0 < v) (hv_one : v < 1) :
    (∫ t, u + t ∂twoWeightTransferLaw u v) = u ∧
      (∫ t, v - t ∂twoWeightTransferLaw u v) = v := by
  rw [integral_twoWeightTransferLaw u v hu hu_one hv hv_one,
    integral_twoWeightTransferLaw u v hu hu_one hv hv_one]
  constructor <;> field_simp [(add_pos (roundingSteps_pos u v hu hu_one hv hv_one).1
    (roundingSteps_pos u v hu hu_one hv hv_one).2).ne']
  all_goals ring

theorem twoWeightTransferLaw_budget_strict (u v : ℝ) (hu : 0 < u) (hu_one : u < 1)
    (hv : 0 < v) (hv_one : v < 1) :
    (∫ t, fractionalBudget (u + t) + fractionalBudget (v - t) ∂twoWeightTransferLaw u v) <
      fractionalBudget u + fractionalBudget v := by
  rw [twoWeightTransferLaw_budget u v hu hu_one hv hv_one]
  exact sub_lt_self _ (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2)
    (roundingSteps_pos u v hu hu_one hv hv_one).1)
    (roundingSteps_pos u v hu hu_one hv hv_one).2)

/-- The complete single replacement, including its actual signed discrepancy cost.
The expected cost is charged to the fractional budget lost in this step. -/
theorem two_weight_rounding_step (d : ℕ) (q D : ℝ) (hq : 0 < q)
    (u v : ℝ) (hu : 0 < u) (hu_one : u < 1) (hv : 0 < v) (hv_one : v < 1)
    (x y : Rd d) (hxy : x ≠ y) (hdiam : ‖x - y‖ ≤ D) :
    ∃ P : Measure ℝ, IsProbabilityMeasure P ∧
      (∀ᵐ t ∂P, 0 ≤ u + t ∧ u + t ≤ 1 ∧ 0 ≤ v - t ∧ v - t ≤ 1 ∧
        (u + t = 0 ∨ u + t = 1 ∨ v - t = 0 ∨ v - t = 1) ∧
        (u + t) + (v - t) = u + v) ∧
      (∫ t, u + t ∂P) = u ∧ (∫ t, v - t ∂P) = v ∧
      Integrable (fun t => Riesz.Analysis.signedDiscrepancyEnergy q (t • unitDipole d x y)) P ∧
      (∫ t, Riesz.Analysis.signedDiscrepancyEnergy q (t • unitDipole d x y) ∂P) ≤
        D ^ q / q * (fractionalBudget u + fractionalBudget v -
          ∫ t, fractionalBudget (u + t) + fractionalBudget (v - t) ∂P) ∧
      (∫ t, fractionalBudget (u + t) + fractionalBudget (v - t) ∂P) <
        fractionalBudget u + fractionalBudget v := by
  exact ⟨twoWeightTransferLaw u v, twoWeightTransferLaw_isProbability u v hu hu_one hv hv_one,
    twoWeightTransferLaw_support u v hu hu_one hv hv_one,
    (twoWeightTransferLaw_weight_means u v hu hu_one hv hv_one).1,
    (twoWeightTransferLaw_weight_means u v hu hu_one hv hv_one).2,
    integrable_twoWeightTransferLaw u v _,
    twoWeightTransferLaw_energy_budget_bound d q D hq u v hu hu_one hv hv_one x y hxy hdiam,
    twoWeightTransferLaw_budget_strict u v hu hu_one hv hv_one⟩

end Riesz.Negative
