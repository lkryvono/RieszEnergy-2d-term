import Riesz.Negative.TwoWeightRounding

/-! Finite atomic signed discrepancies and their exact distance-power quadratic form.
This representation is used to combine the steps of finite-list rounding. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

def weightedAtomicMeasure (d n : ℕ) (x : Fin n → Rd d) (w : Fin n → ℝ) : Measure (Rd d) :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i)

def weightedSignedMeasure (d n : ℕ) (x : Fin n → Rd d) (w : Fin n → ℝ) :
    SignedMeasure (Rd d) :=
  ∑ i, w i • (Measure.dirac (x i)).toSignedMeasure

def weightQuadratic (d n : ℕ) (q : ℝ) (x : Fin n → Rd d) (w : Fin n → ℝ) : ℝ :=
  -(1 / q) * ∑ i, ∑ j, w i * w j * ‖x i - x j‖ ^ q

instance weightedAtomicMeasure_isFinite (d n : ℕ) (x : Fin n → Rd d) (w : Fin n → ℝ) :
    IsFiniteMeasure (weightedAtomicMeasure d n x w) := by
  unfold weightedAtomicMeasure
  refine ⟨?_⟩
  simp [Measure.finsetSum_apply, Measure.smul_apply, ENNReal.sum_lt_top]

theorem weightedAtomicMeasure_prod (d n : ℕ) (x : Fin n → Rd d) (a b : Fin n → ℝ) :
    (weightedAtomicMeasure d n x a).prod (weightedAtomicMeasure d n x b) =
      ∑ i, ∑ j, (ENNReal.ofReal (a i) * ENNReal.ofReal (b j)) • Measure.dirac (x i, x j) := by
  unfold weightedAtomicMeasure
  simp_rw [← Measure.sum_fintype]
  simp_rw [Measure.prod_sum_left, Measure.prod_sum_right, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul, Measure.dirac_prod_dirac]

theorem integrable_weightedAtomic_prod (d n : ℕ) (x : Fin n → Rd d)
    (a b : Fin n → ℝ) (f : Rd d × Rd d → ℝ) :
    Integrable f ((weightedAtomicMeasure d n x a).prod (weightedAtomicMeasure d n x b)) := by
  rw [weightedAtomicMeasure_prod]
  exact integrable_finsetSum_measure.mpr (fun i _ => integrable_finsetSum_measure.mpr
    (fun j _ => (integrable_dirac (by simp)).smul_measure (by finiteness)))

theorem weightedAtomicMeasure_toSigned (d n : ℕ) (x : Fin n → Rd d) (w : Fin n → ℝ) :
    (weightedAtomicMeasure d n x w).toSignedMeasure =
      ∑ i, max (w i) 0 • (Measure.dirac (x i)).toSignedMeasure := by
  ext A hA
  simp only [Measure.toSignedMeasure_apply_measurable hA, weightedAtomicMeasure,
    measureReal_def, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    _root_.sum_apply, _root_.smul_apply]
  rw [ENNReal.toReal_sum (fun i _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal']

theorem weightedAtomicMeasure_mutuallySingular (d n : ℕ) (x : Fin n → Rd d)
    (hx : Function.Injective x) (w : Fin n → ℝ) :
    weightedAtomicMeasure d n x w ⟂ₘ weightedAtomicMeasure d n x (fun i => -w i) := by
  unfold weightedAtomicMeasure
  simp_rw [← Measure.sum_fintype, Measure.MutuallySingular.sum_left,
    Measure.MutuallySingular.sum_right]
  intro i j
  by_cases hij : i = j
  · subst j
    by_cases hw : 0 ≤ w i
    · simp [ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hw)]
    · simp [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hw)]
  · have hsites : Measure.dirac (x i) ⟂ₘ Measure.dirac (x j) :=
      ⟨{x i}ᶜ, (measurableSet_singleton (x i)).compl, by simp, by simp [Ne.symm (hx.ne hij)]⟩
    exact ((hsites.smul (ENNReal.ofReal (w i))).symm.smul (ENNReal.ofReal (-w j))).symm

theorem weightedAtomicMeasure_sub_toSigned (d n : ℕ) (x : Fin n → Rd d) (w : Fin n → ℝ) :
    (weightedAtomicMeasure d n x w).toSignedMeasure -
      (weightedAtomicMeasure d n x (fun i => -w i)).toSignedMeasure =
        weightedSignedMeasure d n x w := by
  simp only [weightedAtomicMeasure_toSigned, weightedSignedMeasure, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← sub_smul (max (w i) 0) (max (-w i) 0) (Measure.dirac (x i)).toSignedMeasure,
    max_zero_sub_max_neg_zero_eq_self]

theorem weightedSignedMeasure_jordan_parts (d n : ℕ) (x : Fin n → Rd d)
    (hx : Function.Injective x) (w : Fin n → ℝ) :
    (weightedSignedMeasure d n x w).toJordanDecomposition.posPart = weightedAtomicMeasure d n x w ∧
      (weightedSignedMeasure d n x w).toJordanDecomposition.negPart =
        weightedAtomicMeasure d n x (fun i => -w i) := by
  let J : JordanDecomposition (Rd d) := ⟨weightedAtomicMeasure d n x w,
    weightedAtomicMeasure d n x (fun i => -w i), weightedAtomicMeasure_mutuallySingular d n x hx w⟩
  have hJ : J.toSignedMeasure = weightedSignedMeasure d n x w :=
    weightedAtomicMeasure_sub_toSigned d n x w
  rw [← hJ, JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  exact ⟨rfl, rfl⟩

theorem integral_weightedAtomic_prod (d n : ℕ) (x : Fin n → Rd d)
    (a b : Fin n → ℝ) (f : Rd d × Rd d → ℝ) :
    (∫ p, f p ∂(weightedAtomicMeasure d n x a).prod (weightedAtomicMeasure d n x b)) =
      ∑ i, ∑ j, max (a i) 0 * max (b j) 0 * f (x i, x j) := by
  rw [weightedAtomicMeasure_prod]
  rw [integral_finsetSum_measure (fun i _ => integrable_finsetSum_measure.mpr
    (fun j _ => (integrable_dirac (by simp)).smul_measure (by finiteness)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum_measure (fun j _ =>
    (integrable_dirac (by simp)).smul_measure (by finiteness))]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal', smul_eq_mul]

/-- The finite matrix expression is the actual signed discrepancy energy.
Weights may have either sign; distinct sites are needed for this Jordan expansion. -/
theorem weightedSignedMeasure_energy (d n : ℕ) (q : ℝ) (x : Fin n → Rd d)
    (hx : Function.Injective x) (w : Fin n → ℝ) :
    Riesz.Analysis.signedDiscrepancyEnergy q (weightedSignedMeasure d n x w) =
      weightQuadratic d n q x w := by
  unfold Riesz.Analysis.signedDiscrepancyEnergy Riesz.Analysis.signedKernelQuadratic weightQuadratic
  simp only [(weightedSignedMeasure_jordan_parts d n x hx w).1,
    (weightedSignedMeasure_jordan_parts d n x hx w).2, integral_weightedAtomic_prod]
  congr 1
  simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  calc
    _ = (max (w i) 0 - max (-w i) 0) * (max (w j) 0 - max (-w j) 0) *
        ‖x i - x j‖ ^ q := by ring
    _ = _ := by rw [max_zero_sub_max_neg_zero_eq_self, max_zero_sub_max_neg_zero_eq_self]

end Riesz.Negative
