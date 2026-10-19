import Riesz.Negative.FiniteSampling
import Riesz.Negative.FiniteCells

/-! Exact expected discrepancy energy for independent weighted cell samples.
This supplies the initial continuous-sampling cost in dyadic discretization. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

def cellMeasureSum (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d)) : Measure (Rd d) :=
  ∑ i, (ν i : Measure (Rd d))

instance cellMeasureSum_isFiniteMeasure (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) : IsFiniteMeasure (cellMeasureSum d n ν) :=
  inferInstanceAs (IsFiniteMeasure (∑ i, (ν i : Measure (Rd d))))

def sampledCellDiscrepancy (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d))
    (x : Fin n → Rd d) : SignedMeasure (Rd d) :=
  (weightedAtomicMeasure d n x (fun i => ((ν i).mass : ℝ))).toSignedMeasure -
    (cellMeasureSum d n ν).toSignedMeasure

theorem weightedAtomicMeasure_mutuallySingular_diffuse (d n : ℕ)
    (x : Fin n → Rd d) (w : Fin n → ℝ) (ρ : Measure (Rd d)) [NullSingletonClass ρ] :
    weightedAtomicMeasure d n x w ⟂ₘ ρ := by
  simp only [weightedAtomicMeasure, ← Measure.sum_fintype, Measure.MutuallySingular.sum_left]
  exact fun i => (mutuallySingular_dirac (x i) ρ).smul (ENNReal.ofReal (w i))

theorem cellMeasureSum_nullSingletonClass (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hatom : ∀ i y, ν i {y} = 0) :
    NullSingletonClass (cellMeasureSum d n ν) := by
  refine ⟨fun y => ?_⟩
  simp [cellMeasureSum, ← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, hatom]

theorem sampledCellDiscrepancy_jordan_parts (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hatom : ∀ i y, ν i {y} = 0)
    (x : Fin n → Rd d) :
    (sampledCellDiscrepancy d n ν x).toJordanDecomposition.posPart =
      weightedAtomicMeasure d n x (fun i => ((ν i).mass : ℝ)) ∧
    (sampledCellDiscrepancy d n ν x).toJordanDecomposition.negPart = cellMeasureSum d n ν := by
  letI := cellMeasureSum_nullSingletonClass d n ν hatom
  let J : JordanDecomposition (Rd d) :=
    ⟨weightedAtomicMeasure d n x (fun i => ((ν i).mass : ℝ)), cellMeasureSum d n ν,
      weightedAtomicMeasure_mutuallySingular_diffuse d n x _ _⟩
  exact ⟨congrArg JordanDecomposition.posPart
    (JordanDecomposition.toJordanDecomposition_toSignedMeasure J),
    congrArg JordanDecomposition.negPart
    (JordanDecomposition.toJordanDecomposition_toSignedMeasure J)⟩

theorem normalizedCellPair_integral (d : ℕ) (ν ρ : FiniteMeasure (Rd d))
    (k : Rd d → Rd d → ℝ) :
    ((ν.mass : ℝ) * (ρ.mass : ℝ)) *
      (∫ p : Rd d × Rd d, k p.1 p.2
        ∂(ν.normalize : Measure (Rd d)).prod (ρ.normalize : Measure (Rd d))) =
      ∫ p : Rd d × Rd d, k p.1 p.2 ∂(ν : Measure (Rd d)).prod (ρ : Measure (Rd d)) := by
  have hν : (ν : Measure (Rd d)) = ν.mass • (ν.normalize : Measure (Rd d)) :=
    (congrArg (fun μ : FiniteMeasure (Rd d) => (μ : Measure (Rd d)))
      ν.self_eq_mass_smul_normalize)
  have hρ : (ρ : Measure (Rd d)) = ρ.mass • (ρ.normalize : Measure (Rd d)) :=
    (congrArg (fun μ : FiniteMeasure (Rd d) => (μ : Measure (Rd d)))
      ρ.self_eq_mass_smul_normalize)
  rw [hν, hρ, Measure.prod_smul_left, Measure.prod_smul_right,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, smul_eq_mul, mul_assoc]

def centeredPointCross (d : ℕ) (k : Rd d → Rd d → ℝ)
    (μ ρ : Measure (Rd d)) (p : Rd d × Rd d) : ℝ :=
  k p.1 p.2 - (∫ y, k p.1 y ∂ρ) - (∫ x, k x p.2 ∂μ) +
    ∫ z : Rd d × Rd d, k z.1 z.2 ∂μ.prod ρ

theorem centeredPointCross_integrable (d : ℕ) (k : Rd d → Rd d → ℝ)
    (μ ρ : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2) (μ.prod ρ)) :
    Integrable (centeredPointCross d k μ ρ) (μ.prod ρ) := by
  exact ((hk.sub (hk.integral_prod_left.comp_fst ρ)).sub
    (hk.integral_prod_right.comp_snd μ)).add (integrable_const _)

theorem centeredPointCross_expectation (d : ℕ) (k : Rd d → Rd d → ℝ)
    (μ ρ : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2) (μ.prod ρ)) :
    (∫ p, centeredPointCross d k μ ρ p ∂μ.prod ρ) = 0 := by
  unfold centeredPointCross
  rw [integral_add (f := fun p : Rd d × Rd d =>
      k p.1 p.2 - (∫ y, k p.1 y ∂ρ) - (∫ x, k x p.2 ∂μ))
      (g := fun _ : Rd d × Rd d =>
      ∫ z : Rd d × Rd d, k z.1 z.2 ∂μ.prod ρ)
      ((hk.sub (hk.integral_prod_left.comp_fst ρ)).sub
      (hk.integral_prod_right.comp_snd μ)) (integrable_const _),
    integral_sub (f := fun p : Rd d × Rd d => k p.1 p.2 - ∫ y, k p.1 y ∂ρ)
      (g := fun p : Rd d × Rd d => ∫ x, k x p.2 ∂μ)
      (hk.sub (hk.integral_prod_left.comp_fst ρ))
      (hk.integral_prod_right.comp_snd μ),
    integral_sub (f := fun p : Rd d × Rd d => k p.1 p.2)
      (g := fun p : Rd d × Rd d => ∫ y, k p.1 y ∂ρ)
      hk (hk.integral_prod_left.comp_fst ρ),
    integral_fun_fst (fun x : Rd d => ∫ y, k x y ∂ρ),
    integral_fun_snd (fun y : Rd d => ∫ x, k x y ∂μ), integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
    ← integral_prod _ hk, ← integral_prod_symm _ hk, sub_self, zero_sub, neg_add_cancel]

def cellSampleCross (d : ℕ) (k : Rd d → Rd d → ℝ)
    (ν ρ : FiniteMeasure (Rd d)) (p : Rd d × Rd d) : ℝ :=
  finiteDiscrepancyCross d k (cellSampleAtom d ν p.1) (ν : Measure (Rd d))
    (cellSampleAtom d ρ p.2) (ρ : Measure (Rd d))

theorem cellSampleCross_eq_centered (d : ℕ) (k : Rd d → Rd d → ℝ)
    (ν ρ : FiniteMeasure (Rd d)) (p : Rd d × Rd d) :
    cellSampleCross d k ν ρ p = ((ν.mass : ℝ) * (ρ.mass : ℝ)) *
      centeredPointCross d k (ν.normalize : Measure (Rd d))
        (ρ.normalize : Measure (Rd d)) p := by
  unfold cellSampleCross finiteDiscrepancyCross cellSampleAtom centeredPointCross
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, integral_smul_measure,
    ENNReal.coe_toReal, smul_eq_mul, integral_dirac,
    Measure.dirac_prod, Measure.prod_dirac,
    (measurableEmbedding_prodMk_left p.1).integral_map,
    (measurableEmbedding_prod_mk_right p.2).integral_map]
  rw [← cellSampleLaw_integral d ρ (fun y => k p.1 y), integral_const_mul,
    ← cellSampleLaw_integral d ν (fun x => k x p.2), integral_const_mul,
    ← normalizedCellPair_integral d ν ρ k]
  ring

theorem cellSampleCross_integrable (d : ℕ) (k : Rd d → Rd d → ℝ)
    (ν ρ : FiniteMeasure (Rd d))
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((ν.normalize : Measure (Rd d)).prod (ρ.normalize : Measure (Rd d)))) :
    Integrable (cellSampleCross d k ν ρ)
      ((ν.normalize : Measure (Rd d)).prod (ρ.normalize : Measure (Rd d))) := by
  exact ((centeredPointCross_integrable d k _ _ hk).const_mul
    ((ν.mass : ℝ) * (ρ.mass : ℝ))).congr
      (ae_of_all _ (fun p => (cellSampleCross_eq_centered d k ν ρ p).symm))

theorem cellSampleCross_expectation (d : ℕ) (k : Rd d → Rd d → ℝ)
    (ν ρ : FiniteMeasure (Rd d))
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((ν.normalize : Measure (Rd d)).prod (ρ.normalize : Measure (Rd d)))) :
    (∫ p, cellSampleCross d k ν ρ p
      ∂(ν.normalize : Measure (Rd d)).prod (ρ.normalize : Measure (Rd d))) = 0 := by
  simp_rw [cellSampleCross_eq_centered, integral_const_mul,
    centeredPointCross_expectation d k _ _ hk, mul_zero]

theorem pointFamily_pair_map (d n : ℕ) (μ : Fin n → Measure (Rd d))
    [∀ i, IsProbabilityMeasure (μ i)] (i j : Fin n) (hij : i ≠ j) :
    Measure.map (fun x : Fin n → Rd d => (x i, x j)) (Measure.pi μ) =
      (μ i).prod (μ j) := by
  simpa only [(measurePreserving_eval μ i).map_eq, (measurePreserving_eval μ j).map_eq]
    using ((ProbabilityTheory.iIndepFun_pi (μ := μ) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hij).map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable

theorem pointFamily_pair_measurePreserving (d n : ℕ) (μ : Fin n → Measure (Rd d))
    [∀ i, IsProbabilityMeasure (μ i)] (i j : Fin n) (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin n → Rd d => (x i, x j)) (Measure.pi μ)
      ((μ i).prod (μ j)) := by
  exact ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),
    pointFamily_pair_map d n μ i j hij⟩

theorem pointFamily_integral_pair (d n : ℕ) (μ : Fin n → Measure (Rd d))
    [∀ i, IsProbabilityMeasure (μ i)] (i j : Fin n) (hij : i ≠ j)
    (f : Rd d × Rd d → ℝ) (hf : Integrable f ((μ i).prod (μ j))) :
    (∫ x, f (x i, x j) ∂Measure.pi μ) = ∫ p, f p ∂(μ i).prod (μ j) := by
  simpa only [pointFamily_pair_map d n μ i j hij] using
    (integral_map (μ := Measure.pi μ) (φ := fun x : Fin n → Rd d => (x i, x j))
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
      ((pointFamily_pair_map d n μ i j hij).symm ▸ hf).aestronglyMeasurable).symm

theorem centeredPointCross_diagonal_integrable (d : ℕ) (k : Rd d → Rd d → ℝ)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2) (μ.prod μ))
    (hdiag : Integrable (fun x => k x x) μ) :
    Integrable (fun x => centeredPointCross d k μ μ (x, x)) μ := by
  exact ((hdiag.sub hk.integral_prod_left).sub hk.integral_prod_right).add
    (integrable_const _)

theorem cellSampleCross_diagonal_integrable (d : ℕ) (k : Rd d → Rd d → ℝ)
    (ν : FiniteMeasure (Rd d))
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((ν.normalize : Measure (Rd d)).prod (ν.normalize : Measure (Rd d))))
    (hdiag : Integrable (fun x => k x x) (ν.normalize : Measure (Rd d))) :
    Integrable (fun x => cellSampleCross d k ν ν (x, x))
      (ν.normalize : Measure (Rd d)) := by
  exact ((centeredPointCross_diagonal_integrable d k _ hk hdiag).const_mul
    ((ν.mass : ℝ) * (ν.mass : ℝ))).congr
      (ae_of_all _ (fun x => (cellSampleCross_eq_centered d k ν ν (x, x)).symm))

theorem cellSampleCross_pi_integrable_offDiagonal (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (k : Rd d → Rd d → ℝ)
    (i j : Fin n) (hij : i ≠ j)
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      (((ν i).normalize : Measure (Rd d)).prod ((ν j).normalize : Measure (Rd d)))) :
    Integrable (fun x : Fin n → Rd d => cellSampleCross d k (ν i) (ν j) (x i, x j))
      (Measure.pi (fun i => ((ν i).normalize : Measure (Rd d)))) := by
  exact (pointFamily_pair_measurePreserving d n
    (fun i => ((ν i).normalize : Measure (Rd d))) i j hij).integrable_comp_of_integrable
    (cellSampleCross_integrable d k (ν i) (ν j) hk)

theorem cellSampleCross_pi_expectation_offDiagonal (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (k : Rd d → Rd d → ℝ)
    (i j : Fin n) (hij : i ≠ j)
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      (((ν i).normalize : Measure (Rd d)).prod ((ν j).normalize : Measure (Rd d)))) :
    (∫ x : Fin n → Rd d, cellSampleCross d k (ν i) (ν j) (x i, x j)
      ∂Measure.pi (fun i => ((ν i).normalize : Measure (Rd d)))) = 0 := by
  exact (pointFamily_integral_pair d n (fun i => ((ν i).normalize : Measure (Rd d)))
    i j hij _ (cellSampleCross_integrable d k (ν i) (ν j) hk)).trans
      (cellSampleCross_expectation d k (ν i) (ν j) hk)

theorem cellSampleCross_pi_integrable (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (k : Rd d → Rd d → ℝ)
    (hk : ∀ i j, Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      (((ν i).normalize : Measure (Rd d)).prod ((ν j).normalize : Measure (Rd d))))
    (hdiag : ∀ i, Integrable (fun x => k x x) ((ν i).normalize : Measure (Rd d)))
    (i j : Fin n) :
    Integrable (fun x : Fin n → Rd d => cellSampleCross d k (ν i) (ν j) (x i, x j))
      (Measure.pi (fun i => ((ν i).normalize : Measure (Rd d)))) := by
  rcases eq_or_ne i j with rfl | hij
  · exact (measurePreserving_eval (fun j => ((ν j).normalize : Measure (Rd d))) i)
      |>.integrable_comp_of_integrable (cellSampleCross_diagonal_integrable d k (ν i)
        (hk i i) (hdiag i))
  · exact cellSampleCross_pi_integrable_offDiagonal d n ν k i j hij (hk i j)

def cellSampleCrossSum (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d))
    (k : Rd d → Rd d → ℝ) (x : Fin n → Rd d) : ℝ :=
  ∑ ij : Fin n × Fin n, cellSampleCross d k (ν ij.1) (ν ij.2) (x ij.1, x ij.2)

theorem cellSampleCrossSum_integrable (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (k : Rd d → Rd d → ℝ)
    (hk : ∀ i j, Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      (((ν i).normalize : Measure (Rd d)).prod ((ν j).normalize : Measure (Rd d))))
    (hdiag : ∀ i, Integrable (fun x => k x x) ((ν i).normalize : Measure (Rd d))) :
    Integrable (cellSampleCrossSum d n ν k)
      (Measure.pi (fun i => ((ν i).normalize : Measure (Rd d)))) := by
  exact integrable_finsetSum _ (fun ij _ =>
    cellSampleCross_pi_integrable d n ν k hk hdiag ij.1 ij.2)

theorem cellSampleCrossSum_expectation (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (k : Rd d → Rd d → ℝ)
    (hk : ∀ i j, Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      (((ν i).normalize : Measure (Rd d)).prod ((ν j).normalize : Measure (Rd d))))
    (hdiag : ∀ i, Integrable (fun x => k x x) ((ν i).normalize : Measure (Rd d))) :
    (∫ x, cellSampleCrossSum d n ν k x
      ∂Measure.pi (fun i => ((ν i).normalize : Measure (Rd d)))) =
      ∑ i, ∫ x : Fin n → Rd d, cellSampleCross d k (ν i) (ν i) (x i, x i)
        ∂Measure.pi (fun i => ((ν i).normalize : Measure (Rd d))) := by
  unfold cellSampleCrossSum
  rw [integral_finsetSum _ (fun ij _ =>
    cellSampleCross_pi_integrable d n ν k hk hdiag ij.1 ij.2), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Finset.sum_eq_single i
    (fun j _ hji => cellSampleCross_pi_expectation_offDiagonal d n ν k i j hji.symm (hk i j))
    (fun hi => (hi (Finset.mem_univ i)).elim)

theorem cellSampleIncrement_energy_eq_cross (d : ℕ) (q : ℝ)
    (ν : FiniteMeasure (Rd d)) (hatom : ∀ y : Rd d, ν {y} = 0) (x : Rd d) :
    Riesz.Analysis.signedDiscrepancyEnergy q (cellSampleIncrement d ν x) =
      -(1 / q) * cellSampleCross d (fun a b => ‖a - b‖ ^ q) ν ν (x, x) := by
  simp only [Riesz.Analysis.signedDiscrepancyEnergy, Riesz.Analysis.signedKernelQuadratic,
    (cellSampleIncrement_jordan_parts d ν hatom x).1,
    (cellSampleIncrement_jordan_parts d ν hatom x).2, cellSampleCross, finiteDiscrepancyCross]

theorem weightedAtomicMeasure_eq_cellSampleSum (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (x : Fin n → Rd d) :
    weightedAtomicMeasure d n x (fun i => ((ν i).mass : ℝ)) =
      ∑ i, cellSampleAtom d (ν i) (x i) := by
  simp [weightedAtomicMeasure, cellSampleAtom]

theorem sampledCellDiscrepancy_energy_eq_finiteCross (d n : ℕ) (q : ℝ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hatom : ∀ i y, ν i {y} = 0)
    (x : Fin n → Rd d) :
    Riesz.Analysis.signedDiscrepancyEnergy q (sampledCellDiscrepancy d n ν x) =
      -(1 / q) * finiteDiscrepancyCross d (fun a b => ‖a - b‖ ^ q)
        (weightedAtomicMeasure d n x (fun i => ((ν i).mass : ℝ))) (cellMeasureSum d n ν)
        (weightedAtomicMeasure d n x (fun i => ((ν i).mass : ℝ))) (cellMeasureSum d n ν) := by
  simp only [Riesz.Analysis.signedDiscrepancyEnergy, Riesz.Analysis.signedKernelQuadratic,
    (sampledCellDiscrepancy_jordan_parts d n ν hatom x).1,
    (sampledCellDiscrepancy_jordan_parts d n ν hatom x).2, finiteDiscrepancyCross]

theorem sampledCellDiscrepancy_energy_eq_crossSum_of_integrable (d n : ℕ) (q : ℝ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hatom : ∀ i y, ν i {y} = 0)
    (x : Fin n → Rd d)
    (haa : ∀ i j, Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q)
      ((cellSampleAtom d (ν i) (x i)).prod (cellSampleAtom d (ν j) (x j))))
    (hab : ∀ i j, Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q)
      ((cellSampleAtom d (ν i) (x i)).prod (ν j : Measure (Rd d))))
    (hba : ∀ i j, Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q)
      ((ν i : Measure (Rd d)).prod (cellSampleAtom d (ν j) (x j))))
    (hbb : ∀ i j, Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q)
      ((ν i : Measure (Rd d)).prod (ν j : Measure (Rd d)))) :
    Riesz.Analysis.signedDiscrepancyEnergy q (sampledCellDiscrepancy d n ν x) =
      -(1 / q) * cellSampleCrossSum d n ν (fun a b => ‖a - b‖ ^ q) x := by
  simpa only [sampledCellDiscrepancy_energy_eq_finiteCross d n q ν hatom x,
    weightedAtomicMeasure_eq_cellSampleSum, cellMeasureSum, cellSampleCrossSum, cellSampleCross]
    using congrArg (fun r : ℝ => -(1 / q) * r)
      (finiteDiscrepancyCross_cellSum d n (fun a b => ‖a - b‖ ^ q)
        (fun i => cellSampleAtom d (ν i) (x i)) (fun i => (ν i : Measure (Rd d)))
        haa hab hba hbb)

theorem cellSampleAtom_concentrated (d : ℕ) (ν : FiniteMeasure (Rd d))
    (S : Set (Rd d)) (x : Rd d) (hx : x ∈ S) : cellSampleAtom d ν x Sᶜ = 0 := by
  simp [cellSampleAtom, Measure.smul_apply, hx]

theorem normalizedCell_concentrated (d : ℕ) (ν : FiniteMeasure (Rd d)) (hν : ν ≠ 0)
    (S : Set (Rd d)) (hsupport : (ν : Measure (Rd d)) Sᶜ = 0) :
    (ν.normalize : Measure (Rd d)) Sᶜ = 0 := by
  simp [ν.toMeasure_normalize_eq_of_nonzero hν, Measure.smul_apply, hsupport]

theorem sampledCellDiscrepancy_energy_eq_crossSum (d n : ℕ) (q D : ℝ) (hq : 0 ≤ q)
    (ν : Fin n → FiniteMeasure (Rd d)) (hatom : ∀ i y, ν i {y} = 0)
    (S : Set (Rd d)) (hsupport : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ ≤ D)
    (x : Fin n → Rd d) (hx : ∀ i, x i ∈ S) :
    Riesz.Analysis.signedDiscrepancyEnergy q (sampledCellDiscrepancy d n ν x) =
      -(1 / q) * cellSampleCrossSum d n ν (fun a b => ‖a - b‖ ^ q) x := by
  have hInt (μ ρ : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
      (hμ : μ Sᶜ = 0) (hρ : ρ Sᶜ = 0) :
      Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q) (μ.prod ρ) :=
    Riesz.Analysis.integrable_rpow_distance q D hq μ ρ
      (Riesz.Analysis.ae_distance_le_of_concentrated μ ρ S D hμ hρ hdiam)
  exact sampledCellDiscrepancy_energy_eq_crossSum_of_integrable d n q ν hatom x
    (fun i j => hInt _ _ (cellSampleAtom_concentrated d (ν i) S (x i) (hx i))
      (cellSampleAtom_concentrated d (ν j) S (x j) (hx j)))
    (fun i j => hInt _ _ (cellSampleAtom_concentrated d (ν i) S (x i) (hx i)) (hsupport j))
    (fun i j => hInt _ _ (hsupport i) (cellSampleAtom_concentrated d (ν j) S (x j) (hx j)))
    (fun i j => hInt _ _ (hsupport i) (hsupport j))

theorem normalizedCells_rpow_integrable (d n : ℕ) (q D : ℝ) (hq : 0 ≤ q)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (S : Set (Rd d)) (hsupport : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ ≤ D) (i j : Fin n) :
    Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q)
      (((ν i).normalize : Measure (Rd d)).prod ((ν j).normalize : Measure (Rd d))) := by
  exact Riesz.Analysis.integrable_rpow_distance q D hq _ _
    (Riesz.Analysis.ae_distance_le_of_concentrated _ _ S D
      (normalizedCell_concentrated d (ν i) (hν i) S (hsupport i))
      (normalizedCell_concentrated d (ν j) (hν j) S (hsupport j)) hdiam)

theorem normalizedCell_rpow_diagonal_integrable (d : ℕ) (q : ℝ)
    (ν : FiniteMeasure (Rd d)) :
    Integrable (fun x : Rd d => ‖x - x‖ ^ q) (ν.normalize : Measure (Rd d)) := by
  simpa only [sub_self, norm_zero] using (integrable_const (0 ^ q : ℝ) :
    Integrable (fun _ : Rd d => (0 : ℝ) ^ q) (ν.normalize : Measure (Rd d)))

theorem normalizedCellSites_supported (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (S : Set (Rd d)) (hsupport : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0) :
    ∀ᵐ x ∂Measure.pi (fun i => ((ν i).normalize : Measure (Rd d))), ∀ i, x i ∈ S := by
  exact ae_all_iff.mpr (fun i =>
    (measurePreserving_eval (fun j => ((ν j).normalize : Measure (Rd d))) i)
      |>.quasiMeasurePreserving.ae (mem_ae_iff.mpr
        (normalizedCell_concentrated d (ν i) (hν i) S (hsupport i))))

theorem sampledCellDiscrepancy_pi_integrable (d n : ℕ) (q D : ℝ) (hq : 0 ≤ q)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hatom : ∀ i y, ν i {y} = 0) (S : Set (Rd d))
    (hsupport : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ ≤ D) :
    Integrable (fun x => Riesz.Analysis.signedDiscrepancyEnergy q
      (sampledCellDiscrepancy d n ν x))
      (Measure.pi (fun i => ((ν i).normalize : Measure (Rd d)))) := by
  exact ((cellSampleCrossSum_integrable d n ν (fun a b => ‖a - b‖ ^ q)
    (normalizedCells_rpow_integrable d n q D hq ν hν S hsupport hdiam)
    (fun i => normalizedCell_rpow_diagonal_integrable d q (ν i))).const_mul (-(1 / q))).congr
      ((normalizedCellSites_supported d n ν hν S hsupport).mono (fun x hx =>
        (sampledCellDiscrepancy_energy_eq_crossSum d n q D hq ν hatom S hsupport hdiam x hx).symm))

theorem cellSampleIncrement_pi_integrable (d n : ℕ) (q D : ℝ) (hq : 0 ≤ q)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hatom : ∀ i y, ν i {y} = 0) (S : Set (Rd d))
    (hsupport : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ ≤ D) (i : Fin n) :
    Integrable (fun x : Fin n → Rd d => Riesz.Analysis.signedDiscrepancyEnergy q
      (cellSampleIncrement d (ν i) (x i)))
      (Measure.pi (fun i => ((ν i).normalize : Measure (Rd d)))) := by
  exact ((cellSampleCross_pi_integrable d n ν (fun a b => ‖a - b‖ ^ q)
    (normalizedCells_rpow_integrable d n q D hq ν hν S hsupport hdiam)
    (fun j => normalizedCell_rpow_diagonal_integrable d q (ν j)) i i).const_mul (-(1 / q))).congr
      (ae_of_all _ (fun x =>
        (cellSampleIncrement_energy_eq_cross d q (ν i) (hatom i) (x i)).symm))

theorem sampledCellDiscrepancy_pi_expectation (d n : ℕ) (q D : ℝ) (hq : 0 ≤ q)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hatom : ∀ i y, ν i {y} = 0) (S : Set (Rd d))
    (hsupport : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ ≤ D) :
    (∫ x, Riesz.Analysis.signedDiscrepancyEnergy q (sampledCellDiscrepancy d n ν x)
      ∂Measure.pi (fun i => ((ν i).normalize : Measure (Rd d)))) =
      ∑ i, ∫ x : Fin n → Rd d, Riesz.Analysis.signedDiscrepancyEnergy q
        (cellSampleIncrement d (ν i) (x i))
        ∂Measure.pi (fun i => ((ν i).normalize : Measure (Rd d))) := by
  rw [integral_congr_ae ((normalizedCellSites_supported d n ν hν S hsupport).mono
    (fun x hx => sampledCellDiscrepancy_energy_eq_crossSum d n q D hq ν hatom S hsupport hdiam x hx))]
  rw [integral_const_mul, cellSampleCrossSum_expectation d n ν (fun a b => ‖a - b‖ ^ q)
    (normalizedCells_rpow_integrable d n q D hq ν hν S hsupport hdiam)
    (fun i => normalizedCell_rpow_diagonal_integrable d q (ν i)), Finset.mul_sum]
  simp_rw [cellSampleIncrement_energy_eq_cross d q _ (hatom _), integral_const_mul]

theorem sampledCellSites_measurePreserving (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) :
    MeasurePreserving (sampledCellSites d n ν) (uniformCellMarks n)
      (Measure.pi (fun i => ((ν i).normalize : Measure (Rd d)))) := by
  exact ⟨measurable_sampledCellSites d n ν, sampledCellSites_map d n ν⟩

theorem sampledCellSites_integral (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (f : (Fin n → Rd d) → ℝ)
    (hf : Integrable f (Measure.pi (fun i => ((ν i).normalize : Measure (Rd d))))) :
    (∫ u, f (sampledCellSites d n ν u) ∂uniformCellMarks n) =
      ∫ x, f x ∂Measure.pi (fun i => ((ν i).normalize : Measure (Rd d))) := by
  simpa only [sampledCellSites_map d n ν] using
    (integral_map (μ := uniformCellMarks n) (φ := sampledCellSites d n ν)
      (measurable_sampledCellSites d n ν).aemeasurable
      ((sampledCellSites_map d n ν).symm ▸ hf).aestronglyMeasurable).symm

theorem sampledCellDiscrepancy_marks_integrable (d n : ℕ) (q D : ℝ) (hq : 0 ≤ q)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hatom : ∀ i y, ν i {y} = 0) (S : Set (Rd d))
    (hsupport : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ ≤ D) :
    Integrable (fun u => Riesz.Analysis.signedDiscrepancyEnergy q
      (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u))) (uniformCellMarks n) := by
  exact (sampledCellSites_measurePreserving d n ν).integrable_comp_of_integrable
    (sampledCellDiscrepancy_pi_integrable d n q D hq ν hν hatom S hsupport hdiam)

theorem cellSampleIncrement_marks_integrable (d n : ℕ) (q D : ℝ) (hq : 0 ≤ q)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hatom : ∀ i y, ν i {y} = 0) (S : Set (Rd d))
    (hsupport : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ ≤ D) (i : Fin n) :
    Integrable (fun u => Riesz.Analysis.signedDiscrepancyEnergy q
      (cellSampleIncrement d (ν i) (sampledCellSites d n ν u i))) (uniformCellMarks n) := by
  exact (sampledCellSites_measurePreserving d n ν).integrable_comp_of_integrable
    (cellSampleIncrement_pi_integrable d n q D hq ν hν hatom S hsupport hdiam i)

/-- Independent continuous replacements have additive actual expected signed
energy on the fixed mark space used by the subsequent rounding algorithm. -/
theorem sampledCellSites_expected_energy_additive (d n : ℕ) (q D : ℝ) (hq : 0 ≤ q)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hatom : ∀ i y, ν i {y} = 0) (S : Set (Rd d))
    (hsupport : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ ≤ D) :
    (∫ u, Riesz.Analysis.signedDiscrepancyEnergy q
      (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u)) ∂uniformCellMarks n) =
      ∑ i, ∫ u, Riesz.Analysis.signedDiscrepancyEnergy q
        (cellSampleIncrement d (ν i) (sampledCellSites d n ν u i)) ∂uniformCellMarks n := by
  rw [sampledCellSites_integral d n ν _
    (sampledCellDiscrepancy_pi_integrable d n q D hq ν hν hatom S hsupport hdiam),
    sampledCellDiscrepancy_pi_expectation d n q D hq ν hν hatom S hsupport hdiam]
  exact Finset.sum_congr rfl (fun i _ => (sampledCellSites_integral d n ν _
    (cellSampleIncrement_pi_integrable d n q D hq ν hν hatom S hsupport hdiam i)).symm)

/-- The total initial sampling cost is bounded by the sum of the local
diameter and squared-mass budgets; no exact one-cell expectation is needed. -/
theorem sampledCellSites_expected_energy_budget (d n : ℕ) (q D : ℝ) (hq : 0 < q)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hatom : ∀ i y, ν i {y} = 0) (S : Set (Rd d))
    (hcommon : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0)
    (hcommon_diam : ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ ≤ D)
    (L : Fin n → ℝ) (hL : ∀ i, 0 ≤ L i) (B : Fin n → Set (Rd d))
    (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdiam : ∀ i, ∀ a ∈ B i, ∀ b ∈ B i, ‖a - b‖ ≤ L i) :
    (∫ u, Riesz.Analysis.signedDiscrepancyEnergy q
      (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u)) ∂uniformCellMarks n) ≤
      ∑ i, (L i) ^ q * (2 * ((ν i).mass : ℝ)) ^ 2 / q := by
  rw [sampledCellSites_expected_energy_additive d n q D hq.le ν hν hatom S
    hcommon hcommon_diam, ← integral_finsetSum Finset.univ
      (fun i _ => cellSampleIncrement_marks_integrable d n q D hq.le ν hν hatom S
        hcommon hcommon_diam i)]
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using
    integral_mono_ae
      (integrable_finsetSum Finset.univ (fun i _ =>
        cellSampleIncrement_marks_integrable d n q D hq.le ν hν hatom S
          hcommon hcommon_diam i)) (integrable_const _)
      (sampledCellSites_cell_energy_budget d n ν hν hatom q hq L hL B hsupport hdiam)

/-- Cells of mass at most one have total sampling cost linear in their total
continuous mass, as required by the first stage of dyadic discretization. -/
theorem sampledCellSites_expected_energy_le_mass (d n : ℕ) (q D L : ℝ)
    (hq : 0 < q) (hL : 0 ≤ L)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hmass : ∀ i, (ν i).mass ≤ 1) (hatom : ∀ i y, ν i {y} = 0)
    (S : Set (Rd d)) (hcommon : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0)
    (hcommon_diam : ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ ≤ D)
    (B : Fin n → Set (Rd d)) (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdiam : ∀ i, ∀ a ∈ B i, ∀ b ∈ B i, ‖a - b‖ ≤ L) :
    (∫ u, Riesz.Analysis.signedDiscrepancyEnergy q
      (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u)) ∂uniformCellMarks n) ≤
      (4 * L ^ q / q) * ∑ i, ((ν i).mass : ℝ) := by
  refine (sampledCellSites_expected_energy_budget d n q D hq ν hν hatom S
    hcommon hcommon_diam (fun _ => L) (fun _ => hL) B hsupport hdiam).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hsq : (2 * ((ν i).mass : ℝ)) ^ 2 ≤ 4 * ((ν i).mass : ℝ) := by
    nlinarith [NNReal.coe_nonneg (ν i).mass,
      (show ((ν i).mass : ℝ) ≤ 1 by exact_mod_cast hmass i)]
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hsq (div_nonneg (Real.rpow_nonneg hL q) hq.le)

end Riesz.Negative
