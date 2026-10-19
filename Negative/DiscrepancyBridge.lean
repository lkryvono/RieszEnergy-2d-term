import Riesz.Negative.Sampling

/-! Comparison with the paper's signed finite-volume discrepancy energy.
The limiting cube and stationary comparisons are separate proof targets. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

theorem cube_background_isFiniteMeasure (d m : ℕ) :
    IsFiniteMeasure (volume.restrict (cube d (m : ℝ))) := by
  refine ⟨?_⟩
  simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    volume_cube, ENNReal.ofReal_natCast, ← Nat.cast_pow] using
    ENNReal.natCast_lt_top (m ^ d)

theorem cube_background_nullSingletonClass (d m : ℕ) (hd : 0 < d) :
    NullSingletonClass (volume.restrict (cube d (m : ℝ))) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  infer_instance

theorem tupleCounting_mutuallySingular (d n : ℕ) (x : Fin n → Rd d)
    (ρ : Measure (Rd d)) [NullSingletonClass ρ] :
    tupleCounting d n x ⟂ₘ ρ := by
  simpa only [Measure.sum_fintype, tupleCounting] using
    (Measure.MutuallySingular.sum_left).mpr
      (fun i : Fin n => mutuallySingular_dirac (x i) ρ)

/-- The paper's signed discrepancy of a finite tuple and the cube background. -/
def tupleDiscrepancy (d m : ℕ) (x : Fin (m ^ d) → Rd d) : SignedMeasure (Rd d) :=
  letI := tupleCounting_isFiniteMeasure d (m ^ d) x
  letI := cube_background_isFiniteMeasure d m
  (tupleCounting d (m ^ d) x).toSignedMeasure -
    (volume.restrict (cube d (m : ℝ))).toSignedMeasure

/-- Counting atoms and diffuse cube volume are the exact Jordan parts of the discrepancy. -/
theorem tupleDiscrepancy_jordan_parts (d m : ℕ) (hd : 0 < d)
    (x : Fin (m ^ d) → Rd d) :
    (tupleDiscrepancy d m x).toJordanDecomposition.posPart = tupleCounting d (m ^ d) x ∧
    (tupleDiscrepancy d m x).toJordanDecomposition.negPart =
      volume.restrict (cube d (m : ℝ)) := by
  letI := tupleCounting_isFiniteMeasure d (m ^ d) x
  letI := cube_background_isFiniteMeasure d m
  letI := cube_background_nullSingletonClass d m hd
  let J : JordanDecomposition (Rd d) := ⟨tupleCounting d (m ^ d) x,
    volume.restrict (cube d (m : ℝ)), tupleCounting_mutuallySingular d (m ^ d) x _⟩
  exact ⟨congrArg JordanDecomposition.posPart
    (JordanDecomposition.toJordanDecomposition_toSignedMeasure J),
    congrArg JordanDecomposition.negPart
    (JordanDecomposition.toJordanDecomposition_toSignedMeasure J)⟩

/-- The exact showcase energy agrees with the signed discrepancy form on cube tuples. -/
theorem tuple_D_q_eq_signedDiscrepancyEnergy (d m : ℕ) (q : ℝ)
    (hd : 0 < d) (hq : 0 ≤ q) (x : Fin (m ^ d) → Rd d)
    (hx : ∀ i, x i ∈ cube d (m : ℝ)) :
    D_q d q m (tupleCounting d (m ^ d) x) =
      Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x) := by
  letI := tupleCounting_isFiniteMeasure d (m ^ d) x
  letI := cube_background_isFiniteMeasure d m
  obtain ⟨hpos, hneg⟩ := tupleDiscrepancy_jordan_parts d m hd x
  rw [Riesz.Analysis.signedDiscrepancyEnergy_eq_kernel,
    Riesz.Analysis.signedKernelQuadratic_eq_difference _
      (fun a b => congrArg (K_s (-q)) (norm_sub_rev a b)), hpos, hneg]
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp (cube_isBounded d (m : ℝ))
  have hdiam : ∀ a ∈ cube d (m : ℝ), ∀ b ∈ cube d (m : ℝ), ‖a - b‖ ≤ L :=
    fun a ha b hb => by simpa only [dist_eq_norm] using hL ha hb
  have hμ : tupleCounting d (m ^ d) x (cube d (m : ℝ))ᶜ = 0 :=
    (tupleCounting_compl_eq_zero_iff d (m ^ d) x _ (measurableSet_cube d (m : ℝ))).mpr hx
  have hν : (volume.restrict (cube d (m : ℝ))) (cube d (m : ℝ))ᶜ = 0 := by
    simp only [Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
      Set.compl_inter_self, measure_empty]
  exact Riesz.Analysis.D_q_eq_kernel_quadratic d m q L hq _
    (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hμ hμ hdiam)
    (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hμ hν hdiam)
    (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hν hν hdiam)

theorem cube_background_mass (d m : ℕ) :
    (volume.restrict (cube d (m : ℝ))) Set.univ = (m ^ d : ℕ) := by
  simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    volume_cube, ENNReal.ofReal_natCast, ← Nat.cast_pow]

/-- The tuple and its cube background have exactly equal total mass. -/
theorem tupleDiscrepancy_mass_zero (d m : ℕ) (x : Fin (m ^ d) → Rd d) :
    tupleDiscrepancy d m x Set.univ = 0 := by
  letI := tupleCounting_isFiniteMeasure d (m ^ d) x
  letI := cube_background_isFiniteMeasure d m
  simp only [tupleDiscrepancy, Measure.toSignedMeasure_sub_apply MeasurableSet.univ,
    measureReal_def, tupleCounting_univ, cube_background_mass, sub_self]

theorem tupleDiscrepancy_totalVariation (d m : ℕ) (hd : 0 < d)
    (x : Fin (m ^ d) → Rd d) :
    (tupleDiscrepancy d m x).totalVariation =
      tupleCounting d (m ^ d) x + volume.restrict (cube d (m : ℝ)) := by
  obtain ⟨hpos, hneg⟩ := tupleDiscrepancy_jordan_parts d m hd x
  simp only [SignedMeasure.totalVariation, hpos, hneg]

/-- The finite-volume discrepancy has precisely twice the prescribed point count in variation. -/
theorem tupleDiscrepancy_totalVariation_mass (d m : ℕ) (hd : 0 < d)
    (x : Fin (m ^ d) → Rd d) :
    (tupleDiscrepancy d m x).totalVariation Set.univ = 2 * (m ^ d : ℕ) := by
  simp only [tupleDiscrepancy_totalVariation d m hd x, Measure.add_apply,
    tupleCounting_univ, cube_background_mass, two_mul]

theorem tupleDiscrepancy_concentrated_cube (d m : ℕ) (hd : 0 < d)
    (x : Fin (m ^ d) → Rd d) (hx : ∀ i, x i ∈ cube d (m : ℝ)) :
    (tupleDiscrepancy d m x).totalVariation (cube d (m : ℝ))ᶜ = 0 := by
  simp only [tupleDiscrepancy_totalVariation d m hd x, Measure.add_apply,
    (tupleCounting_compl_eq_zero_iff d (m ^ d) x _ (measurableSet_cube d (m : ℝ))).mpr hx,
    Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
    Set.compl_inter_self, measure_empty, add_zero]

theorem tupleDiscrepancy_compact_support (d m : ℕ) (hd : 0 < d)
    (x : Fin (m ^ d) → Rd d) (hx : ∀ i, x i ∈ cube d (m : ℝ)) :
    ∃ S : Set (Rd d), IsCompact S ∧ (tupleDiscrepancy d m x).totalVariation Sᶜ = 0 := by
  exact ⟨closure (cube d (m : ℝ)), (cube_isBounded d (m : ℝ)).isCompact_closure,
    measure_mono_null (Set.compl_subset_compl.mpr subset_closure)
      (tupleDiscrepancy_concentrated_cube d m hd x hx)⟩

/-- The pointwise discrepancy identity holds almost surely for every balanced tuple law. -/
theorem tupleBalanced_D_q_ae_eq_signedDiscrepancyEnergy (d m : ℕ) (q : ℝ)
    (hd : 0 < d) (hq : 0 ≤ q) (Q : Measure (Fin (m ^ d) → Rd d))
    (hQ : TupleBalancedAdmissible d m Q) :
    (fun x => D_q d q m (tupleCounting d (m ^ d) x)) =ᵐ[Q]
      (fun x => Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x)) := by
  exact hQ.2.1.mono (fun x hx =>
    tuple_D_q_eq_signedDiscrepancyEnergy d m q hd hq x hx.2)

/-- Expected showcase and signed discrepancy energies coincide under a balanced tuple law. -/
theorem tupleBalanced_signed_expectedEnergy_eq (d m : ℕ) (q : ℝ)
    (hd : 0 < d) (hq : 0 ≤ q) (Q : Measure (Fin (m ^ d) → Rd d))
    (hQ : TupleBalancedAdmissible d m Q) :
    (∫ x, D_q d q m (tupleCounting d (m ^ d) x) ∂Q) =
      ∫ x, Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x) ∂Q := by
  exact integral_congr_ae (tupleBalanced_D_q_ae_eq_signedDiscrepancyEnergy d m q hd hq Q hQ)

/-- Signed discrepancy energies are ordinary integrable random variables in the negative branch. -/
theorem tupleBalanced_signedDiscrepancyEnergy_integrable (d m : ℕ) (q : ℝ)
    (hd : 0 < d) (hq : 0 < q) (hq_two : q < 2)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    Integrable (fun x => Riesz.Analysis.signedDiscrepancyEnergy q
      (tupleDiscrepancy d m x)) Q := by
  exact (tupleBalanced_D_q_integrable d m q hq hq_two Q hQ).congr
    (tupleBalanced_D_q_ae_eq_signedDiscrepancyEnergy d m q hd hq.le Q hQ)

/-- The paper's signed finite-volume energy evaluated on balanced distinct-tuple laws. -/
def signedTupleBalancedExpectedEnergies (d : ℕ) (q : ℝ) (m : ℕ) : Set ℝ :=
  {r | ∃ Q : Measure (Fin (m ^ d) → Rd d), TupleBalancedAdmissible d m Q ∧
    (∫ x, Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x) ∂Q) = r}

def signedTupleBalancedInfimum (d : ℕ) (q : ℝ) (m : ℕ) : ℝ :=
  sInf (signedTupleBalancedExpectedEnergies d q m)

/-- Both finite-volume energies have precisely the same set of attainable expectations. -/
theorem tupleBalancedExpectedEnergies_eq_signed (d m : ℕ) (q : ℝ)
    (hd : 0 < d) (hq : 0 ≤ q) :
    tupleBalancedExpectedEnergies d q m = signedTupleBalancedExpectedEnergies d q m := by
  ext r
  constructor
  · rintro ⟨Q, hQ, hE⟩
    exact ⟨Q, hQ, (tupleBalanced_signed_expectedEnergy_eq d m q hd hq Q hQ).symm.trans hE⟩
  · rintro ⟨Q, hQ, hE⟩
    exact ⟨Q, hQ, (tupleBalanced_signed_expectedEnergy_eq d m q hd hq Q hQ).trans hE⟩

/-- Measurable labeling and the signed-energy bridge preserve the showcase energy set exactly. -/
theorem balancedExpectedEnergies_eq_signedTuple (d m : ℕ) (q : ℝ)
    (hd : 0 < d) (hq : 0 < q) :
    balancedExpectedEnergies d q m = signedTupleBalancedExpectedEnergies d q m := by
  exact (balancedExpectedEnergies_eq_tuple d m q hq).trans
    (tupleBalancedExpectedEnergies_eq_signed d m q hd hq.le)

/-- The showcase's finite-volume infimum equals that of signed balanced tuple discrepancies. -/
theorem b_eq_signedTupleBalancedInfimum (d m : ℕ) (q : ℝ)
    (hd : 0 < d) (hq : 0 < q) :
    b d q m = signedTupleBalancedInfimum d q m := by
  exact congrArg sInf (balancedExpectedEnergies_eq_signedTuple d m q hd hq)

/-- The exact finite tuple discrepancy has the paper's Gaussian integral representation. -/
theorem tuple_signedDiscrepancyEnergy_gaussian (d m : ℕ) (q : ℝ)
    (hd : 0 < d) (hq : 0 < q) (hq_two : q < 2)
    (x : Fin (m ^ d) → Rd d) (hx : ∀ i, x i ∈ cube d (m : ℝ)) :
    Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x) =
      gamma_s (-q) * (∫ t : ℝ in Set.Ioi 0, t ^ (-q / 2 - 1) *
        Riesz.Analysis.signedKernelQuadratic
          (fun a b : Rd d => Real.exp (-(t * ‖a - b‖ ^ 2))) (tupleDiscrepancy d m x)) ∧
      0 ≤ Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x) := by
  obtain ⟨S, hcompact, hsupport⟩ := tupleDiscrepancy_compact_support d m hd x hx
  exact Riesz.Analysis.signedDiscrepancyEnergy_gaussian_compact q hq hq_two
    (tupleDiscrepancy d m x) (tupleDiscrepancy_mass_zero d m x) S hcompact hsupport

/-- Near-minimizers of the showcase infimum may be chosen as balanced distinct-tuple laws
with integrable signed discrepancy energy. -/
theorem exists_near_optimal_signed_tuple_law (d m : ℕ) (q ε : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hq : 0 < q) (hq_two : q < 2) (hε : 0 < ε) :
    ∃ Q : Measure (Fin (m ^ d) → Rd d), TupleBalancedAdmissible d m Q ∧
      Integrable (fun x => Riesz.Analysis.signedDiscrepancyEnergy q
        (tupleDiscrepancy d m x)) Q ∧
      b d q m ≤ (∫ x, Riesz.Analysis.signedDiscrepancyEnergy q
        (tupleDiscrepancy d m x) ∂Q) ∧
      (∫ x, Riesz.Analysis.signedDiscrepancyEnergy q
        (tupleDiscrepancy d m x) ∂Q) < b d q m + ε := by
  obtain ⟨P, hP, _, hle, hlt⟩ :=
    exists_near_optimal_balanced_law d m q ε hd hm hq hq_two hε
  obtain ⟨Q, hQ, hmap⟩ := exists_tuple_balanced_law d m P hP
  have hE : (∫ x, Riesz.Analysis.signedDiscrepancyEnergy q
      (tupleDiscrepancy d m x) ∂Q) = ∫ μ, D_q d q m μ ∂P :=
    (tupleBalanced_signed_expectedEnergy_eq d m q hd hq.le Q hQ).symm.trans
      ((tupleBalanced_expectedEnergy_eq d m q hq Q hQ).trans
        (congrArg (fun P => ∫ μ, D_q d q m μ ∂P) hmap))
  exact ⟨Q, hQ, tupleBalanced_signedDiscrepancyEnergy_integrable d m q hd hq hq_two Q hQ,
    hE.symm ▸ hle, hE.symm ▸ hlt⟩

end Riesz.Negative
