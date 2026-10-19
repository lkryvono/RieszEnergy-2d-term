import Riesz.Negative.IndependentCells

/-! Finite independent cell assembly in the showcase's actual configuration-law space.
The geometry of a cube partition and the limiting stationary comparison are separate targets. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

/-- The union counting measure of a finite family of point tuples. -/
def cellFamilyCounting (d J : ℕ) (n : Fin J → ℕ)
    (x : (j : Fin J) → Fin (n j) → Rd d) : Measure (Rd d) :=
  ∑ j, tupleCounting d (n j) (x j)

/-- The same family, indexed by the disjoint union of the cell labels. -/
def cellFamilySites (d J : ℕ) (n : Fin J → ℕ)
    (x : (j : Fin J) → Fin (n j) → Rd d) (a : (j : Fin J) × Fin (n j)) : Rd d :=
  x a.1 a.2

/-- The configuration law obtained by independently sampling the cell laws and taking their union. -/
def cellFamilyCountingLaw (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) : ConfigurationLaw d :=
  Measure.map (cellFamilyCounting d J n) (Measure.pi Q)

theorem measurable_cellFamilyCounting (d J : ℕ) (n : Fin J → ℕ) :
    Measurable (cellFamilyCounting d J n) := by
  exact Finset.measurable_fun_sum _ (fun j _ =>
    (measurable_tupleCounting d (n j)).comp (measurable_pi_apply j))

theorem cellFamilyCounting_univ (d J : ℕ) (n : Fin J → ℕ)
    (x : (j : Fin J) → Fin (n j) → Rd d) :
    cellFamilyCounting d J n x Set.univ = (∑ j, n j : ℕ) := by
  simp only [cellFamilyCounting, Measure.finsetSum_apply, tupleCounting_univ, Nat.cast_sum]

theorem cellFamilySites_injective (d J : ℕ) (n : Fin J → ℕ)
    (x : (j : Fin J) → Fin (n j) → Rd d) (S : Fin J → Set (Rd d))
    (hdisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hx : ∀ j, Function.Injective (x j) ∧ ∀ i, x j i ∈ S j) :
    Function.Injective (cellFamilySites d J n x) := by
  rintro ⟨j, i⟩ ⟨k, l⟩ heq
  by_cases hjk : j = k
  · subst k
    exact congrArg (Sigma.mk j) ((hx j).1 heq)
  · change x j i = x k l at heq
    exact False.elim (Set.disjoint_left.mp (hdisjoint hjk) ((hx j).2 i)
      (heq.symm ▸ (hx k).2 l))

theorem cellFamilyCounting_simple (d J : ℕ) (n : Fin J → ℕ)
    (x : (j : Fin J) → Fin (n j) → Rd d)
    (hx : Function.Injective (cellFamilySites d J n x)) :
    IsSimpleConfiguration d (cellFamilyCounting d J n x) := by
  refine ⟨Set.range (cellFamilySites d J n x),
    fun K _ => (Set.finite_range _).inter_of_left K, ?_⟩
  simpa [Measure.sum_fintype, Function.comp_def, Fintype.sum_sigma,
    cellFamilyCounting, cellFamilySites, tupleCounting] using
    Measure.sum_comp_equiv (Equiv.ofInjective (cellFamilySites d J n x) hx)
      (fun z : Set.range (cellFamilySites d J n x) => Measure.dirac z.val)

theorem cellFamilyCounting_concentrated (d J : ℕ) (n : Fin J → ℕ)
    (x : (j : Fin J) → Fin (n j) → Rd d) (S : Set (Rd d)) (hS : MeasurableSet S)
    (hx : ∀ j i, x j i ∈ S) : cellFamilyCounting d J n x Sᶜ = 0 := by
  rw [cellFamilyCounting, Measure.finsetSum_apply]
  exact Finset.sum_eq_zero (fun j _ =>
    (tupleCounting_compl_eq_zero_iff d (n j) (x j) S hS).mpr (hx j))

theorem cellFamilyCountingLaw_probability (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)] :
    IsProbabilityMeasure (cellFamilyCountingLaw d J n Q) := by
  exact Measure.isProbabilityMeasure_map (measurable_cellFamilyCounting d J n).aemeasurable

theorem cellFamily_joint_good (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)]
    (S : Fin J → Set (Rd d))
    (hQ : ∀ j, ∀ᵐ x ∂Q j, Function.Injective x ∧ ∀ i, x i ∈ S j) :
    ∀ᵐ x ∂Measure.pi Q, ∀ j, Function.Injective (x j) ∧ ∀ i, x j i ∈ S j := by
  exact ae_all_iff.mpr (fun j => ae_of_ae_map (measurable_pi_apply j).aemeasurable
    ((measurePreserving_eval Q j).map_eq.symm ▸ hQ j))

theorem cellFamilyCountingLaw_mean (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)]
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ μ, μ D ∂cellFamilyCountingLaw d J n Q) =
      (∑ j, tupleMeanMeasure d (n j) (Q j)) D := by
  rw [cellFamilyCountingLaw, lintegral_map (Measure.measurable_coe hD)
    (measurable_cellFamilyCounting d J n)]
  simp_rw [cellFamilyCounting, Measure.finsetSum_apply]
  rw [lintegral_finsetSum (f := fun (j : Fin J) (x : (j : Fin J) → Fin (n j) → Rd d) =>
    tupleCounting d (n j) (x j) D) Finset.univ (fun j _ =>
      (Measure.measurable_coe hD).comp ((measurable_tupleCounting d (n j)).comp
        (measurable_pi_apply j)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact ((measurePreserving_eval Q j).lintegral_comp
    ((Measure.measurable_coe hD).comp (measurable_tupleCounting d (n j)))).trans
    (tupleMeanMeasure_apply d (n j) (Q j) D hD).symm

/-- Independent cell assembly preserves the exact showcase balanced predicate.
The hypotheses describe only the finite partition, its point counts and cell means. -/
theorem cellFamilyCountingLaw_balanced (d J m : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d))
    (hprob : ∀ j, IsProbabilityMeasure (Q j)) (S : Fin J → Set (Rd d))
    (hdisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hsub : ∀ j, S j ⊆ cube d (m : ℝ))
    (hQ : ∀ j, ∀ᵐ x ∂Q j, Function.Injective x ∧ ∀ i, x i ∈ S j)
    (hcount : ∑ j, n j = m ^ d)
    (hmean : (∑ j, tupleMeanMeasure d (n j) (Q j)) = volume.restrict (cube d (m : ℝ))) :
    BalancedAdmissible d m (cellFamilyCountingLaw d J n Q) := by
  letI : ∀ j, IsProbabilityMeasure (Q j) := hprob
  have hgood := cellFamily_joint_good d J n Q S hQ
  have hclass : ∀ᵐ μ ∂cellFamilyCountingLaw d J n Q,
      IsSimpleConfiguration d μ ∧ μ Set.univ = (m ^ d : ℕ) :=
    (ae_map_iff (measurable_cellFamilyCounting d J n).aemeasurable
      (measurableSet_simple_fixed_count d (m ^ d))).mpr
      (hgood.mono (fun x hx => ⟨cellFamilyCounting_simple d J n x
        (cellFamilySites_injective d J n x S hdisjoint hx),
        (cellFamilyCounting_univ d J n x).trans (congrArg Nat.cast hcount)⟩))
  have hsupport : ∀ᵐ μ ∂cellFamilyCountingLaw d J n Q, μ (cube d (m : ℝ))ᶜ = 0 :=
    (ae_map_iff (measurable_cellFamilyCounting d J n).aemeasurable
      (measurableSet_eq_fun (Measure.measurable_coe (measurableSet_cube d (m : ℝ)).compl)
        measurable_const)).mpr
      (hgood.mono (fun x hx => cellFamilyCounting_concentrated d J n x _
        (measurableSet_cube d (m : ℝ)) (fun j i => hsub j ((hx j).2 i))))
  refine ⟨cellFamilyCountingLaw_probability d J n Q,
    (hclass.and hsupport).mono (fun _ h => ⟨h.1.1, h.2, h.1.2⟩),
    fun D hD => (cellFamilyCountingLaw_mean d J n Q D hD).trans (congrArg (fun μ => μ D) hmean)⟩

/-- The product sample space has the exact two-cell product marginal for distinct cells. -/
theorem cellFamily_pair_map (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)]
    (i j : Fin J) (hij : i ≠ j) :
    Measure.map (fun x : (j : Fin J) → Fin (n j) → Rd d => (x i, x j)) (Measure.pi Q) =
      (Q i).prod (Q j) := by
  have hIndep := ProbabilityTheory.iIndepFun_pi (μ := Q) (X := fun _ => id)
    (fun _ => aemeasurable_id)
  have hpair := (hIndep.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  simpa only [(measurePreserving_eval Q i).map_eq, (measurePreserving_eval Q j).map_eq]
    using hpair

theorem cellFamily_pair_measurePreserving (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)]
    (i j : Fin J) (hij : i ≠ j) :
    MeasurePreserving (fun x : (j : Fin J) → Fin (n j) → Rd d => (x i, x j))
      (Measure.pi Q) ((Q i).prod (Q j)) := by
  exact ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),
    cellFamily_pair_map d J n Q i j hij⟩

theorem tupleDiscrepancyCross_integrable (d n r : ℕ)
    (Q : Measure (Fin n → Rd d)) (R : Measure (Fin r → Rd d))
    [IsFiniteMeasure Q] [IsFiniteMeasure R] (k : Rd d → Rd d → ℝ)
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleMeanMeasure d n Q).prod (tupleMeanMeasure d r R))) :
    Integrable (tupleDiscrepancyCross d n r (tupleMeanMeasure d n Q) (tupleMeanMeasure d r R) k)
      (Q.prod R) := by
  exact (centeredTupleCross_integrable d n r Q R k hk).congr
    (Filter.Eventually.of_forall (fun z => (tupleDiscrepancyCross_eq_centered d n r Q R k z).symm))

theorem cellFamily_cross_integrable (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)]
    (k : Rd d → Rd d → ℝ) (i j : Fin J) (hij : i ≠ j)
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleMeanMeasure d (n i) (Q i)).prod (tupleMeanMeasure d (n j) (Q j)))) :
    Integrable (fun x => tupleDiscrepancyCross d (n i) (n j)
      (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n j) (Q j))
      k (x i, x j)) (Measure.pi Q) := by
  exact (cellFamily_pair_measurePreserving d J n Q i j hij).integrable_comp_of_integrable
    (tupleDiscrepancyCross_integrable d (n i) (n j) (Q i) (Q j) k hk)

theorem cellFamily_cross_expectation_zero (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)]
    (k : Rd d → Rd d → ℝ) (i j : Fin J) (hij : i ≠ j)
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleMeanMeasure d (n i) (Q i)).prod (tupleMeanMeasure d (n j) (Q j)))) :
    (∫ x, tupleDiscrepancyCross d (n i) (n j)
      (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n j) (Q j))
      k (x i, x j) ∂Measure.pi Q) = 0 := by
  have hc := tupleDiscrepancyCross_integrable d (n i) (n j) (Q i) (Q j) k hk
  have hm := integral_map (μ := Measure.pi Q)
    (φ := fun x : (j : Fin J) → Fin (n j) → Rd d => (x i, x j))
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
    ((cellFamily_pair_map d J n Q i j hij).symm ▸ hc.aestronglyMeasurable)
  rw [cellFamily_pair_map d J n Q i j hij] at hm
  exact hm.symm.trans (expected_tupleDiscrepancyCross_eq_zero d (n i) (n j) (Q i) (Q j) k hk)

theorem cellFamily_self_integrable (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)]
    (k : Rd d → Rd d → ℝ) (i : Fin J)
    (hi : Integrable (fun x => tupleDiscrepancyCross d (n i) (n i)
      (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n i) (Q i)) k (x, x)) (Q i)) :
    Integrable (fun x => tupleDiscrepancyCross d (n i) (n i)
      (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n i) (Q i))
      k (x i, x i)) (Measure.pi Q) := by
  exact (measurePreserving_eval Q i).integrable_comp_of_integrable hi

theorem cellFamily_self_expectation (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)]
    (k : Rd d → Rd d → ℝ) (i : Fin J)
    (hi : Integrable (fun x => tupleDiscrepancyCross d (n i) (n i)
      (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n i) (Q i)) k (x, x)) (Q i)) :
    (∫ x, tupleDiscrepancyCross d (n i) (n i)
      (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n i) (Q i))
      k (x i, x i) ∂Measure.pi Q) =
      ∫ x, tupleDiscrepancyCross d (n i) (n i)
        (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n i) (Q i)) k (x, x) ∂Q i := by
  have hm := integral_map (μ := Measure.pi Q)
    (φ := fun x : (j : Fin J) → Fin (n j) → Rd d => x i) (measurable_pi_apply i).aemeasurable
    ((measurePreserving_eval Q i).map_eq.symm ▸ hi.aestronglyMeasurable)
  simpa only [(measurePreserving_eval Q i).map_eq] using hm.symm

/-- The full expanded discrepancy form contains every ordered pair of cells. -/
def cellFamilyCrossSum (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) (k : Rd d → Rd d → ℝ)
    (x : (j : Fin J) → Fin (n j) → Rd d) : ℝ :=
  ∑ ij : Fin J × Fin J, tupleDiscrepancyCross d (n ij.1) (n ij.2)
    (tupleMeanMeasure d (n ij.1) (Q ij.1)) (tupleMeanMeasure d (n ij.2) (Q ij.2))
    k (x ij.1, x ij.2)

theorem cellFamily_cross_term_integrable (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)]
    (k : Rd d → Rd d → ℝ)
    (hk : ∀ i j, Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleMeanMeasure d (n i) (Q i)).prod (tupleMeanMeasure d (n j) (Q j))))
    (hself : ∀ i, Integrable (fun x => tupleDiscrepancyCross d (n i) (n i)
      (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n i) (Q i)) k (x, x)) (Q i))
    (ij : Fin J × Fin J) :
    Integrable (fun x => tupleDiscrepancyCross d (n ij.1) (n ij.2)
      (tupleMeanMeasure d (n ij.1) (Q ij.1)) (tupleMeanMeasure d (n ij.2) (Q ij.2))
      k (x ij.1, x ij.2)) (Measure.pi Q) := by
  rcases ij with ⟨i, j⟩
  by_cases hij : i = j
  · subst j
    exact cellFamily_self_integrable d J n Q k i (hself i)
  · exact cellFamily_cross_integrable d J n Q k i j hij (hk i j)

/-- Independence removes all off-diagonal cell interactions in expectation. -/
theorem cellFamilyCrossSum_expectation (d J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)]
    (k : Rd d → Rd d → ℝ)
    (hk : ∀ i j, Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleMeanMeasure d (n i) (Q i)).prod (tupleMeanMeasure d (n j) (Q j))))
    (hself : ∀ i, Integrable (fun x => tupleDiscrepancyCross d (n i) (n i)
      (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n i) (Q i)) k (x, x)) (Q i)) :
    (∫ x, cellFamilyCrossSum d J n Q k x ∂Measure.pi Q) =
      ∑ i, ∫ x, tupleDiscrepancyCross d (n i) (n i)
        (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n i) (Q i)) k (x, x) ∂Q i := by
  unfold cellFamilyCrossSum
  rw [integral_finsetSum _
    (fun ij _ => cellFamily_cross_term_integrable d J n Q k hk hself ij), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · exact cellFamily_self_expectation d J n Q k i (hself i)
  · intro j _ hji
    exact cellFamily_cross_expectation_zero d J n Q k i j hji.symm (hk i j)
  · simp

/-- The cross form of two finite discrepancies, written as four product integrals. -/
def finiteDiscrepancyCross (d : ℕ) (k : Rd d → Rd d → ℝ)
    (μ ν ρ σ : Measure (Rd d)) : ℝ :=
  (∫ p : Rd d × Rd d, k p.1 p.2 ∂μ.prod ρ) -
    (∫ p : Rd d × Rd d, k p.1 p.2 ∂μ.prod σ) -
    (∫ p : Rd d × Rd d, k p.1 p.2 ∂ν.prod ρ) +
    ∫ p : Rd d × Rd d, k p.1 p.2 ∂ν.prod σ

theorem integral_prod_cellSum (d J : ℕ) (k : Rd d → Rd d → ℝ)
    (μ ν : Fin J → Measure (Rd d)) [∀ j, IsFiniteMeasure (μ j)] [∀ j, IsFiniteMeasure (ν j)]
    (hk : ∀ i j, Integrable (fun p : Rd d × Rd d => k p.1 p.2) ((μ i).prod (ν j))) :
    (∫ p : Rd d × Rd d, k p.1 p.2 ∂(∑ i, μ i).prod (∑ j, ν j)) =
      ∑ ij : Fin J × Fin J, ∫ p : Rd d × Rd d, k p.1 p.2 ∂(μ ij.1).prod (ν ij.2) := by
  rw [← Measure.sum_fintype, ← Measure.sum_fintype, Measure.prod_sum, Measure.sum_fintype]
  exact integral_finsetSum_measure (fun ij _ => hk ij.1 ij.2)

/-- Finite discrepancy energies expand into the complete ordered cell-pair sum. -/
theorem finiteDiscrepancyCross_cellSum (d J : ℕ) (k : Rd d → Rd d → ℝ)
    (μ ν : Fin J → Measure (Rd d)) [∀ j, IsFiniteMeasure (μ j)] [∀ j, IsFiniteMeasure (ν j)]
    (hμμ : ∀ i j, Integrable (fun p : Rd d × Rd d => k p.1 p.2) ((μ i).prod (μ j)))
    (hμν : ∀ i j, Integrable (fun p : Rd d × Rd d => k p.1 p.2) ((μ i).prod (ν j)))
    (hνμ : ∀ i j, Integrable (fun p : Rd d × Rd d => k p.1 p.2) ((ν i).prod (μ j)))
    (hνν : ∀ i j, Integrable (fun p : Rd d × Rd d => k p.1 p.2) ((ν i).prod (ν j))) :
    finiteDiscrepancyCross d k (∑ i, μ i) (∑ i, ν i) (∑ i, μ i) (∑ i, ν i) =
      ∑ ij : Fin J × Fin J, finiteDiscrepancyCross d k (μ ij.1) (ν ij.1) (μ ij.2) (ν ij.2) := by
  unfold finiteDiscrepancyCross
  rw [integral_prod_cellSum d J k μ μ hμμ, integral_prod_cellSum d J k μ ν hμν,
    integral_prod_cellSum d J k ν μ hνμ, integral_prod_cellSum d J k ν ν hνν]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Product and point-first cross forms agree once the three nonconstant exchanges are integrable. -/
theorem finiteDiscrepancyCross_eq_tuple (d n r : ℕ) (k : Rd d → Rd d → ℝ)
    (x : Fin n → Rd d) (y : Fin r → Rd d) (ν ρ : Measure (Rd d))
    [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    (hxy : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleCounting d n x).prod (tupleCounting d r y)))
    (hxρ : Integrable (fun p : Rd d × Rd d => k p.1 p.2) ((tupleCounting d n x).prod ρ))
    (hνy : Integrable (fun p : Rd d × Rd d => k p.1 p.2) (ν.prod (tupleCounting d r y))) :
    finiteDiscrepancyCross d k (tupleCounting d n x) ν (tupleCounting d r y) ρ =
      tupleDiscrepancyCross d n r ν ρ k (x, y) := by
  letI := tupleCounting_isFiniteMeasure d n x
  letI := tupleCounting_isFiniteMeasure d r y
  unfold finiteDiscrepancyCross tupleDiscrepancyCross
  rw [integral_prod _ hxy, integral_prod _ hxρ, integral_prod_symm _ hνy]

theorem tupleSelfPair_rpow_integrable (d n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (Q : Measure (Fin n → Rd d)) [IsFiniteMeasure Q] (S : Set (Rd d))
    (hbounded : Bornology.IsBounded S)
    (hQ : ∀ᵐ x ∂Q, ∀ i, x i ∈ S) :
    Integrable (fun x => ∑ ij : Fin n × Fin n, ‖x ij.1 - x ij.2‖ ^ q) Q := by
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp hbounded
  refine integrable_finsetSum _ (fun ij _ => ?_)
  refine (integrable_const (L ^ q)).mono'
    (((measurable_pi_apply ij.1).sub (measurable_pi_apply ij.2)).norm.pow_const q).aestronglyMeasurable ?_
  filter_upwards [hQ] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow (norm_nonneg _)
    (dist_eq_norm (x ij.1) (x ij.2) ▸ hL (hx ij.1) (hx ij.2)) hq

/-- Bounded support supplies the diagonal integrability required for cell energy additivity. -/
theorem tupleSelf_rpow_cross_integrable (d n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (Q : Measure (Fin n → Rd d)) [IsFiniteMeasure Q] (S : Set (Rd d))
    (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hQ : ∀ᵐ x ∂Q, ∀ i, x i ∈ S) :
    Integrable (fun x => tupleDiscrepancyCross d n n (tupleMeanMeasure d n Q)
      (tupleMeanMeasure d n Q) (fun a b => ‖a - b‖ ^ q) (x, x)) Q := by
  have hk := independentTuple_rpow_kernel_integrable d n n q hq Q Q S hS hbounded hQ hQ
  simp only [tupleDiscrepancyCross_eq_centered, centeredTupleCross]
  exact (((tupleSelfPair_rpow_integrable d n q hq Q S hbounded hQ).sub
    (tupleMeanMeasure_integrable_sum d n Q (fun a => ∫ b, ‖a - b‖ ^ q ∂tupleMeanMeasure d n Q)
      hk.integral_prod_left)).sub
    (tupleMeanMeasure_integrable_sum d n Q (fun b => ∫ a, ‖a - b‖ ^ q ∂tupleMeanMeasure d n Q)
      hk.integral_prod_right)).add (integrable_const _)

/-- The actual four-integral discrepancy of the union is its complete cell cross sum. -/
theorem cellFamily_rpow_crossSum_eq (d J : ℕ) (n : Fin J → ℕ) (q : ℝ) (hq : 0 ≤ q)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsFiniteMeasure (Q j)]
    (S : Set (Rd d)) (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hQ : ∀ j, ∀ᵐ x ∂Q j, ∀ i, x i ∈ S)
    (x : (j : Fin J) → Fin (n j) → Rd d) (hx : ∀ j i, x j i ∈ S) :
    finiteDiscrepancyCross d (fun a b => ‖a - b‖ ^ q)
      (cellFamilyCounting d J n x) (∑ j, tupleMeanMeasure d (n j) (Q j))
      (cellFamilyCounting d J n x) (∑ j, tupleMeanMeasure d (n j) (Q j)) =
      cellFamilyCrossSum d J n Q (fun a b => ‖a - b‖ ^ q) x := by
  letI : ∀ j : Fin J, IsFiniteMeasure (tupleCounting d (n j) (x j)) :=
    fun j => tupleCounting_isFiniteMeasure d (n j) (x j)
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp hbounded
  have hμ (j : Fin J) : tupleCounting d (n j) (x j) Sᶜ = 0 :=
    (tupleCounting_compl_eq_zero_iff d (n j) (x j) S hS).mpr (hx j)
  have hν (j : Fin J) : tupleMeanMeasure d (n j) (Q j) Sᶜ = 0 :=
    tupleMeanMeasure_concentrated d (n j) (Q j) S hS (hQ j)
  have hInt (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0) :
      Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q) (μ.prod ν) :=
    Riesz.Analysis.integrable_rpow_distance q L hq μ ν
      (Riesz.Analysis.ae_distance_le_of_concentrated μ ν S L hμ hν
        (fun a ha b hb => dist_eq_norm a b ▸ hL ha hb))
  unfold cellFamilyCounting cellFamilyCrossSum
  rw [finiteDiscrepancyCross_cellSum d J _
    (fun j => tupleCounting d (n j) (x j)) (fun j => tupleMeanMeasure d (n j) (Q j))
    (fun i j => hInt _ _ (hμ i) (hμ j)) (fun i j => hInt _ _ (hμ i) (hν j))
    (fun i j => hInt _ _ (hν i) (hμ j)) (fun i j => hInt _ _ (hν i) (hν j))]
  exact Finset.sum_congr rfl (fun ij _ => finiteDiscrepancyCross_eq_tuple d (n ij.1) (n ij.2) _
    (x ij.1) (x ij.2) _ _ (hInt _ _ (hμ ij.1) (hμ ij.2))
    (hInt _ _ (hμ ij.1) (hν ij.2)) (hInt _ _ (hν ij.1) (hμ ij.2)))

theorem D_q_eq_finiteDiscrepancyCross (d m : ℕ) (q : ℝ) (μ : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure (volume.restrict (cube d (m : ℝ)))]
    (hμμ : Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q) (μ.prod μ))
    (hμν : Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q)
      (μ.prod (volume.restrict (cube d (m : ℝ)))))
    (hνν : Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q)
      ((volume.restrict (cube d (m : ℝ))).prod (volume.restrict (cube d (m : ℝ))))) :
    D_q d q m μ = -(1 / q) * finiteDiscrepancyCross d (fun a b => ‖a - b‖ ^ q)
      μ (volume.restrict (cube d (m : ℝ))) μ (volume.restrict (cube d (m : ℝ))) := by
  unfold D_q finiteDiscrepancyCross
  rw [Riesz.Analysis.integral_symmetric_kernel (fun a b : Rd d => ‖a - b‖ ^ q)
    (fun a b => congrArg (fun r : ℝ => r ^ q) (norm_sub_rev a b))
    (volume.restrict (cube d (m : ℝ))) μ]
  rw [integral_prod _ hμμ, integral_prod _ hμν, integral_prod _ hνν]
  ring

/-- The combined showcase energy is exactly the complete finite-cell cross sum. -/
theorem cellFamily_D_q_eq_crossSum (d J m : ℕ) (n : Fin J → ℕ) (q : ℝ) (hq : 0 ≤ q)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsFiniteMeasure (Q j)]
    (hQ : ∀ j, ∀ᵐ x ∂Q j, ∀ i, x i ∈ cube d (m : ℝ))
    (hmean : (∑ j, tupleMeanMeasure d (n j) (Q j)) = volume.restrict (cube d (m : ℝ)))
    (x : (j : Fin J) → Fin (n j) → Rd d) (hx : ∀ j i, x j i ∈ cube d (m : ℝ)) :
    D_q d q m (cellFamilyCounting d J n x) =
      -(1 / q) * cellFamilyCrossSum d J n Q (fun a b => ‖a - b‖ ^ q) x := by
  letI : ∀ j : Fin J, IsFiniteMeasure (tupleCounting d (n j) (x j)) :=
    fun j => tupleCounting_isFiniteMeasure d (n j) (x j)
  letI : IsFiniteMeasure (cellFamilyCounting d J n x) :=
    inferInstanceAs (IsFiniteMeasure (∑ j, tupleCounting d (n j) (x j)))
  letI := cube_background_isFiniteMeasure d m
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp (cube_isBounded d (m : ℝ))
  have hμ := cellFamilyCounting_concentrated d J n x _ (measurableSet_cube d (m : ℝ)) hx
  have hν : (volume.restrict (cube d (m : ℝ))) (cube d (m : ℝ))ᶜ = 0 := by
    simp only [Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
      Set.compl_inter_self, measure_empty]
  have hInt (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (hμ : μ (cube d (m : ℝ))ᶜ = 0) (hν : ν (cube d (m : ℝ))ᶜ = 0) :
      Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q) (μ.prod ν) :=
    Riesz.Analysis.integrable_rpow_distance q L hq μ ν
      (Riesz.Analysis.ae_distance_le_of_concentrated μ ν _ L hμ hν
        (fun a ha b hb => dist_eq_norm a b ▸ hL ha hb))
  rw [D_q_eq_finiteDiscrepancyCross d m q _ (hInt _ _ hμ hμ) (hInt _ _ hμ hν) (hInt _ _ hν hν),
    ← hmean]
  exact congrArg (fun a => -(1 / q) * a) (cellFamily_rpow_crossSum_eq d J n q hq Q
    (cube d (m : ℝ)) (measurableSet_cube d (m : ℝ)) (cube_isBounded d (m : ℝ)) hQ x hx)

/-- The energy of the actual combined configuration law is the sum of the cell self energies.
The cube partition and limiting argument are not hypotheses hidden in this identity. -/
theorem cellFamily_expected_D_q (d J m : ℕ) (n : Fin J → ℕ) (q : ℝ) (hq : 0 < q)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d)) [∀ j, IsProbabilityMeasure (Q j)]
    (hQ : ∀ j, ∀ᵐ x ∂Q j, ∀ i, x i ∈ cube d (m : ℝ))
    (hmean : (∑ j, tupleMeanMeasure d (n j) (Q j)) = volume.restrict (cube d (m : ℝ)))
    (hP : BalancedAdmissible d m (cellFamilyCountingLaw d J n Q)) :
    (∫ μ, D_q d q m μ ∂cellFamilyCountingLaw d J n Q) =
      ∑ i, ∫ x, -(1 / q) * tupleDiscrepancyCross d (n i) (n i)
        (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n i) (Q i))
        (fun a b => ‖a - b‖ ^ q) (x, x) ∂Q i := by
  have hk := fun i j : Fin J => independentTuple_rpow_kernel_integrable d (n i) (n j) q hq.le
    (Q i) (Q j) (cube d (m : ℝ)) (measurableSet_cube d (m : ℝ))
    (cube_isBounded d (m : ℝ)) (hQ i) (hQ j)
  have hself := fun i : Fin J => tupleSelf_rpow_cross_integrable d (n i) q hq.le
    (Q i) (cube d (m : ℝ)) (measurableSet_cube d (m : ℝ))
    (cube_isBounded d (m : ℝ)) (hQ i)
  have hgood : ∀ᵐ x ∂Measure.pi Q, ∀ j i, x j i ∈ cube d (m : ℝ) :=
    ae_all_iff.mpr (fun j => ae_of_ae_map (measurable_pi_apply j).aemeasurable
      ((measurePreserving_eval Q j).map_eq.symm ▸ hQ j))
  rw [cellFamilyCountingLaw, integral_map (measurable_cellFamilyCounting d J n).aemeasurable
    (balanced_D_q_aestronglyMeasurable d m q hq _ hP)]
  rw [integral_congr_ae (hgood.mono (fun x hx =>
    cellFamily_D_q_eq_crossSum d J m n q hq.le Q hQ hmean x hx))]
  simp_rw [integral_const_mul, cellFamilyCrossSum_expectation d J n Q _ hk hself,
    Finset.mul_sum]

/-- A finite independent partition gives an upper bound for the actual balanced infimum.
Concrete cube tiling still requires constructing the supports, counts and volume means below. -/
theorem b_le_cellFamily_self_energies (d J m : ℕ) (n : Fin J → ℕ) (q : ℝ)
    (hq : 0 < q) (hq_two : q < 2)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd d))
    (hprob : ∀ j, IsProbabilityMeasure (Q j)) (S : Fin J → Set (Rd d))
    (hdisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hsub : ∀ j, S j ⊆ cube d (m : ℝ))
    (hQ : ∀ j, ∀ᵐ x ∂Q j, Function.Injective x ∧ ∀ i, x i ∈ S j)
    (hcount : ∑ j, n j = m ^ d)
    (hmean : (∑ j, tupleMeanMeasure d (n j) (Q j)) = volume.restrict (cube d (m : ℝ))) :
    b d q m ≤ ∑ i, ∫ x, -(1 / q) * tupleDiscrepancyCross d (n i) (n i)
      (tupleMeanMeasure d (n i) (Q i)) (tupleMeanMeasure d (n i) (Q i))
      (fun a b => ‖a - b‖ ^ q) (x, x) ∂Q i := by
  letI : ∀ j, IsProbabilityMeasure (Q j) := hprob
  have hP := cellFamilyCountingLaw_balanced d J m n Q hprob S hdisjoint hsub hQ hcount hmean
  exact (b_le_expectedEnergy d m q hq hq_two _ hP).trans_eq
    (cellFamily_expected_D_q d J m n q hq Q
      (fun j => (hQ j).mono (fun x hx i => hsub j (hx.2 i))) hmean hP)

end Riesz.Negative
