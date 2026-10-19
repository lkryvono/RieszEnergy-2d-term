import Riesz.Negative.FiniteCells

/-! Translated finite cell laws and invariance of their discrepancy self energies.
These are inputs to the concrete cube tiling construction. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

/-- Simultaneous translation of every labeled point in a finite tuple. -/
def translateTuple (d n : ℕ) (u : Rd d) : (Fin n → Rd d) ≃ᵐ (Fin n → Rd d) :=
  MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.addLeft u)

@[simp]
theorem translateTuple_apply (d n : ℕ) (u : Rd d) (x : Fin n → Rd d) (i : Fin n) :
    translateTuple d n u x i = u + x i := by
  rfl

/-- The translated tuple law, in the same measurable sample space. -/
def translateTupleLaw (d n : ℕ) (u : Rd d) (Q : Measure (Fin n → Rd d)) :
    Measure (Fin n → Rd d) := Measure.map (translateTuple d n u) Q

/-- The geometric support of a translated half-open cube. -/
def translatedCube (d : ℕ) (L : ℝ) (u : Rd d) : Set (Rd d) :=
  (fun x => u + x) '' cube d L

theorem translatedCube_measurable (d : ℕ) (L : ℝ) (u : Rd d) :
    MeasurableSet (translatedCube d L u) := by
  exact (measurableEmbedding_addLeft u).measurableSet_image.mpr (measurableSet_cube d L)

theorem map_cube_volume_translation (d : ℕ) (L : ℝ) (u : Rd d) :
    Measure.map (fun x => u + x) (volume.restrict (cube d L)) =
      volume.restrict (translatedCube d L u) := by
  have h := (MeasurableEquiv.addLeft u).restrict_map (volume : Measure (Rd d))
    (translatedCube d L u)
  simpa only [MeasurableEquiv.coe_addLeft, map_add_left_eq_self, translatedCube,
    Set.preimage_image_eq _ (add_right_injective u)] using h.symm

theorem tupleMeanMeasure_translateTupleLaw (d n : ℕ) (u : Rd d)
    (Q : Measure (Fin n → Rd d)) :
    tupleMeanMeasure d n (translateTupleLaw d n u Q) =
      Measure.map (fun x => u + x) (tupleMeanMeasure d n Q) := by
  unfold tupleMeanMeasure translateTupleLaw
  rw [Measure.map_finset_sum (measurable_const_add u).aemeasurable]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Measure.map_map (measurable_pi_apply i) (translateTuple d n u).measurable,
    Measure.map_map (measurable_const_add u) (measurable_pi_apply i)]
  rfl

theorem translateTupleLaw_probability (d n : ℕ) (u : Rd d)
    (Q : Measure (Fin n → Rd d)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (translateTupleLaw d n u Q) := by
  exact Measure.isProbabilityMeasure_map (translateTuple d n u).measurable.aemeasurable

theorem translateTupleLaw_good (d n : ℕ) (L : ℝ) (u : Rd d)
    (Q : Measure (Fin n → Rd d))
    (hQ : ∀ᵐ x ∂Q, Function.Injective x ∧ ∀ i, x i ∈ cube d L) :
    ∀ᵐ x ∂translateTupleLaw d n u Q,
      Function.Injective x ∧ ∀ i, x i ∈ translatedCube d L u := by
  apply (translateTuple d n u).measurableEmbedding.ae_map_iff.mpr
  exact hQ.mono (fun x hx => ⟨(add_right_injective u).comp hx.1,
    fun i => ⟨x i, hx.2 i, rfl⟩⟩)

/-- A common translation preserves every distance-power product integral. -/
theorem integral_rpow_translate_prod (d : ℕ) (q : ℝ) (u : Rd d)
    (μ ν : Measure (Rd d)) [SFinite μ] [SFinite ν] :
    (∫ p : Rd d × Rd d, ‖p.1 - p.2‖ ^ q
      ∂(Measure.map (fun a => u + a) μ).prod (Measure.map (fun a => u + a) ν)) =
      ∫ p : Rd d × Rd d, ‖p.1 - p.2‖ ^ q ∂μ.prod ν := by
  rw [Measure.map_prod_map μ ν (measurable_const_add u) (measurable_const_add u)]
  have he : MeasurableEmbedding (Prod.map (fun x : Rd d => u + x) (fun x => u + x)) :=
    ((MeasurableEquiv.addLeft u).prodCongr (MeasurableEquiv.addLeft u)).measurableEmbedding
  simpa only [Prod.map_fst, Prod.map_snd, add_sub_add_left_eq_sub] using
    he.integral_map (μ := μ.prod ν) (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q)

theorem tupleDiscrepancyCross_translate_self (d n : ℕ) (q : ℝ) (u : Rd d)
    (ν : Measure (Rd d)) [IsFiniteMeasure ν] (x : Fin n → Rd d) :
    tupleDiscrepancyCross d n n (Measure.map (fun a => u + a) ν)
      (Measure.map (fun a => u + a) ν) (fun a b => ‖a - b‖ ^ q)
      (translateTuple d n u x, translateTuple d n u x) =
      tupleDiscrepancyCross d n n ν ν (fun a b => ‖a - b‖ ^ q) (x, x) := by
  unfold tupleDiscrepancyCross
  simp only [integral_tupleCounting, translateTuple_apply,
    (measurableEmbedding_addLeft u).integral_map, integral_rpow_translate_prod, add_sub_add_left_eq_sub]

/-- Translating a cell preserves its expected self discrepancy energy. -/
theorem translateTupleLaw_self_energy (d n : ℕ) (q : ℝ) (u : Rd d)
    (Q : Measure (Fin n → Rd d)) [IsFiniteMeasure Q] :
    (∫ x, -(1 / q) * tupleDiscrepancyCross d n n
      (tupleMeanMeasure d n (translateTupleLaw d n u Q))
      (tupleMeanMeasure d n (translateTupleLaw d n u Q))
      (fun a b => ‖a - b‖ ^ q) (x, x) ∂translateTupleLaw d n u Q) =
      ∫ x, -(1 / q) * tupleDiscrepancyCross d n n
        (tupleMeanMeasure d n Q) (tupleMeanMeasure d n Q)
        (fun a b => ‖a - b‖ ^ q) (x, x) ∂Q := by
  rw [tupleMeanMeasure_translateTupleLaw, translateTupleLaw,
    integral_map_equiv (translateTuple d n u)]
  simp only [tupleDiscrepancyCross_translate_self]

theorem tupleBalanced_translated_mean (d m : ℕ) (u : Rd d)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    tupleMeanMeasure d (m ^ d) (translateTupleLaw d (m ^ d) u Q) =
      volume.restrict (translatedCube d (m : ℝ) u) := by
  rw [tupleMeanMeasure_translateTupleLaw, tupleBalanced_tupleMeanMeasure d m Q hQ,
    map_cube_volume_translation]

/-- The single-cell self form is the exact showcase cube energy. -/
theorem tupleBalanced_D_q_eq_self_cross (d m : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q)
    (x : Fin (m ^ d) → Rd d) (hx : ∀ i, x i ∈ cube d (m : ℝ)) :
    D_q d q m (tupleCounting d (m ^ d) x) = -(1 / q) *
      tupleDiscrepancyCross d (m ^ d) (m ^ d) (tupleMeanMeasure d (m ^ d) Q)
        (tupleMeanMeasure d (m ^ d) Q) (fun a b => ‖a - b‖ ^ q) (x, x) := by
  letI : IsProbabilityMeasure Q := hQ.1
  have hmean : (∑ _ : Fin 1, tupleMeanMeasure d (m ^ d) Q) = volume.restrict (cube d (m : ℝ)) := by
    simpa only [Fintype.sum_unique] using tupleBalanced_tupleMeanMeasure d m Q hQ
  simpa only [cellFamilyCounting, cellFamilyCrossSum, Fintype.sum_prod_type, Fintype.sum_unique] using
    cellFamily_D_q_eq_crossSum d 1 m (fun _ => m ^ d) q hq (fun _ => Q)
      (fun _ => hQ.2.1.mono (fun _ h => h.2)) hmean (fun _ => x) (fun _ => hx)

theorem tupleBalanced_translated_self_energy (d m : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (u : Rd d) (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    (∫ x, -(1 / q) * tupleDiscrepancyCross d (m ^ d) (m ^ d)
      (tupleMeanMeasure d (m ^ d) (translateTupleLaw d (m ^ d) u Q))
      (tupleMeanMeasure d (m ^ d) (translateTupleLaw d (m ^ d) u Q))
      (fun a b => ‖a - b‖ ^ q) (x, x) ∂translateTupleLaw d (m ^ d) u Q) =
      ∫ x, D_q d q m (tupleCounting d (m ^ d) x) ∂Q := by
  letI : IsProbabilityMeasure Q := hQ.1
  rw [translateTupleLaw_self_energy]
  exact integral_congr_ae (hQ.2.1.mono (fun x hx =>
    (tupleBalanced_D_q_eq_self_cross d m q hq Q hQ x hx.2).symm))

/-- Near-minimizers can be placed in any translated cube without changing their energy budget. -/
theorem exists_near_optimal_translated_tuple_law (d m : ℕ) (q ε : ℝ) (u : Rd d)
    (hd : 0 < d) (hm : 0 < m) (hq : 0 < q) (hq_two : q < 2) (hε : 0 < ε) :
    ∃ Q : Measure (Fin (m ^ d) → Rd d), IsProbabilityMeasure Q ∧
      (∀ᵐ x ∂Q, Function.Injective x ∧ ∀ i, x i ∈ translatedCube d (m : ℝ) u) ∧
      tupleMeanMeasure d (m ^ d) Q = volume.restrict (translatedCube d (m : ℝ) u) ∧
      (∫ x, -(1 / q) * tupleDiscrepancyCross d (m ^ d) (m ^ d)
        (tupleMeanMeasure d (m ^ d) Q) (tupleMeanMeasure d (m ^ d) Q)
        (fun a b => ‖a - b‖ ^ q) (x, x) ∂Q) < b d q m + ε := by
  obtain ⟨P, hP, _, _, hlt⟩ := exists_near_optimal_balanced_law d m q ε hd hm hq hq_two hε
  obtain ⟨Q, hQ, hmap⟩ := exists_tuple_balanced_law d m P hP
  letI : IsProbabilityMeasure Q := hQ.1
  refine ⟨translateTupleLaw d (m ^ d) u Q, translateTupleLaw_probability _ _ _ _,
    translateTupleLaw_good _ _ _ _ Q hQ.2.1, tupleBalanced_translated_mean d m u Q hQ, ?_⟩
  rw [tupleBalanced_translated_self_energy d m q hq.le u Q hQ,
    tupleBalanced_expectedEnergy_eq d m q hq Q hQ, hmap]
  exact hlt

theorem mem_translatedCube_iff (d : ℕ) (L : ℝ) (u x : Rd d) :
    x ∈ translatedCube d L u ↔ ∀ i, u i ≤ x i ∧ x i < u i + L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ∀ i, u i ≤ u i + y i ∧ u i + y i < u i + L
    exact fun i => ⟨le_add_of_nonneg_right (hy i).1,
      by simpa only [add_comm] using add_lt_add_left (hy i).2 (u i)⟩
  · intro hx
    refine ⟨x - u, ?_, ?_⟩
    · change ∀ i, 0 ≤ x i - u i ∧ x i - u i < L
      exact fun i => ⟨sub_nonneg.mpr (hx i).1,
        sub_lt_iff_lt_add.mpr (by simpa only [add_comm] using (hx i).2)⟩
    · abel_nf

theorem translatedCube_subset_cube (d : ℕ) (L M : ℝ) (u : Rd d)
    (hlo : ∀ i, 0 ≤ u i) (hhi : ∀ i, u i + L ≤ M) :
    translatedCube d L u ⊆ cube d M := by
  intro x hx
  exact fun i => ⟨(hlo i).trans ((mem_translatedCube_iff d L u x).mp hx i).1,
    (((mem_translatedCube_iff d L u x).mp hx i).2).trans_le (hhi i)⟩

/-- Half-open translated cells are genuinely disjoint when separated in one coordinate. -/
theorem translatedCube_disjoint_of_coordinate_separation (d : ℕ) (L K : ℝ) (u v : Rd d)
    (i : Fin d) (hsep : u i + L ≤ v i) :
    Disjoint (translatedCube d L u) (translatedCube d K v) := by
  refine Set.disjoint_left.mpr (fun x hx hy => ?_)
  exact not_lt_of_ge (hsep.trans ((mem_translatedCube_iff d K v x).mp hy i).1)
    ((mem_translatedCube_iff d L u x).mp hx i).2

end Riesz.Negative
