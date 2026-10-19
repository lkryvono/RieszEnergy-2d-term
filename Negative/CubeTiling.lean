import Riesz.Negative.Translations
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic

/-! The concrete balanced cube tiling and the all-integer finite-volume density limit.
Side-m cells cover the integer core; unit cells cover its remainder. The infinite
stationary construction and comparison with the Euclidean infimum remain separate. -/

noncomputable section

open MeasureTheory Filter RieszShowcase
open scoped ENNReal Classical Topology

namespace Riesz.Negative

def gridOrigin (d : ℕ) (L : ℝ) (k : Fin d → ℕ) : Rd d :=
  WithLp.toLp 2 (fun i => L * (k i : ℝ))

def gridCell (d ℓ : ℕ) (L : ℝ) (z : Fin d → Fin ℓ) : Set (Rd d) :=
  translatedCube d L (gridOrigin d L (fun i => (z i : ℕ)))

theorem mem_gridCell_iff (d ℓ : ℕ) (L : ℝ) (z : Fin d → Fin ℓ) (x : Rd d) :
    x ∈ gridCell d ℓ L z ↔ ∀ i, L * (z i : ℕ) ≤ x i ∧ x i < L * (z i : ℕ) + L := by
  exact mem_translatedCube_iff d L _ x

def CubeRemainderIndex (d M m : ℕ) :=
  {z : Fin d → Fin M // ¬ ∀ i, (z i : ℕ) < (M / m) * m}

def CubeTilingIndex (d M m : ℕ) :=
  (Fin d → Fin (M / m)) ⊕ CubeRemainderIndex d M m

instance (d M m : ℕ) : Fintype (CubeRemainderIndex d M m) :=
  inferInstanceAs (Fintype {z : Fin d → Fin M // ¬ ∀ i, (z i : ℕ) < (M / m) * m})

instance (d M m : ℕ) : Fintype (CubeTilingIndex d M m) :=
  inferInstanceAs (Fintype ((Fin d → Fin (M / m)) ⊕ CubeRemainderIndex d M m))

def cubeTilingSide (d M m : ℕ) : CubeTilingIndex d M m → ℕ
  | Sum.inl _ => m
  | Sum.inr _ => 1

def cubeTilingOrigin (d M m : ℕ) : CubeTilingIndex d M m → Rd d
  | Sum.inl z => gridOrigin d (m : ℝ) (fun i => (z i : ℕ))
  | Sum.inr z => gridOrigin d 1 (fun i => (z.val i : ℕ))

def cubeTilingCell (d M m : ℕ) : CubeTilingIndex d M m → Set (Rd d)
  | Sum.inl z => gridCell d (M / m) (m : ℝ) z
  | Sum.inr z => gridCell d M 1 z.val

theorem grid_coordinate_step (L : ℝ) (hL : 0 ≤ L) (a b : ℕ) (hab : a < b) :
    L * (a : ℝ) + L ≤ L * (b : ℝ) := by
  have h : (a : ℝ) + 1 ≤ (b : ℝ) := by
    simpa only [Nat.cast_succ] using (Nat.cast_le (α := ℝ)).mpr (Nat.succ_le_of_lt hab)
  simpa only [mul_add, mul_one] using mul_le_mul_of_nonneg_left h hL

theorem gridCell_subset_cube (d ℓ : ℕ) (L : ℝ) (hL : 0 ≤ L) (z : Fin d → Fin ℓ) :
    gridCell d ℓ L z ⊆ cube d (L * (ℓ : ℝ)) := by
  exact translatedCube_subset_cube d L (L * (ℓ : ℝ)) _
    (fun i => mul_nonneg hL (Nat.cast_nonneg (z i : ℕ)))
    (fun i => grid_coordinate_step L hL (z i : ℕ) ℓ (z i).isLt)

theorem gridCells_pairwise_disjoint (d ℓ : ℕ) (L : ℝ) (hL : 0 < L) :
    Pairwise (fun z w : Fin d → Fin ℓ => Disjoint (gridCell d ℓ L z) (gridCell d ℓ L w)) := by
  intro z w hzw
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hzw
  rcases lt_or_gt_of_ne hi with h | h
  · exact translatedCube_disjoint_of_coordinate_separation d L L _ _ i
      (grid_coordinate_step L hL.le (z i : ℕ) (w i : ℕ) h)
  · exact (translatedCube_disjoint_of_coordinate_separation d L L _ _ i
      (grid_coordinate_step L hL.le (w i : ℕ) (z i : ℕ) h)).symm

theorem exists_grid_coordinate (ℓ : ℕ) (L x : ℝ) (hL : 0 < L)
    (hx : 0 ≤ x) (hxl : x < L * (ℓ : ℝ)) :
    ∃ z : Fin ℓ, L * (z : ℕ) ≤ x ∧ x < L * (z : ℕ) + L := by
  have hdiv : 0 ≤ x / L := div_nonneg hx hL.le
  have hfloor : Nat.floor (x / L) < ℓ := (Nat.floor_lt hdiv).mpr
    ((div_lt_iff₀ hL).mpr (by simpa only [mul_comm] using hxl))
  refine ⟨⟨Nat.floor (x / L), hfloor⟩, ?_, ?_⟩
  · simpa only [mul_comm] using (le_div_iff₀ hL).mp (Nat.floor_le hdiv)
  · simpa only [mul_add, mul_one, mul_comm] using
      (div_lt_iff₀ hL).mp (Nat.lt_floor_add_one (x / L))

theorem gridCells_cover_cube (d ℓ : ℕ) (L : ℝ) (hL : 0 < L) :
    (⋃ z : Fin d → Fin ℓ, gridCell d ℓ L z) = cube d (L * (ℓ : ℝ)) := by
  refine Set.Subset.antisymm (Set.iUnion_subset (gridCell_subset_cube d ℓ L hL.le)) ?_
  intro x hx
  choose z hzlo hzhi using fun i : Fin d => exists_grid_coordinate ℓ L (x i) hL (hx i).1 (hx i).2
  exact Set.mem_iUnion.mpr ⟨z, (mem_gridCell_iff d ℓ L z x).mpr (fun i => ⟨hzlo i, hzhi i⟩)⟩

theorem cube_subset_cube (d : ℕ) (L M : ℝ) (hLM : L ≤ M) : cube d L ⊆ cube d M := by
  exact fun x hx i => ⟨(hx i).1, ((hx i).2).trans_le hLM⟩

theorem cubeTilingCell_subset_cube (d M m : ℕ) (a : CubeTilingIndex d M m) :
    cubeTilingCell d M m a ⊆ cube d (M : ℝ) := by
  cases a with
  | inl z =>
    have hc : (m : ℝ) * ((M / m : ℕ) : ℝ) ≤ (M : ℝ) := by
      simpa only [Nat.cast_mul, mul_comm] using
        (Nat.cast_le (α := ℝ)).mpr (Nat.div_mul_le_self M m)
    exact (gridCell_subset_cube d (M / m) (m : ℝ) (Nat.cast_nonneg m) z).trans
      (cube_subset_cube d _ _ hc)
  | inr z =>
    simpa only [cubeTilingCell, one_mul] using gridCell_subset_cube d M 1 zero_le_one z.val

theorem gridCell_disjoint_remainder (d M m : ℕ) (z : Fin d → Fin (M / m))
    (r : CubeRemainderIndex d M m) :
    Disjoint (gridCell d (M / m) (m : ℝ) z) (gridCell d M 1 r.val) := by
  obtain ⟨i, hi⟩ := not_forall.mp r.property
  have hsep : (m : ℝ) * ((M / m : ℕ) : ℝ) ≤ ((r.val i : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, mul_comm] using (Nat.cast_le (α := ℝ)).mpr (Nat.le_of_not_lt hi)
  refine Set.disjoint_left.mpr (fun x hx hy => ?_)
  exact not_lt_of_ge (hsep.trans (by simpa only [one_mul] using
    ((mem_gridCell_iff d M 1 r.val x).mp hy i).1))
    ((gridCell_subset_cube d (M / m) (m : ℝ) (Nat.cast_nonneg m) z hx i).2)

theorem cubeTilingCells_pairwise_disjoint (d M m : ℕ) (hm : 0 < m) :
    Pairwise (fun a b : CubeTilingIndex d M m =>
      Disjoint (cubeTilingCell d M m a) (cubeTilingCell d M m b)) := by
  rintro (a | a) (b | b) hab
  · exact gridCells_pairwise_disjoint d (M / m) (m : ℝ) (Nat.cast_pos.mpr hm)
      (fun h => hab (congrArg Sum.inl h))
  · exact gridCell_disjoint_remainder d M m a b
  · exact (gridCell_disjoint_remainder d M m b a).symm
  · exact gridCells_pairwise_disjoint d M 1 zero_lt_one
      (fun h => hab (congrArg Sum.inr (Subtype.ext h)))

theorem cubeTilingCells_cover_cube (d M m : ℕ) (hm : 0 < m) :
    (⋃ a : CubeTilingIndex d M m, cubeTilingCell d M m a) = cube d (M : ℝ) := by
  have hcore : (⋃ z : Fin d → Fin (M / m), gridCell d (M / m) (m : ℝ) z) =
      cube d (((M / m) * m : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, mul_comm] using gridCells_cover_cube d (M / m) (m : ℝ)
      (Nat.cast_pos.mpr hm)
  have hunit : (⋃ z : Fin d → Fin M, gridCell d M 1 z) = cube d (M : ℝ) := by
    simpa only [one_mul] using gridCells_cover_cube d M 1 zero_lt_one
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (cubeTilingCell_subset_cube d M m)
  · intro x hx
    by_cases hxc : x ∈ cube d (((M / m) * m : ℕ) : ℝ)
    · obtain ⟨z, hz⟩ := Set.mem_iUnion.mp (hcore.symm ▸ hxc)
      exact Set.mem_iUnion.mpr ⟨Sum.inl z, hz⟩
    · obtain ⟨z, hz⟩ := Set.mem_iUnion.mp (hunit.symm ▸ hx)
      have hzb : ∀ i, (z i : ℕ) ≤ x i ∧ x i < (z i : ℕ) + 1 := by
        simpa only [one_mul] using (mem_gridCell_iff d M 1 z x).mp hz
      have hzout : ¬ ∀ i, (z i : ℕ) < (M / m) * m := by
        intro hzi
        apply hxc
        change ∀ i, 0 ≤ x i ∧ x i < (((M / m) * m : ℕ) : ℝ)
        exact fun i => ⟨(hx i).1, ((hzb i).2).trans_le
          (by simpa only [Nat.cast_succ] using (Nat.cast_le (α := ℝ)).mpr (Nat.succ_le_of_lt (hzi i)))⟩
      exact Set.mem_iUnion.mpr ⟨Sum.inr ⟨z, hzout⟩, hz⟩

/-- The exact finite partition, including every leftover unit cell. -/
theorem cubeTiling_partition (d M m : ℕ) (hm : 0 < m) :
    Pairwise (fun a b : CubeTilingIndex d M m =>
      Disjoint (cubeTilingCell d M m a) (cubeTilingCell d M m b)) ∧
    (⋃ a : CubeTilingIndex d M m, cubeTilingCell d M m a) = cube d (M : ℝ) := by
  exact ⟨cubeTilingCells_pairwise_disjoint d M m hm, cubeTilingCells_cover_cube d M m hm⟩

theorem cubeTilingCell_eq_translatedCube (d M m : ℕ) (a : CubeTilingIndex d M m) :
    cubeTilingCell d M m a =
      translatedCube d (cubeTilingSide d M m a : ℝ) (cubeTilingOrigin d M m a) := by
  cases a <;> simp only [cubeTilingCell, gridCell, cubeTilingSide, cubeTilingOrigin, Nat.cast_one]

theorem cubeTilingCell_measurable (d M m : ℕ) (a : CubeTilingIndex d M m) :
    MeasurableSet (cubeTilingCell d M m a) := by
  exact cubeTilingCell_eq_translatedCube d M m a ▸ translatedCube_measurable d _ _

/-- The mean measures of the concrete cells sum to the exact cube background. -/
theorem cubeTiling_volume_sum (d M m : ℕ) (hm : 0 < m) :
    (∑ a : CubeTilingIndex d M m, volume.restrict (cubeTilingCell d M m a)) =
      volume.restrict (cube d (M : ℝ)) := by
  simpa only [Measure.sum_fintype, cubeTilingCells_cover_cube d M m hm] using
    (Measure.restrict_iUnion (μ := (volume : Measure (Rd d)))
      (cubeTilingCells_pairwise_disjoint d M m hm) (cubeTilingCell_measurable d M m)).symm

theorem volume_translatedCube (d : ℕ) (L : ℝ) (u : Rd d) :
    volume (translatedCube d L u) = (ENNReal.ofReal L) ^ d := by
  have h := congrArg (fun μ : Measure (Rd d) => μ Set.univ) (map_cube_volume_translation d L u)
  simpa only [Measure.map_apply (measurable_const_add u) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ, volume_cube] using h.symm

theorem cubeTilingCell_volume (d M m : ℕ) (a : CubeTilingIndex d M m) :
    volume (cubeTilingCell d M m a) = ((cubeTilingSide d M m a) ^ d : ℕ) := by
  rw [cubeTilingCell_eq_translatedCube, volume_translatedCube]
  simp only [ENNReal.ofReal_natCast, Nat.cast_pow]

theorem cubeTiling_point_count (d M m : ℕ) (hm : 0 < m) :
    (∑ a : CubeTilingIndex d M m, cubeTilingSide d M m a ^ d) = M ^ d := by
  have h := congrArg (fun μ : Measure (Rd d) => μ Set.univ) (cubeTiling_volume_sum d M m hm)
  have hc : ((∑ a : CubeTilingIndex d M m, cubeTilingSide d M m a ^ d : ℕ) : ℝ≥0∞) =
      (M ^ d : ℕ) := by
    simpa only [Measure.finsetSum_apply, Measure.restrict_apply_univ,
      cubeTilingCell_volume, volume_cube, ENNReal.ofReal_natCast, Nat.cast_sum, Nat.cast_pow] using h
  exact_mod_cast hc

theorem cubeTilingSide_pos (d M m : ℕ) (hm : 0 < m) (a : CubeTilingIndex d M m) :
    0 < cubeTilingSide d M m a := by
  cases a <;> simp only [cubeTilingSide, hm, Nat.zero_lt_one]

/-- The number of leftover unit cells is the exact difference of the two cube volumes. -/
theorem cubeTiling_remainder_card (d M m : ℕ) (hm : 0 < m) :
    Fintype.card (CubeRemainderIndex d M m) = M ^ d - ((M / m) * m) ^ d := by
  have h := cubeTiling_point_count d M m hm
  change (∑ a : (Fin d → Fin (M / m)) ⊕ CubeRemainderIndex d M m,
    cubeTilingSide d M m a ^ d) = M ^ d at h
  have hc : ((M / m) * m) ^ d + Fintype.card (CubeRemainderIndex d M m) = M ^ d := by
    simpa only [CubeTilingIndex, Fintype.sum_sum_type, cubeTilingSide,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      smul_eq_mul, one_pow, mul_one, mul_pow] using h
  omega

/-- Cell laws indexed by the concrete tiling, with exactly one point per unit volume. -/
abbrev CubeTilingLawFamily (d M m : ℕ) :=
  (a : CubeTilingIndex d M m) → Measure (Fin (cubeTilingSide d M m a ^ d) → Rd d)

def cubeTilingEquiv (d M m : ℕ) :
    CubeTilingIndex d M m ≃ Fin (Fintype.card (CubeTilingIndex d M m)) :=
  Fintype.equivFin _

/-- The law obtained by independently sampling every main and remainder cell. -/
def cubeTilingLaw (d M m : ℕ) (Q : CubeTilingLawFamily d M m) : ConfigurationLaw d :=
  cellFamilyCountingLaw d (Fintype.card (CubeTilingIndex d M m))
    (fun j => cubeTilingSide d M m ((cubeTilingEquiv d M m).symm j) ^ d)
    (fun j => Q ((cubeTilingEquiv d M m).symm j))

def cubeTilingSelfEnergy (d M m : ℕ) (q : ℝ) (Q : CubeTilingLawFamily d M m)
    (a : CubeTilingIndex d M m) : ℝ :=
  ∫ x, -(1 / q) * tupleDiscrepancyCross d (cubeTilingSide d M m a ^ d)
    (cubeTilingSide d M m a ^ d)
    (tupleMeanMeasure d (cubeTilingSide d M m a ^ d) (Q a))
    (tupleMeanMeasure d (cubeTilingSide d M m a ^ d) (Q a))
    (fun u v => ‖u - v‖ ^ q) (x, x) ∂Q a

theorem cubeTilingLaw_balanced (d M m : ℕ) (hm : 0 < m)
    (Q : CubeTilingLawFamily d M m) (hprob : ∀ a, IsProbabilityMeasure (Q a))
    (hQ : ∀ a, ∀ᵐ x ∂Q a, Function.Injective x ∧ ∀ i, x i ∈ cubeTilingCell d M m a)
    (hmean : ∀ a, tupleMeanMeasure d (cubeTilingSide d M m a ^ d) (Q a) =
      volume.restrict (cubeTilingCell d M m a)) :
    BalancedAdmissible d M (cubeTilingLaw d M m Q) := by
  let e := cubeTilingEquiv d M m
  refine cellFamilyCountingLaw_balanced d (Fintype.card (CubeTilingIndex d M m)) M
    (fun j => cubeTilingSide d M m (e.symm j) ^ d) (fun j => Q (e.symm j))
    (fun j => hprob (e.symm j)) (fun j => cubeTilingCell d M m (e.symm j)) ?_
    (fun j => cubeTilingCell_subset_cube d M m (e.symm j)) (fun j => hQ (e.symm j)) ?_ ?_
  case refine_3 =>
    exact (e.symm.sum_comp (fun a => tupleMeanMeasure d (cubeTilingSide d M m a ^ d) (Q a))).trans
      ((Finset.sum_congr rfl (fun a _ => hmean a)).trans (cubeTiling_volume_sum d M m hm))
  case refine_2 =>
    exact (e.symm.sum_comp (fun a => cubeTilingSide d M m a ^ d)).trans
      (cubeTiling_point_count d M m hm)
  exact fun _ _ hij => cubeTilingCells_pairwise_disjoint d M m hm
    (fun h => hij (e.symm.injective h))

theorem cubeTilingLaw_expectedEnergy (d M m : ℕ) (q : ℝ) (hm : 0 < m) (hq : 0 < q)
    (Q : CubeTilingLawFamily d M m) (hprob : ∀ a, IsProbabilityMeasure (Q a))
    (hQ : ∀ a, ∀ᵐ x ∂Q a, Function.Injective x ∧ ∀ i, x i ∈ cubeTilingCell d M m a)
    (hmean : ∀ a, tupleMeanMeasure d (cubeTilingSide d M m a ^ d) (Q a) =
      volume.restrict (cubeTilingCell d M m a)) :
    (∫ μ, D_q d q M μ ∂cubeTilingLaw d M m Q) =
      ∑ a : CubeTilingIndex d M m, cubeTilingSelfEnergy d M m q Q a := by
  let e := cubeTilingEquiv d M m
  letI : ∀ j : Fin (Fintype.card (CubeTilingIndex d M m)), IsProbabilityMeasure (Q (e.symm j)) :=
    fun j => hprob (e.symm j)
  have hsum : (∑ j : Fin (Fintype.card (CubeTilingIndex d M m)),
      tupleMeanMeasure d (cubeTilingSide d M m (e.symm j) ^ d) (Q (e.symm j))) =
      volume.restrict (cube d (M : ℝ)) :=
    (e.symm.sum_comp (fun a => tupleMeanMeasure d (cubeTilingSide d M m a ^ d) (Q a))).trans
      ((Finset.sum_congr rfl (fun a _ => hmean a)).trans (cubeTiling_volume_sum d M m hm))
  exact (cellFamily_expected_D_q d (Fintype.card (CubeTilingIndex d M m)) M
    (fun j => cubeTilingSide d M m (e.symm j) ^ d) q hq (fun j => Q (e.symm j))
    (fun j => (hQ (e.symm j)).mono (fun x hx i =>
      cubeTilingCell_subset_cube d M m (e.symm j) (hx.2 i))) hsum
    (cubeTilingLaw_balanced d M m hm Q hprob hQ hmean)).trans
      (e.symm.sum_comp (cubeTilingSelfEnergy d M m q Q))

theorem cubeTiling_budget_sum (d M m : ℕ) (hm : 0 < m) (q ε : ℝ) :
    (∑ a : CubeTilingIndex d M m, (b d q (cubeTilingSide d M m a) + ε)) =
      (((M / m) ^ d : ℕ) : ℝ) * (b d q m + ε) +
      ((M ^ d - ((M / m) * m) ^ d : ℕ) : ℝ) * (b d q 1 + ε) := by
  change (∑ a : (Fin d → Fin (M / m)) ⊕ CubeRemainderIndex d M m,
    (b d q (cubeTilingSide d M m a) + ε)) = _
  simp only [Fintype.sum_sum_type, cubeTilingSide, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, cubeTiling_remainder_card d M m hm]

/-- A concrete balanced tiling law exists for every integer cube size, with its energy budget. -/
theorem exists_cubeTiling_law_with_budget (d M m : ℕ) (q ε : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hq : 0 < q) (hq_two : q < 2) (hε : 0 < ε) :
    ∃ Q : CubeTilingLawFamily d M m, BalancedAdmissible d M (cubeTilingLaw d M m Q) ∧
      (∫ μ, D_q d q M μ ∂cubeTilingLaw d M m Q) ≤
        (((M / m) ^ d : ℕ) : ℝ) * (b d q m + ε) +
        ((M ^ d - ((M / m) * m) ^ d : ℕ) : ℝ) * (b d q 1 + ε) := by
  choose Q hprob hQ hmean henergy using fun a : CubeTilingIndex d M m =>
    exists_near_optimal_translated_tuple_law d (cubeTilingSide d M m a) q ε
      (cubeTilingOrigin d M m a) hd (cubeTilingSide_pos d M m hm a) hq hq_two hε
  simp_rw [← cubeTilingCell_eq_translatedCube] at hQ hmean
  refine ⟨Q, cubeTilingLaw_balanced d M m hm Q hprob hQ hmean, ?_⟩
  rw [cubeTilingLaw_expectedEnergy d M m q hm hq Q hprob hQ hmean,
    ← cubeTiling_budget_sum d M m hm q ε]
  exact Finset.sum_le_sum (fun a _ => (henergy a).le)

theorem b_le_cubeTiling_budget (d M m : ℕ) (q ε : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hq : 0 < q) (hq_two : q < 2) (hε : 0 < ε) :
    b d q M ≤ (((M / m) ^ d : ℕ) : ℝ) * (b d q m + ε) +
      ((M ^ d - ((M / m) * m) ^ d : ℕ) : ℝ) * (b d q 1 + ε) := by
  obtain ⟨Q, hQ, henergy⟩ := exists_cubeTiling_law_with_budget d M m q ε hd hm hq hq_two hε
  exact (b_le_expectedEnergy d M q hq hq_two _ hQ).trans henergy

/-- The concrete all-size tiling inequality, with the approximation errors removed. -/
theorem b_cubeTiling_le (d M m : ℕ) (q : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hq : 0 < q) (hq_two : q < 2) :
    b d q M ≤ (((M / m) ^ d : ℕ) : ℝ) * b d q m +
      ((M ^ d - ((M / m) * m) ^ d : ℕ) : ℝ) * b d q 1 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let c : ℝ := (((M / m) ^ d : ℕ) : ℝ) + ((M ^ d - ((M / m) * m) ^ d : ℕ) : ℝ) + 1
  have hc : 0 < c := by positivity
  have h := b_le_cubeTiling_budget d M m q (ε / c) hd hm hq hq_two (div_pos hε hc)
  nlinarith [div_pos hε hc, div_mul_cancel₀ ε hc.ne']

def balancedDensityValues (d : ℕ) (q : ℝ) : Set ℝ :=
  {r | ∃ m : ℕ, 1 ≤ m ∧ r = b d q m / (m : ℝ) ^ d}

theorem balancedDensityValues_nonempty (d : ℕ) (q : ℝ) :
    (balancedDensityValues d q).Nonempty := by
  exact ⟨b d q 1 / ((1 : ℕ) : ℝ) ^ d, 1, le_rfl, rfl⟩

theorem balancedDensityValues_bddBelow (d : ℕ) (q : ℝ) (hq : 0 < q) (hq_two : q < 2) :
    BddBelow (balancedDensityValues d q) := by
  refine ⟨0, ?_⟩
  rintro r ⟨m, _, rfl⟩
  exact div_nonneg (b_nonneg d m q hq hq_two) (by positivity)

theorem cubeTiling_normalized_budget_tendsto (d m : ℕ) (q : ℝ) (hm : 0 < m) :
    Tendsto (fun M : ℕ =>
      ((((M / m) ^ d : ℕ) : ℝ) * b d q m +
        ((M ^ d - ((M / m) * m) ^ d : ℕ) : ℝ) * b d q 1) / (M : ℝ) ^ d)
      atTop (𝓝 (b d q m / (m : ℝ) ^ d)) := by
  have hratio : Tendsto (fun M : ℕ => ((M / m : ℕ) : ℝ) / (M : ℝ))
      atTop (𝓝 (1 / (m : ℝ))) := by
    have h : Tendsto (fun M : ℕ => (1 - ((M % m : ℕ) : ℝ) / (M : ℝ)) / (m : ℝ))
        atTop (𝓝 (1 / (m : ℝ))) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds.sub (tendsto_mod_div_atTop_nhds_zero_nat hm)).div_const (m : ℝ)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
    have hdiv : ((M % m : ℕ) : ℝ) + (m : ℝ) * ((M / m : ℕ) : ℝ) = (M : ℝ) := by
      exact_mod_cast Nat.mod_add_div M m
    field_simp [(Nat.cast_pos.mpr hm : (0 : ℝ) < m).ne', (Nat.cast_pos.mpr hM : (0 : ℝ) < M).ne']
    linarith
  have hbudget : Tendsto (fun M : ℕ =>
      (((M / m : ℕ) : ℝ) / (M : ℝ)) ^ d * b d q m +
        (1 - (((M / m : ℕ) : ℝ) / (M : ℝ)) ^ d * (m : ℝ) ^ d) * b d q 1)
      atTop (𝓝 (b d q m / (m : ℝ) ^ d)) := by
    simpa [div_pow, hm.ne', div_eq_mul_inv, mul_comm] using
      ((hratio.pow d).mul_const (b d q m)).add
        (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
          ((hratio.pow d).mul_const ((m : ℝ) ^ d))).mul_const (b d q 1))
  apply hbudget.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
  rw [Nat.cast_sub (Nat.pow_le_pow_left (Nat.div_mul_le_self M m) d)]
  simp only [Nat.cast_pow, Nat.cast_mul, mul_pow, div_pow]
  field_simp [(pow_pos (Nat.cast_pos.mpr hM : (0 : ℝ) < M) d).ne']

/-- The finite-volume density converges along all integers to the infimum of cube densities.
Identification of this infimum with the stationary Euclidean energy is a separate obligation. -/
theorem balanced_cube_density_limit (d : ℕ) (q : ℝ)
    (hd : 0 < d) (hq : 0 < q) (hq_two : q < 2) :
    Tendsto (fun M : ℕ => b d q M / (M : ℝ) ^ d)
      atTop (𝓝 (sInf {r : ℝ | ∃ m : ℕ, 1 ≤ m ∧ r = b d q m / (m : ℝ) ^ d})) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  case refine_2 =>
    intro a ha
    obtain ⟨r, ⟨m, hm, rfl⟩, hr⟩ :=
      (csInf_lt_iff (balancedDensityValues_bddBelow d q hq hq_two)
        (balancedDensityValues_nonempty d q)).mp ha
    filter_upwards [(cubeTiling_normalized_budget_tendsto d m q hm).eventually (gt_mem_nhds hr)]
      with M hM
    exact (div_le_div_of_nonneg_right (b_cubeTiling_le d M m q hd hm hq hq_two)
      (by positivity)).trans_lt hM
  intro a ha
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  exact ha.trans_le (csInf_le (balancedDensityValues_bddBelow d q hq hq_two) ⟨M, hM, rfl⟩)

theorem balanced_density_inf_bounds (d : ℕ) (q : ℝ) (hq : 0 < q) (hq_two : q < 2) :
    0 ≤ sInf (balancedDensityValues d q) ∧ sInf (balancedDensityValues d q) ≤ b d q 1 := by
  refine ⟨?_, ?_⟩
  · exact le_csInf (balancedDensityValues_nonempty d q) (fun r ⟨m, _, hr⟩ =>
      hr ▸ div_nonneg (b_nonneg d m q hq hq_two) (by positivity))
  · simpa only [Nat.cast_one, one_pow, div_one] using
      csInf_le (balancedDensityValues_bddBelow d q hq hq_two)
        (show b d q 1 / ((1 : ℕ) : ℝ) ^ d ∈ balancedDensityValues d q from ⟨1, le_rfl, rfl⟩)

end Riesz.Negative
