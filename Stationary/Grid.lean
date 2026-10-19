import Riesz.Negative.CubeTiling
import Mathlib.Probability.ProductMeasure
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-! Infinite independent cell configurations for the stationary competitor construction.
The cell law and finite-volume energies are exactly those in the showcase. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Stationary

abbrev GridIndex (d : ℕ) := Fin d → ℤ
abbrev GridMarks (d n : ℕ) := GridIndex d → Fin n → Rd d

def latticeOrigin (d : ℕ) (L : ℝ) (z : GridIndex d) : Rd d :=
  WithLp.toLp 2 (fun i => L * (z i : ℝ))

def latticeCell (d : ℕ) (L : ℝ) (u : Rd d) (z : GridIndex d) : Set (Rd d) :=
  Riesz.Negative.translatedCube d L (u + latticeOrigin d L z)

def gridSites (d n : ℕ) (L : ℝ) (u : Rd d) (x : GridMarks d n)
    (a : GridIndex d × Fin n) : Rd d :=
  u + latticeOrigin d L a.1 + x a.1 a.2

/-- The actual infinite counting measure, with all cell labels included. -/
def gridConfiguration (d n : ℕ) (L : ℝ) (u : Rd d) (x : GridMarks d n) : Measure (Rd d) :=
  Measure.sum (fun a : GridIndex d × Fin n => Measure.dirac (gridSites d n L u x a))

def gridMarksLaw (d n : ℕ) (Q : Measure (Fin n → Rd d)) : Measure (GridMarks d n) :=
  Measure.infinitePi (fun _ : GridIndex d => Q)

def fixedGridLaw (d n : ℕ) (L : ℝ) (u : Rd d) (Q : Measure (Fin n → Rd d)) :
    ConfigurationLaw d := Measure.map (gridConfiguration d n L u) (gridMarksLaw d n Q)

def randomShiftGridLaw (d m : ℕ) (Q : Measure (Fin (m ^ d) → Rd d)) : ConfigurationLaw d :=
  Measure.map (fun p : Rd d × GridMarks d (m ^ d) => gridConfiguration d (m ^ d) (m : ℝ) p.1 p.2)
    ((Riesz.Negative.cubeUniform d m).prod (gridMarksLaw d (m ^ d) Q))

theorem lattice_coordinate_step (L : ℝ) (hL : 0 ≤ L) (a b : ℤ) (hab : a < b) :
    L * (a : ℝ) + L ≤ L * (b : ℝ) := by
  have h : (a : ℝ) + 1 ≤ (b : ℝ) := by
    simpa only [Int.cast_add, Int.cast_one] using (Int.cast_le (R := ℝ)).mpr (Int.add_one_le_of_lt hab)
  simpa only [mul_add, mul_one] using mul_le_mul_of_nonneg_left h hL

theorem latticeCells_pairwise_disjoint (d : ℕ) (L : ℝ) (hL : 0 < L) (u : Rd d) :
    Pairwise (fun z w : GridIndex d => Disjoint (latticeCell d L u z) (latticeCell d L u w)) := by
  intro z w hzw
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hzw
  rcases lt_or_gt_of_ne hi with h | h
  · apply Riesz.Negative.translatedCube_disjoint_of_coordinate_separation d L L _ _ i
    change u i + L * (z i : ℝ) + L ≤ u i + L * (w i : ℝ)
    linarith [lattice_coordinate_step L hL.le (z i) (w i) h]
  · apply Disjoint.symm
    apply Riesz.Negative.translatedCube_disjoint_of_coordinate_separation d L L _ _ i
    change u i + L * (w i : ℝ) + L ≤ u i + L * (z i : ℝ)
    linarith [lattice_coordinate_step L hL.le (w i) (z i) h]

theorem gridSites_mem_cell (d n : ℕ) (L : ℝ) (u : Rd d) (x : GridMarks d n)
    (z : GridIndex d) (i : Fin n) (hx : x z i ∈ cube d L) :
    gridSites d n L u x (z, i) ∈ latticeCell d L u z := by
  exact ⟨x z i, hx, rfl⟩

theorem gridSites_injective (d n : ℕ) (L : ℝ) (hL : 0 < L) (u : Rd d) (x : GridMarks d n)
    (hx : ∀ z, Function.Injective (x z) ∧ ∀ i, x z i ∈ cube d L) :
    Function.Injective (gridSites d n L u x) := by
  rintro ⟨z, i⟩ ⟨w, j⟩ heq
  by_cases hzw : z = w
  case neg =>
    exact False.elim (Set.disjoint_left.mp (latticeCells_pairwise_disjoint d L hL u hzw)
      (gridSites_mem_cell d n L u x z i ((hx z).2 i))
      (heq.symm ▸ gridSites_mem_cell d n L u x w j ((hx w).2 j)))
  subst w
  exact congrArg (Prod.mk z) ((hx z).1 ((add_right_injective (u + latticeOrigin d L z)) heq))

theorem gridIndex_bounds_of_site_bound (d n : ℕ) (L : ℝ) (hL : 0 < L) (u : Rd d)
    (x : GridMarks d n) (hx : ∀ z i, x z i ∈ cube d L) (R : ℝ) (a : GridIndex d × Fin n)
    (ha : ‖gridSites d n L u x a‖ ≤ R) :
    ∀ i, Int.floor ((-R - u i - L) / L) ≤ a.1 i ∧
      a.1 i ≤ Int.ceil ((R - u i) / L) := by
  intro i
  have hc : |(gridSites d n L u x a) i| ≤ R := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (gridSites d n L u x a) i).trans ha
  change |u i + L * (a.1 i : ℝ) + x a.1 a.2 i| ≤ R at hc
  have hlo : (-R - u i - L) / L ≤ (a.1 i : ℝ) :=
    (div_le_iff₀ hL).mpr (by linarith [(abs_le.mp hc).1, (hx a.1 a.2 i).2])
  have hhi : (a.1 i : ℝ) ≤ (R - u i) / L :=
    (le_div_iff₀ hL).mpr (by linarith [(abs_le.mp hc).2, (hx a.1 a.2 i).1])
  exact ⟨Int.cast_le.mp ((Int.floor_le _).trans hlo),
    Int.cast_le.mp (hhi.trans (Int.le_ceil _))⟩

theorem gridSites_locallyFinite (d n : ℕ) (L : ℝ) (hL : 0 < L) (u : Rd d) (x : GridMarks d n)
    (hx : ∀ z i, x z i ∈ cube d L) :
    ∀ K : Set (Rd d), IsCompact K → (Set.range (gridSites d n L u x) ∩ K).Finite := by
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let T : Set (GridIndex d) := {z | ∀ i, z i ∈
    Set.Icc (Int.floor ((-R - u i - L) / L)) (Int.ceil ((R - u i) / L))}
  have hT : T.Finite := Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  refine ((hT.prod (Set.finite_univ : (Set.univ : Set (Fin n)).Finite)).image
    (gridSites d n L u x)).subset ?_
  rintro y ⟨⟨a, rfl⟩, hy⟩
  exact ⟨a, ⟨gridIndex_bounds_of_site_bound d n L hL u x hx R a (hR _ hy), Set.mem_univ _⟩, rfl⟩

/-- An infinite cell filling with distinct points in each cell is a simple configuration. -/
theorem gridConfiguration_simple (d n : ℕ) (L : ℝ) (hL : 0 < L) (u : Rd d) (x : GridMarks d n)
    (hx : ∀ z, Function.Injective (x z) ∧ ∀ i, x z i ∈ cube d L) :
    IsSimpleConfiguration d (gridConfiguration d n L u x) := by
  refine ⟨Set.range (gridSites d n L u x),
    gridSites_locallyFinite d n L hL u x (fun z => (hx z).2), ?_⟩
  exact Measure.sum_comp_equiv
    (Equiv.ofInjective (gridSites d n L u x) (gridSites_injective d n L hL u x hx))
    (fun y : Set.range (gridSites d n L u x) => Measure.dirac y.val)

theorem exists_lattice_coordinate (L x : ℝ) (hL : 0 < L) :
    ∃ z : ℤ, L * (z : ℝ) ≤ x ∧ x < L * (z : ℝ) + L := by
  refine ⟨Int.floor (x / L), ?_, ?_⟩
  case refine_2 =>
    simpa only [mul_add, mul_one, mul_comm] using
      (div_lt_iff₀ hL).mp (Int.lt_floor_add_one (x / L))
  simpa only [mul_comm] using (le_div_iff₀ hL).mp (Int.floor_le (x / L))

theorem latticeCells_cover (d : ℕ) (L : ℝ) (hL : 0 < L) (u : Rd d) :
    (⋃ z : GridIndex d, latticeCell d L u z) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro p
  choose z hlo hhi using fun i : Fin d => exists_lattice_coordinate L (p i - u i) hL
  refine Set.mem_iUnion.mpr ⟨z,
    (Riesz.Negative.mem_translatedCube_iff d L (u + latticeOrigin d L z) p).mpr ?_⟩
  change ∀ i, u i + L * (z i : ℝ) ≤ p i ∧ p i < u i + L * (z i : ℝ) + L
  exact fun i => ⟨by linarith [hlo i], by linarith [hhi i]⟩

theorem measurable_gridSites (d n : ℕ) (L : ℝ) (a : GridIndex d × Fin n) :
    Measurable (fun p : Rd d × GridMarks d n => gridSites d n L p.1 p.2 a) := by
  exact (measurable_fst.add_const (latticeOrigin d L a.1)).add
    ((measurable_pi_apply a.2).comp ((measurable_pi_apply a.1).comp measurable_snd))

theorem measurable_gridConfiguration (d n : ℕ) (L : ℝ) :
    Measurable (fun p : Rd d × GridMarks d n => gridConfiguration d n L p.1 p.2) := by
  refine Measure.measurable_of_measurable_coe _ (fun D hD => ?_)
  simp only [gridConfiguration, Measure.sum_apply _ hD]
  exact Measurable.tsum (fun a => (Measure.measurable_coe hD).comp
    (Measure.measurable_dirac.comp (measurable_gridSites d n L a)))

theorem measurable_fixedGridConfiguration (d n : ℕ) (L : ℝ) (u : Rd d) :
    Measurable (gridConfiguration d n L u) := by
  simpa only [Function.comp_def, id_eq] using (measurable_gridConfiguration d n L).comp
    ((measurable_const : Measurable (fun _ : GridMarks d n => u)).prodMk measurable_id)

theorem gridMarksLaw_probability (d n : ℕ) (Q : Measure (Fin n → Rd d)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (gridMarksLaw d n Q) := by
  exact inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : GridIndex d => Q)))

theorem fixedGridLaw_probability (d n : ℕ) (L : ℝ) (u : Rd d)
    (Q : Measure (Fin n → Rd d)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (fixedGridLaw d n L u Q) := by
  letI := gridMarksLaw_probability d n Q
  exact Measure.isProbabilityMeasure_map (measurable_fixedGridConfiguration d n L u).aemeasurable

theorem randomShiftGridLaw_probability (d m : ℕ) (hm : 0 < m)
    (Q : Measure (Fin (m ^ d) → Rd d)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (randomShiftGridLaw d m Q) := by
  letI := gridMarksLaw_probability d (m ^ d) Q
  letI := Riesz.Negative.cubeUniform_probability d m hm
  exact Measure.isProbabilityMeasure_map (measurable_gridConfiguration d (m ^ d) (m : ℝ)).aemeasurable

theorem gridMarksLaw_good (d n : ℕ) (L : ℝ) (Q : Measure (Fin n → Rd d))
    [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, Function.Injective x ∧ ∀ i, x i ∈ cube d L) :
    ∀ᵐ x ∂gridMarksLaw d n Q, ∀ z, Function.Injective (x z) ∧ ∀ i, x z i ∈ cube d L := by
  exact ae_all_iff.mpr (fun z => ae_of_ae_map (measurable_pi_apply z).aemeasurable
    ((measurePreserving_eval_infinitePi (fun _ : GridIndex d => Q) z).map_eq.symm ▸ hQ))

theorem gridMarksLaw_ae_simple_configuration (d n : ℕ) (L : ℝ) (hL : 0 < L) (u : Rd d)
    (Q : Measure (Fin n → Rd d)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, Function.Injective x ∧ ∀ i, x i ∈ cube d L) :
    ∀ᵐ x ∂gridMarksLaw d n Q, IsSimpleConfiguration d (gridConfiguration d n L u x) := by
  exact (gridMarksLaw_good d n L Q hQ).mono (fun x hx => gridConfiguration_simple d n L hL u x hx)

theorem latticeCell_measurable (d : ℕ) (L : ℝ) (u : Rd d) (z : GridIndex d) :
    MeasurableSet (latticeCell d L u z) := by
  exact Riesz.Negative.translatedCube_measurable d L _

theorem latticeCells_volume_sum (d : ℕ) (L : ℝ) (hL : 0 < L) (u : Rd d) :
    Measure.sum (fun z : GridIndex d => volume.restrict (latticeCell d L u z)) = volume := by
  simpa only [latticeCells_cover d L hL u, Measure.restrict_univ] using
    (Measure.restrict_iUnion (μ := (volume : Measure (Rd d)))
      (latticeCells_pairwise_disjoint d L hL u) (latticeCell_measurable d L u)).symm

theorem gridConfiguration_count_eq_tsum (d n : ℕ) (L : ℝ) (u : Rd d) (x : GridMarks d n)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    gridConfiguration d n L u x D = ∑' z : GridIndex d,
      Riesz.Negative.tupleCounting d n (fun i => u + latticeOrigin d L z + x z i) D := by
  simp only [gridConfiguration, Measure.sum_apply _ hD, ENNReal.tsum_prod', tsum_fintype,
    Riesz.Negative.tupleCounting, Measure.finsetSum_apply, gridSites]

theorem translatedTuple_count_mean (d m : ℕ) (v : Rd d)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ x, Riesz.Negative.tupleCounting d (m ^ d) (fun i => v + x i) D ∂Q) =
      (volume.restrict (Riesz.Negative.translatedCube d (m : ℝ) v)) D := by
  have h := Riesz.Negative.tupleMeanMeasure_apply d (m ^ d)
    (Riesz.Negative.translateTupleLaw d (m ^ d) v Q) D hD
  rw [Riesz.Negative.tupleBalanced_translated_mean d m v Q hQ,
    Riesz.Negative.translateTupleLaw, lintegral_map
      (f := fun x => Riesz.Negative.tupleCounting d (m ^ d) x D)
      ((Measure.measurable_coe hD).comp (Riesz.Negative.measurable_tupleCounting d (m ^ d)))
      (Riesz.Negative.translateTuple d (m ^ d) v).measurable] at h
  exact h.symm

theorem gridMarksLaw_cell_count_mean (d m : ℕ) (u : Rd d)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q)
    (z : GridIndex d) (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ x : GridMarks d (m ^ d), Riesz.Negative.tupleCounting d (m ^ d)
      (fun i => u + latticeOrigin d (m : ℝ) z + x z i) D ∂gridMarksLaw d (m ^ d) Q) =
      (volume.restrict (latticeCell d (m : ℝ) u z)) D := by
  letI : IsProbabilityMeasure Q := hQ.1
  exact ((measurePreserving_eval_infinitePi (fun _ : GridIndex d => Q) z).lintegral_comp
    (f := fun y => Riesz.Negative.tupleCounting d (m ^ d)
      (fun i => u + latticeOrigin d (m : ℝ) z + y i) D)
    ((Measure.measurable_coe hD).comp ((Riesz.Negative.measurable_tupleCounting d (m ^ d)).comp
      (Riesz.Negative.translateTuple d (m ^ d) (u + latticeOrigin d (m : ℝ) z)).measurable))).trans
        (translatedTuple_count_mean d m _ Q hQ D hD)

/-- The infinite fixed-origin grid law has exact Lebesgue intensity, for every Borel set. -/
theorem fixedGridLaw_mean (d m : ℕ) (hm : 0 < m) (u : Rd d)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ μ, μ D ∂fixedGridLaw d (m ^ d) (m : ℝ) u Q) = volume D := by
  rw [fixedGridLaw, lintegral_map (Measure.measurable_coe hD)
    (measurable_fixedGridConfiguration d (m ^ d) (m : ℝ) u)]
  simp_rw [gridConfiguration_count_eq_tsum d (m ^ d) (m : ℝ) u _ D hD]
  rw [lintegral_tsum (f := fun (z : GridIndex d) (x : GridMarks d (m ^ d)) =>
      Riesz.Negative.tupleCounting d (m ^ d)
        (fun i => u + latticeOrigin d (m : ℝ) z + x z i) D)
    (fun z => ((Measure.measurable_coe hD).comp
      ((Riesz.Negative.measurable_tupleCounting d (m ^ d)).comp
        ((Riesz.Negative.translateTuple d (m ^ d) (u + latticeOrigin d (m : ℝ) z)).measurable.comp
          (measurable_pi_apply z)))).aemeasurable)]
  simp_rw [gridMarksLaw_cell_count_mean d m u Q hQ _ D hD]
  rw [← Measure.sum_apply _ hD, latticeCells_volume_sum d (m : ℝ) (Nat.cast_pos.mpr hm) u]

theorem gridMarksLaw_configuration_mean (d m : ℕ) (hm : 0 < m) (u : Rd d)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ x, gridConfiguration d (m ^ d) (m : ℝ) u x D ∂gridMarksLaw d (m ^ d) Q) = volume D := by
  rw [← lintegral_map (Measure.measurable_coe hD) (measurable_fixedGridConfiguration d (m ^ d) (m : ℝ) u)]
  exact fixedGridLaw_mean d m hm u Q hQ D hD

/-- Randomizing the grid origin retains exact intensity one. -/
theorem randomShiftGridLaw_mean (d m : ℕ) (hm : 0 < m)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ μ, μ D ∂randomShiftGridLaw d m Q) = volume D := by
  letI : IsProbabilityMeasure Q := hQ.1
  letI := gridMarksLaw_probability d (m ^ d) Q
  letI := Riesz.Negative.cubeUniform_probability d m hm
  rw [randomShiftGridLaw, lintegral_map (Measure.measurable_coe hD)
    (measurable_gridConfiguration d (m ^ d) (m : ℝ)),
    lintegral_prod (fun p : Rd d × GridMarks d (m ^ d) =>
      gridConfiguration d (m ^ d) (m : ℝ) p.1 p.2 D) (((Measure.measurable_coe hD).comp
      (measurable_gridConfiguration d (m ^ d) (m : ℝ))).aemeasurable)]
  simp_rw [gridMarksLaw_configuration_mean d m hm _ Q hQ D hD]
  simp

/-- Lattice translations reindex the independently marked cells. -/
def gridReindex (d n : ℕ) (k : GridIndex d) : GridMarks d n ≃ᵐ GridMarks d n :=
  MeasurableEquiv.piCongrLeft (fun _ : GridIndex d => Fin n → Rd d) (Equiv.addRight k)

theorem latticeOrigin_add (d : ℕ) (L : ℝ) (z k : GridIndex d) :
    latticeOrigin d L (z + k) = latticeOrigin d L z + latticeOrigin d L k := by
  ext i
  simp [latticeOrigin, Int.cast_add, mul_add]

theorem gridReindex_apply_add (d n : ℕ) (k z : GridIndex d) (x : GridMarks d n) :
    gridReindex d n k x (z + k) = x z := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : GridIndex d => Fin n → Rd d)
    (Equiv.addRight k) x z

theorem gridConfiguration_lattice_shift (d n : ℕ) (L : ℝ) (u : Rd d)
    (k : GridIndex d) (x : GridMarks d n) :
    gridConfiguration d n L (u + latticeOrigin d L k) x =
      gridConfiguration d n L u (gridReindex d n k x) := by
  have h := Measure.sum_comp_equiv
    ((Equiv.addRight k).prodCongr (Equiv.refl (Fin n)))
    (fun a : GridIndex d × Fin n => Measure.dirac (gridSites d n L u (gridReindex d n k x) a))
  simpa only [gridConfiguration, Function.comp_def, gridSites, Equiv.prodCongr_apply,
    Equiv.coe_addRight, Prod.map_fst, Prod.map_snd, Equiv.refl_apply,
    gridReindex_apply_add, latticeOrigin_add,
    add_assoc, add_left_comm] using h

theorem gridMarksLaw_reindex (d n : ℕ) (k : GridIndex d)
    (Q : Measure (Fin n → Rd d)) [IsProbabilityMeasure Q] :
    Measure.map (gridReindex d n k) (gridMarksLaw d n Q) = gridMarksLaw d n Q := by
  exact Measure.infinitePi_map_piCongrLeft (fun _ : GridIndex d => Q) (Equiv.addRight k)

theorem fixedGridLaw_lattice_periodic (d n : ℕ) (L : ℝ) (u : Rd d)
    (k : GridIndex d) (Q : Measure (Fin n → Rd d)) [IsProbabilityMeasure Q] :
    fixedGridLaw d n L (u + latticeOrigin d L k) Q = fixedGridLaw d n L u Q := by
  have heq : gridConfiguration d n L (u + latticeOrigin d L k) =
      gridConfiguration d n L u ∘ gridReindex d n k :=
    funext (gridConfiguration_lattice_shift d n L u k)
  rw [fixedGridLaw, heq, ← Measure.map_map (measurable_fixedGridConfiguration d n L u)
    (gridReindex d n k).measurable, gridMarksLaw_reindex d n k Q]
  rfl

theorem gridConfiguration_translate (d n : ℕ) (L : ℝ) (u a : Rd d) (x : GridMarks d n) :
    Measure.map (fun y : Rd d => a + y) (gridConfiguration d n L u x) =
      gridConfiguration d n L (u + a) x := by
  simp only [gridConfiguration, Measure.map_sum (measurable_const_add a).aemeasurable,
    Measure.map_dirac' (measurable_const_add a), gridSites, add_assoc, add_left_comm]

theorem fixedGridLaw_translate (d n : ℕ) (L : ℝ) (u a : Rd d)
    (Q : Measure (Fin n → Rd d)) :
    Measure.map (fun μ : Measure (Rd d) => Measure.map (fun y : Rd d => a + y) μ)
      (fixedGridLaw d n L u Q) = fixedGridLaw d n L (u + a) Q := by
  have heq : (fun μ : Measure (Rd d) => Measure.map (fun y : Rd d => a + y) μ) ∘
      gridConfiguration d n L u = gridConfiguration d n L (u + a) :=
    funext (gridConfiguration_translate d n L u a)
  rw [fixedGridLaw, Measure.map_map (Measure.measurable_map _ (measurable_const_add a))
    (measurable_fixedGridConfiguration d n L u), heq]
  rfl

theorem randomShiftGridLaw_apply (d m : ℕ)
    (Q : Measure (Fin (m ^ d) → Rd d)) [IsProbabilityMeasure Q]
    (S : Set (Measure (Rd d))) (hS : MeasurableSet S) :
    randomShiftGridLaw d m Q S =
      ∫⁻ u, fixedGridLaw d (m ^ d) (m : ℝ) u Q S ∂Riesz.Negative.cubeUniform d m := by
  letI := gridMarksLaw_probability d (m ^ d) Q
  rw [randomShiftGridLaw, Measure.map_apply (measurable_gridConfiguration d (m ^ d) (m : ℝ)) hS,
    Measure.prod_apply ((measurable_gridConfiguration d (m ^ d) (m : ℝ)) hS)]
  simp only [fixedGridLaw, Measure.map_apply (measurable_fixedGridConfiguration d (m ^ d) (m : ℝ) _) hS,
    Set.preimage_preimage]

def latticeOriginHom (d : ℕ) (L : ℝ) : GridIndex d →+ Rd d where
  toFun := latticeOrigin d L
  map_zero' := by simp [latticeOrigin, Pi.zero_def]
  map_add' := latticeOrigin_add d L

def latticeGroup (d : ℕ) (L : ℝ) : AddSubgroup (Rd d) := (latticeOriginHom d L).range

instance latticeGroup_countable (d : ℕ) (L : ℝ) : Countable (latticeGroup d L) :=
  (AddMonoidHom.rangeRestrict_surjective (latticeOriginHom d L)).countable

theorem cube_lattice_fundamentalDomain (d : ℕ) (L : ℝ) (hL : 0 < L) :
    IsAddFundamentalDomain (latticeGroup d L) (cube d L) (volume : Measure (Rd d)) := by
  have hcover : ∀ x : Rd d, ∃ g : latticeGroup d L, g +ᵥ x ∈ cube d L := by
    intro x
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp ((latticeCells_cover d L hL 0).symm ▸ Set.mem_univ x)
    rcases hz with ⟨y, hy, rfl⟩
    refine ⟨-(latticeOriginHom d L).rangeRestrict z, ?_⟩
    change -latticeOrigin d L z + (0 + latticeOrigin d L z + y) ∈ cube d L
    simpa only [zero_add, neg_add_cancel_left] using hy
  refine ⟨(Riesz.Negative.measurableSet_cube d L).nullMeasurableSet,
    Filter.Eventually.of_forall hcover, ?_⟩
  rintro ⟨v, z, rfl⟩ ⟨w, k, rfl⟩ hzk
  have hne : z ≠ k := fun h => hzk (Subtype.ext (congrArg (latticeOriginHom d L) h))
  change AEDisjoint volume ((fun x : Rd d => latticeOrigin d L z + x) '' cube d L)
    ((fun x : Rd d => latticeOrigin d L k + x) '' cube d L)
  simpa only [latticeCell, Riesz.Negative.translatedCube, zero_add] using
    (latticeCells_pairwise_disjoint d L hL 0 hne).aedisjoint

theorem periodic_cube_lintegral_translate (d : ℕ) (L : ℝ) (hL : 0 < L)
    (f : Rd d → ℝ≥0∞) (hf : ∀ (k : GridIndex d) (u : Rd d),
      f (u + latticeOrigin d L k) = f u) (a : Rd d) :
    (∫⁻ u in cube d L, f (u + a)) = ∫⁻ u in cube d L, f u := by
  have hfd := cube_lattice_fundamentalDomain d L hL
  have ht := hfd.vadd_of_comm a
  have hf' : ∀ (g : latticeGroup d L) (u : Rd d), f (g +ᵥ u) = f u := by
    rintro ⟨v, k, rfl⟩ u
    simpa [latticeOriginHom, add_comm] using hf k u
  have hchange := (measurePreserving_add_left (volume : Measure (Rd d)) a).setLIntegral_comp_emb
    (measurableEmbedding_addLeft a) f (cube d L)
  simpa only [add_comm a] using hchange.trans (hfd.setLIntegral_eq ht f hf').symm

theorem phaseAverage_shift (d m : ℕ) (hm : 0 < m)
    (Q : Measure (Fin (m ^ d) → Rd d)) [IsProbabilityMeasure Q]
    (S : Set (Measure (Rd d))) (_hS : MeasurableSet S) (a : Rd d) :
    (∫⁻ u, fixedGridLaw d (m ^ d) (m : ℝ) (u + a) Q S ∂Riesz.Negative.cubeUniform d m) =
      ∫⁻ u, fixedGridLaw d (m ^ d) (m : ℝ) u Q S ∂Riesz.Negative.cubeUniform d m := by
  simp only [Riesz.Negative.cubeUniform, lintegral_smul_measure, smul_eq_mul]
  exact congrArg (fun r : ℝ≥0∞ => ((m : ℝ≥0∞) ^ d)⁻¹ * r)
    (periodic_cube_lintegral_translate d (m : ℝ) (Nat.cast_pos.mpr hm)
      (fun u => fixedGridLaw d (m ^ d) (m : ℝ) u Q S)
      (fun k u => congrArg (fun P : ConfigurationLaw d => P S)
        (fixedGridLaw_lattice_periodic d (m ^ d) (m : ℝ) u k Q)) a)

/-- The randomized law is invariant under every Euclidean translation. -/
theorem randomShiftGridLaw_stationary (d m : ℕ) (hm : 0 < m)
    (Q : Measure (Fin (m ^ d) → Rd d)) [IsProbabilityMeasure Q] :
    IsStationary d (randomShiftGridLaw d m Q) := by
  intro a
  ext S hS : 1
  rw [Measure.map_apply (Measure.measurable_map _ (measurable_const_add a)) hS,
    randomShiftGridLaw_apply d m Q _
      ((Measure.measurable_map _ (measurable_const_add a)) hS),
    randomShiftGridLaw_apply d m Q S hS]
  simp_rw [← Measure.map_apply (Measure.measurable_map _ (measurable_const_add a)) hS,
    fixedGridLaw_translate d (m ^ d) (m : ℝ) _ a Q]
  exact phaseAverage_shift d m hm Q S hS a

theorem gridConfiguration_count_le (d n : ℕ) (L : ℝ) (u : Rd d) (x : GridMarks d n)
    (D : Set (Rd d)) (hD : MeasurableSet D) (T : Finset (GridIndex d))
    (hT : ∀ a : GridIndex d × Fin n, gridSites d n L u x a ∈ D → a.1 ∈ T) :
    gridConfiguration d n L u x D ≤ (T.card * n : ℕ) := by
  simp only [gridConfiguration, Measure.sum_apply _ hD]
  have hzero : ∀ a ∉ T ×ˢ (Finset.univ : Finset (Fin n)),
      (Measure.dirac (gridSites d n L u x a)) D = 0 := by
    intro a ha
    exact (Measure.dirac_apply' _ hD).trans (Set.indicator_of_notMem
      (fun h => ha (Finset.mem_product.mpr ⟨hT a h, Finset.mem_univ _⟩)) _)
  rw [tsum_eq_sum hzero]
  refine (Finset.sum_le_sum (s := T ×ˢ (Finset.univ : Finset (Fin n)))
    (fun a _ => measure_mono (μ := Measure.dirac (gridSites d n L u x a))
      (Set.subset_univ D))).trans_eq ?_
  simp

theorem exists_uniform_grid_count_bound (d n : ℕ) (L : ℝ) (hL : 0 < L)
    (D : Set (Rd d)) (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) :
    ∃ C : ℕ, ∀ (u : Rd d), u ∈ cube d L → ∀ x : GridMarks d n,
      (∀ z i, x z i ∈ cube d L) → gridConfiguration d n L u x D ≤ (C : ℝ≥0∞) := by
  obtain ⟨R, hR⟩ := hDb.exists_norm_le
  let T : Set (GridIndex d) := {z | ∀ i, z i ∈
    Set.Icc (Int.floor ((-R - 2 * L) / L)) (Int.ceil (R / L))}
  have hT : T.Finite := Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  refine ⟨hT.toFinset.card * n, ?_⟩
  intro u hu x hx
  refine gridConfiguration_count_le d n L u x D hD hT.toFinset
    (fun a ha => hT.mem_toFinset.mpr ?_)
  have hb := gridIndex_bounds_of_site_bound d n L hL u x hx R a (hR _ ha)
  intro i
  refine ⟨(Int.floor_mono ?_).trans (hb i).1, (hb i).2.trans (Int.ceil_mono ?_)⟩
  · exact div_le_div_of_nonneg_right (by linarith [(hu i).2]) hL.le
  · exact div_le_div_of_nonneg_right (sub_le_self R (hu i).1) hL.le

theorem randomShiftGridLaw_count_ae_bound (d m : ℕ) (hm : 0 < m)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q)
    (D : Set (Rd d)) (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) :
    ∃ C : ℕ, ∀ᵐ μ ∂randomShiftGridLaw d m Q, μ D ≤ (C : ℝ≥0∞) := by
  letI : IsProbabilityMeasure Q := hQ.1
  obtain ⟨C, hC⟩ := exists_uniform_grid_count_bound d (m ^ d) (m : ℝ) (Nat.cast_pos.mpr hm) D hD hDb
  letI := gridMarksLaw_probability d (m ^ d) Q
  refine ⟨C, (ae_map_iff (measurable_gridConfiguration d (m ^ d) (m : ℝ)).aemeasurable
    (measurableSet_le (Measure.measurable_coe hD) measurable_const)).mpr ?_⟩
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
    ((Measure.measurable_coe hD).comp (measurable_gridConfiguration d (m ^ d) (m : ℝ)))
    measurable_const)).mpr
  filter_upwards [Measure.ae_smul_measure
    (ae_restrict_mem (Riesz.Negative.measurableSet_cube d (m : ℝ))) (((m : ℝ≥0∞) ^ d)⁻¹)] with u hu
  exact (gridMarksLaw_good d (m ^ d) (m : ℝ) Q hQ.2.1).mono
    (fun x hx => hC u hu x (fun z => (hx z).2))

theorem randomShiftGridLaw_local_second_moment (d m : ℕ) (hm : 0 < m)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q)
    (D : Set (Rd d)) (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) :
    (∫⁻ μ, (μ D) ^ (2 : ℕ) ∂randomShiftGridLaw d m Q) < ∞ := by
  obtain ⟨C, hC⟩ := randomShiftGridLaw_count_ae_bound d m hm Q hQ D hD hDb
  letI : IsProbabilityMeasure Q := hQ.1
  letI := randomShiftGridLaw_probability d m hm Q
  have hbound := lintegral_mono_ae (hC.mono (fun μ hμ => pow_le_pow_left' hμ 2))
  simp only [lintegral_const, measure_univ, mul_one] at hbound
  exact hbound.trans_lt (ENNReal.pow_lt_top (ENNReal.natCast_lt_top C))

end Riesz.Stationary
