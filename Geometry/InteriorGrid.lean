import Riesz.Stationary.Grid
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Finite grids inside open parameter domains

Half-open lattice cells are retained only when their closures lie in the
domain. Their uncovered Lebesgue volume tends to zero with the mesh.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase
open scoped ENNReal Topology Classical

namespace Riesz.Stationary

def interiorGridIndices (d : ℕ) (ell : ℝ) (D : Set (Rd d)) : Set (GridIndex d) :=
  {z | closure (latticeCell d ell 0 z) ⊆ D}

def interiorGridCovered (d : ℕ) (ell : ℝ) (D : Set (Rd d)) : Set (Rd d) :=
  ⋃ z ∈ interiorGridIndices d ell D, latticeCell d ell 0 z

theorem interiorGridCovered_subset (d : ℕ) (ell : ℝ) (D : Set (Rd d)) :
    interiorGridCovered d ell D ⊆ D := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx
  exact hz (subset_closure hxz)

theorem interiorGridCovered_measurable (d : ℕ) (ell : ℝ) (D : Set (Rd d)) :
    MeasurableSet (interiorGridCovered d ell D) := by
  exact MeasurableSet.iUnion (fun z => MeasurableSet.iUnion
    (fun _ => latticeCell_measurable d ell 0 z))

/-- A lattice cell has the Euclidean diameter bound for its mesh. -/
theorem latticeCell_norm_sub_le (d : ℕ) {ell : ℝ} (hell : 0 < ell)
    (z : GridIndex d) {x y : Rd d}
    (hx : x ∈ latticeCell d ell 0 z) (hy : y ∈ latticeCell d ell 0 z) :
    ‖x - y‖ ≤ Real.sqrt d * ell := by
  have hxc := (Riesz.Negative.mem_translatedCube_iff d ell
    (0 + latticeOrigin d ell z) x).mp hx
  have hyc := (Riesz.Negative.mem_translatedCube_iff d ell
    (0 + latticeOrigin d ell z) y).mp hy
  have hc (i : Fin d) : |x i - y i| ≤ ell :=
    abs_le.mpr ⟨by linarith [(hxc i).1, (hyc i).2],
      by linarith [(hyc i).1, (hxc i).2]⟩
  have hsquare : ‖x - y‖ ^ 2 ≤ (d : ℝ) * ell ^ 2 := by
    calc
      _ = ∑ i : Fin d, (x i - y i) ^ 2 := EuclideanSpace.real_norm_sq_eq (x - y)
      _ ≤ ∑ _i : Fin d, ell ^ 2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hell.le).2 (hc i))
      _ = _ := by simp
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hell.le)).mp
      (by simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] using hsquare)

/-- Closure control follows from the diameter bound without a boundary formula. -/
theorem closure_latticeCell_subset_closedBall (d : ℕ) {ell : ℝ}
    (hell : 0 < ell) (z : GridIndex d) {x : Rd d}
    (hx : x ∈ latticeCell d ell 0 z) :
    closure (latticeCell d ell 0 z) ⊆ Metric.closedBall x (Real.sqrt d * ell) := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  exact fun y hy => by simpa only [Metric.mem_closedBall, dist_eq_norm] using
    latticeCell_norm_sub_le d hell z hy hx

theorem interiorGridIndices_finite (d : ℕ) {ell : ℝ} (hell : 0 < ell)
    (D : Set (Rd d)) (hD : Bornology.IsBounded D) :
    (interiorGridIndices d ell D).Finite := by
  obtain ⟨R, hR⟩ := hD.exists_norm_le
  let marks : GridMarks d 1 := fun _ _ => 0
  have hmarks : ∀ z i, marks z i ∈ cube d ell :=
    fun _ _ _ => ⟨by simp [marks], by simpa [marks] using hell⟩
  let T : Set (GridIndex d) := {z | ∀ i, z i ∈
    Set.Icc (Int.floor ((-R - ell) / ell)) (Int.ceil (R / ell))}
  have hT : T.Finite := Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  apply hT.subset
  intro z hz
  have horigin : latticeOrigin d ell z ∈ latticeCell d ell 0 z := by
    simpa only [gridSites, marks, zero_add, add_zero] using
      gridSites_mem_cell d 1 ell 0 marks z 0 (hmarks z 0)
  have hnorm : ‖gridSites d 1 ell 0 marks (z, 0)‖ ≤ R := by
    simpa only [gridSites, marks, zero_add, add_zero] using
      hR (latticeOrigin d ell z) (hz (subset_closure horigin))
  have hb := gridIndex_bounds_of_site_bound d 1 ell hell 0 marks hmarks R (z, 0) hnorm
  simpa only [T, Set.mem_setOf_eq, Set.mem_Icc, PiLp.zero_apply, sub_zero] using hb

theorem eventually_mem_interiorGridCovered (d : ℕ)
    (D : Set (Rd d)) (hD : IsOpen D) {x : Rd d} (hx : x ∈ D)
    (ell : ℕ → ℝ) (hell : ∀ n, 0 < ell n)
    (hmesh : Tendsto ell atTop (𝓝 0)) :
    ∀ᶠ n in atTop, x ∈ interiorGridCovered d (ell n) D := by
  have hrad : Tendsto (fun n => Real.sqrt d * ell n) atTop (𝓝 0) := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul (Real.sqrt d) hmesh
  have hsmall : ∀ᶠ n in atTop, Metric.closedBall x (Real.sqrt d * ell n) ⊆ D :=
    hrad.eventually (eventually_closedBall_subset (hD.mem_nhds hx))
  filter_upwards [hsmall] with n hn
  have hcover : x ∈ ⋃ z : GridIndex d, latticeCell d (ell n) 0 z :=
    (latticeCells_cover d (ell n) (hell n) 0).symm ▸ Set.mem_univ x
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hcover
  exact Set.mem_iUnion₂.mpr ⟨z,
    (closure_latticeCell_subset_closedBall d (hell n) z hz).trans hn, hz⟩

/-- The uncovered volume tends to zero for every positive mesh tending to zero. -/
theorem tendsto_volume_uncovered_interiorGrid (d : ℕ)
    (D : Set (Rd d)) (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D)
    (ell : ℕ → ℝ) (hell : ∀ n, 0 < ell n)
    (hmesh : Tendsto ell atTop (𝓝 0)) :
    Tendsto (fun n => (volume : Measure (Rd d))
      (D \ interiorGridCovered d (ell n) D)) atTop (𝓝 0) := by
  let R : ℕ → Set (Rd d) := fun n => D \ interiorGridCovered d (ell n) D
  let f : ℕ → Rd d → ℝ≥0∞ := fun n => (R n).indicator (fun _ => 1)
  let bound : Rd d → ℝ≥0∞ := D.indicator (fun _ => 1)
  have hR : ∀ n, MeasurableSet (R n) := fun n =>
    hDopen.measurableSet.diff (interiorGridCovered_measurable d (ell n) D)
  have hf : ∀ n, Measurable (f n) := fun n => measurable_const.indicator (hR n)
  have hbound : ∀ n, f n ≤ᵐ[volume] bound := fun n =>
    Eventually.of_forall (Set.indicator_le_indicator_of_subset
      (Set.sdiff_subset : R n ⊆ D) (fun _ => (bot_le : (0 : ℝ≥0∞) ≤ 1)))
  have hfin : (∫⁻ x, bound x ∂(volume : Measure (Rd d))) ≠ ∞ := by
    simpa only [bound, lintegral_indicator_fun_one (μ := volume) hDopen.measurableSet] using
      (hDbdd.measure_lt_top (μ := (volume : Measure (Rd d)))).ne
  have hpoint : ∀ᵐ x ∂(volume : Measure (Rd d)),
      Tendsto (fun n => f n x) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ D
    · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
      filter_upwards [eventually_mem_interiorGridCovered d D hDopen hx ell hell hmesh] with n hn
      simp [f, R, hn]
    · simp [f, R, hx]
  have hlim := tendsto_lintegral_of_dominated_convergence
    (μ := (volume : Measure (Rd d))) (F := f) (f := fun _ => 0)
    bound hf hbound hfin hpoint
  have hlin (n : ℕ) : (∫⁻ x, f n x ∂(volume : Measure (Rd d))) = volume (R n) :=
    lintegral_indicator_fun_one (hR n)
  simpa only [hlin, R, lintegral_zero] using hlim

/-- Finite interior cell families with exact closure certificates and vanishing loss. -/
theorem exists_finite_interiorGrid_almost_cover (d : ℕ)
    (D : Set (Rd d)) (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D)
    (ell : ℕ → ℝ) (hell : ∀ n, 0 < ell n)
    (hmesh : Tendsto ell atTop (𝓝 0)) :
    ∃ I : ℕ → Finset (GridIndex d),
      (∀ n z, z ∈ I n ↔ closure (latticeCell d (ell n) 0 z) ⊆ D) ∧
      Tendsto (fun n => (volume : Measure (Rd d))
        (D \ ⋃ z ∈ I n, latticeCell d (ell n) 0 z)) atTop (𝓝 0) := by
  let I : ℕ → Finset (GridIndex d) := fun n =>
    (interiorGridIndices_finite d (hell n) D hDbdd).toFinset
  have hI (n : ℕ) (z : GridIndex d) :
      z ∈ I n ↔ closure (latticeCell d (ell n) 0 z) ⊆ D :=
    (interiorGridIndices_finite d (hell n) D hDbdd).mem_toFinset
  have heq (n : ℕ) : (⋃ z ∈ I n, latticeCell d (ell n) 0 z) =
      interiorGridCovered d (ell n) D := by
    ext x
    simp only [interiorGridCovered, Set.mem_iUnion, hI,
      interiorGridIndices, Set.mem_setOf_eq]
  refine ⟨I, hI, ?_⟩
  simpa only [heq] using
    tendsto_volume_uncovered_interiorGrid d D hDopen hDbdd ell hell hmesh

end Riesz.Stationary
