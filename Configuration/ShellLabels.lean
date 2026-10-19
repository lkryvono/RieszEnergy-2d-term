import Riesz.Configuration.CountingLabels
import Riesz.Configuration.Translations
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Order.Disjointed

/-!
# Measurable shell labels with repetitions

Disjoint bounded shells give a fixed countable label space for every counting
configuration. Active labels reconstruct the original ambient measure exactly.
-/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Negative Set
open scoped ENNReal Classical

namespace Riesz.Configuration

private theorem sum_cutoff_dirac (d n : ℕ) (x : ℕ → Rd d) :
    Measure.sum (fun j : ℕ => if j < n then Measure.dirac (x j) else 0) =
      tupleCounting d n (fun i => x i.val) := by
  ext D hD
  simp only [Measure.sum_apply _ hD, tupleCounting, Measure.finsetSum_apply]
  have he := (Fin.val_injective (n := n)).tsum_eq
    (f := fun j : ℕ => (if j < n then Measure.dirac (x j) else 0) D)
    (by
      intro j hj
      by_cases h : j < n
      · exact ⟨⟨j, h⟩, rfl⟩
      · exact False.elim (hj (by simp [h])))
  simpa using he.symm

def countingShell (d k : ℕ) : Set (Rd d) :=
  disjointed (fun n : ℕ => Metric.closedBall (0 : Rd d) (n : ℝ)) k

private theorem measurableSet_countingShell (d k : ℕ) :
    MeasurableSet (countingShell d k) := by
  exact MeasurableSet.disjointed
    (fun n : ℕ => (measurableSet_closedBall :
      MeasurableSet (Metric.closedBall (0 : Rd d) (n : ℝ)))) k

private theorem iUnion_countingShell (d : ℕ) :
    (⋃ k : ℕ, countingShell d k) = Set.univ := by
  simpa only [countingShell, iUnion_disjointed] using
    Metric.iUnion_closedBall_nat (0 : Rd d)

private theorem finiteCountingOn_countingShell
    (d k : ℕ) (μ : CountingConfiguration d) :
    FiniteCountingOn d (countingShell d k) μ.val := by
  exact finiteCountingOn_of_subset d μ.val
    (disjointed_subset _ _) (μ.property k)

def countingShellCount (d k : ℕ) (μ : CountingConfiguration d) : ℕ :=
  ⌊(μ.val (countingShell d k)).toReal⌋₊

theorem measurable_countingShellCount (d k : ℕ) :
    Measurable (countingShellCount d k) := by
  exact ((Measure.measurable_coe (measurableSet_countingShell d k)).comp
    measurable_subtype_coe).ennreal_toReal.nat_floor

private def finiteCountingLabel (d n : ℕ) :
    Measure (Rd d) → (Fin n → Rd d) :=
  Classical.choose (exists_measurable_counting_label d n)

private theorem measurable_finiteCountingLabel (d n : ℕ) :
    Measurable (finiteCountingLabel d n) :=
  (Classical.choose_spec (exists_measurable_counting_label d n)).1

private theorem finiteCountingLabel_spec
    (d n : ℕ) (ν : Measure (Rd d))
    (hν : ∃ x : Fin n → Rd d, ν = tupleCounting d n x) :
    tupleCounting d n (finiteCountingLabel d n ν) = ν :=
  (Classical.choose_spec (exists_measurable_counting_label d n)).2 ν hν

private theorem countingShell_label_spec
    (d k : ℕ) (μ : CountingConfiguration d) :
    tupleCounting d (countingShellCount d k μ)
      (finiteCountingLabel d (countingShellCount d k μ)
        (μ.val.restrict (countingShell d k))) =
      μ.val.restrict (countingShell d k) := by
  obtain ⟨n, x, hx⟩ := finiteCountingOn_countingShell d k μ
  have hmass : μ.val (countingShell d k) = (n : ℝ≥0∞) := by
    simpa only [Measure.restrict_apply_univ, tupleCounting_univ] using
      congrArg (fun ν : Measure (Rd d) => ν Set.univ) hx
  have hn : countingShellCount d k μ = n := by
    simp [countingShellCount, hmass]
  rw [hn]
  exact finiteCountingLabel_spec d n (μ.val.restrict (countingShell d k)) ⟨x, hx⟩

private def countingPositionAtCount
    (d k n j : ℕ) (μ : CountingConfiguration d) : Rd d :=
  if hj : j < n then
    finiteCountingLabel d n (μ.val.restrict (countingShell d k)) ⟨j, hj⟩
  else 0

def countingShellPosition (d k j : ℕ) (μ : CountingConfiguration d) : Rd d :=
  countingPositionAtCount d k (countingShellCount d k μ) j μ

private theorem measurable_countingPositionAtCount (d k n j : ℕ) :
    Measurable (countingPositionAtCount d k n j) := by
  change Measurable (fun μ : CountingConfiguration d => countingPositionAtCount d k n j μ)
  by_cases hj : j < n
  · simpa only [countingPositionAtCount, dif_pos hj, Function.comp_def] using
      (measurable_pi_apply (⟨j, hj⟩ : Fin n)).comp
        ((measurable_finiteCountingLabel d n).comp
          ((measurable_restrict d (countingShell d k)
            (measurableSet_countingShell d k)).comp measurable_subtype_coe))
  · simpa only [countingPositionAtCount, dif_neg hj] using
      (measurable_const : Measurable (fun _ : CountingConfiguration d => (0 : Rd d)))

theorem measurable_countingShellPosition (d k j : ℕ) :
    Measurable (countingShellPosition d k j) := by
  have hf : Measurable (fun p : CountingConfiguration d × ℕ =>
      countingPositionAtCount d k p.2 j p.1) :=
    measurable_from_prod_countable_left
      (fun n => measurable_countingPositionAtCount d k n j)
  exact hf.comp (measurable_id.prodMk (measurable_countingShellCount d k))

theorem countingShell_tuple (d k : ℕ) (μ : CountingConfiguration d) :
    tupleCounting d (countingShellCount d k μ)
      (fun i => countingShellPosition d k i.val μ) =
      μ.val.restrict (countingShell d k) := by
  simpa [countingShellPosition, countingPositionAtCount] using
    countingShell_label_spec d k μ

theorem countingShellPosition_mem (d k j : ℕ) (μ : CountingConfiguration d)
    (hj : j < countingShellCount d k μ) :
    countingShellPosition d k j μ ∈ countingShell d k := by
  have hz : tupleCounting d (countingShellCount d k μ)
      (fun i => countingShellPosition d k i.val μ) (countingShell d k)ᶜ = 0 := by
    rw [countingShell_tuple]
    simp [Measure.restrict_apply (measurableSet_countingShell d k).compl]
  exact ((tupleCounting_compl_eq_zero_iff d (countingShellCount d k μ)
    (fun i => countingShellPosition d k i.val μ) (countingShell d k)
    (measurableSet_countingShell d k)).mp hz) ⟨j, hj⟩

def countingShellAtom (d : ℕ) (ij : ℕ × ℕ) (μ : CountingConfiguration d) :
    Measure (Rd d) :=
  if ij.2 < countingShellCount d ij.1 μ then
    Measure.dirac (countingShellPosition d ij.1 ij.2 μ)
  else 0

theorem measurable_countingShellAtom (d : ℕ) (ij : ℕ × ℕ) :
    Measurable (countingShellAtom d ij) := by
  exact Measurable.ite
    (measurableSet_lt measurable_const (measurable_countingShellCount d ij.1))
    (Measure.measurable_dirac.comp (measurable_countingShellPosition d ij.1 ij.2))
    measurable_const

private theorem countingShell_sum (d k : ℕ) (μ : CountingConfiguration d) :
    Measure.sum (fun j : ℕ => countingShellAtom d (k, j) μ) =
      μ.val.restrict (countingShell d k) := by
  exact (sum_cutoff_dirac d (countingShellCount d k μ)
    (fun j => countingShellPosition d k j μ)).trans (countingShell_tuple d k μ)

theorem countingConfiguration_eq_sum_activeDirac
    (d : ℕ) (μ : CountingConfiguration d) :
    μ.val = Measure.sum (fun ij : ℕ × ℕ => countingShellAtom d ij μ) := by
  calc
    μ.val = Measure.sum (fun k : ℕ => μ.val.restrict (countingShell d k)) := by
      simpa only [iUnion_countingShell, Measure.restrict_univ] using
        (Measure.restrict_iUnion (μ := μ.val) (s := countingShell d)
          (disjoint_disjointed (fun n : ℕ =>
            Metric.closedBall (0 : Rd d) (n : ℝ)))
          (fun k => measurableSet_countingShell d k))
    _ = Measure.sum (fun k : ℕ =>
        Measure.sum (fun j : ℕ => countingShellAtom d (k, j) μ)) := by
      exact congrArg (fun f : ℕ → Measure (Rd d) => Measure.sum f)
        (funext (fun k => (countingShell_sum d k μ).symm))
    _ = Measure.sum (fun ij : ℕ × ℕ => countingShellAtom d ij μ) :=
      Measure.sum_sum (fun k j => countingShellAtom d (k, j) μ)

end Riesz.Configuration
