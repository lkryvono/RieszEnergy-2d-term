import Riesz.Negative.Sampling
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Measurable finite labels with repetitions

Sorting labels by a real measurable embedding preserves their multiplicities.
The resulting canonical finite tuple gives a measurable selector on measures.
-/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Negative
open scoped ENNReal Classical

namespace Riesz.Configuration

private theorem tupleCounting_threshold_eq_card
    (d n : ℕ) (f : Rd d → ℝ) (x : Fin n → Rd d) (a : ℝ) :
    tupleCounting d n x {z | f z ≤ a} =
      ((Finset.univ.filter (fun i => f (x i) ≤ a)).card : ℝ≥0∞) := by
  simp [tupleCounting, Measure.finsetSum_apply, Measure.dirac_apply, Set.indicator]

private theorem tupleCounting_monotone_injective
    (d n : ℕ) (f : Rd d → ℝ) (hf : Function.Injective f) :
    Set.InjOn (tupleCounting d n) {x | Monotone (f ∘ x)} := by
  intro x hx y hy hxy
  have hcard (a : ℝ) :
      (Finset.univ.filter (fun i => f (x i) ≤ a)).card =
        (Finset.univ.filter (fun i => f (y i) ≤ a)).card := by
    have he := congrArg (fun μ : Measure (Rd d) => μ {z | f z ≤ a}) hxy
    rw [tupleCounting_threshold_eq_card, tupleCounting_threshold_eq_card] at he
    exact_mod_cast he
  funext j
  apply hf
  apply le_antisymm
  · apply (Tuple.lt_card_le_iff_apply_le_of_monotone (j := j) hx).1
    change (j : ℕ) < (Finset.univ.filter (fun i => f (x i) ≤ f (y j))).card
    rw [hcard (f (y j))]
    exact (Tuple.lt_card_le_iff_apply_le_of_monotone (j := j) hy).2 le_rfl
  · apply (Tuple.lt_card_le_iff_apply_le_of_monotone (j := j) hy).1
    change (j : ℕ) < (Finset.univ.filter (fun i => f (y i) ≤ f (x j))).card
    rw [← hcard (f (x j))]
    exact (Tuple.lt_card_le_iff_apply_le_of_monotone (j := j) hx).2 le_rfl

private theorem measurableSet_monotone_tuples
    (d n : ℕ) (f : Rd d → ℝ) (hf : Measurable f) :
    MeasurableSet {x : Fin n → Rd d | Monotone (f ∘ x)} := by
  simpa only [Monotone, Set.setOf_forall, Function.comp_def] using
    MeasurableSet.iInter (fun i : Fin n => MeasurableSet.iInter (fun j : Fin n =>
      MeasurableSet.iInter (fun _ : i ≤ j =>
        measurableSet_le (hf.comp (measurable_pi_apply i))
          (hf.comp (measurable_pi_apply j)))))

private theorem tupleCounting_monotone_representation
    (d n : ℕ) (f : Rd d → ℝ) (x : Fin n → Rd d) :
    ∃ y : Fin n → Rd d, Monotone (f ∘ y) ∧
      tupleCounting d n y = tupleCounting d n x := by
  refine ⟨x ∘ Tuple.sort (f ∘ x), Tuple.monotone_sort (f ∘ x), ?_⟩
  exact Equiv.sum_comp (Tuple.sort (f ∘ x)) (fun i => Measure.dirac (x i))

/-- Measurable labels for finite counting measures retain repeated sites. -/
theorem exists_measurable_counting_label (d n : ℕ) :
    ∃ label : Measure (Rd d) → (Fin n → Rd d), Measurable label ∧
      ∀ μ : Measure (Rd d),
        (∃ x : Fin n → Rd d, μ = tupleCounting d n x) →
        tupleCounting d n (label μ) = μ := by
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real (Rd d)
  let O := {x : Fin n → Rd d // Monotone (f ∘ x)}
  letI : StandardBorelSpace O := (measurableSet_monotone_tuples d n f hf.measurable).standardBorel
  letI := countablySeparated_finiteMeasure (Rd d)
  have hg : MeasurableEmbedding (fun x : O => finiteTupleCounting d n x.val) :=
    ((measurable_finiteTupleCounting d n).comp measurable_subtype_coe).measurableEmbedding
      (fun x y h => Subtype.ext (tupleCounting_monotone_injective d n f hf.injective
        x.property y.property (congrArg FiniteMeasure.toMeasure h)))
  have hcount : MeasurableEmbedding (fun x : O => tupleCounting d n x.val) :=
    (MeasurableEmbedding.subtype_coe
      (FiniteMeasure.measurableSet_isFiniteMeasure (Ω := Rd d))).comp hg
  obtain ⟨label, hlabel, hleft⟩ := hcount.exists_measurable_extend
    (measurable_subtype_coe : Measurable (fun x : O => x.val))
    (fun _ => ⟨fun _ => 0⟩)
  refine ⟨label, hlabel, ?_⟩
  rintro μ ⟨x, rfl⟩
  obtain ⟨y, hy, hxy⟩ := tupleCounting_monotone_representation d n f x
  have hly : label (tupleCounting d n y) = y := congr_fun hleft (⟨y, hy⟩ : O)
  rw [← hxy, hly]

end Riesz.Configuration
