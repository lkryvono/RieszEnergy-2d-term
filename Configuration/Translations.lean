import Riesz.Configuration.Compactness
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! Translation of multiplicity-aware counting configurations and determination
of their laws by the existing countable family of compact tests. -/

noncomputable section

open MeasureTheory RieszShowcase Set
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Configuration

theorem finiteCountingOn_of_subset (d : ℕ) (μ : Measure (Rd d))
    {K L : Set (Rd d)} (hKL : K ⊆ L) (hμ : FiniteCountingOn d L μ) :
    FiniteCountingOn d K μ := by
  rcases hμ with ⟨n, x, hx⟩
  rcases finiteCountingOn_tupleCounting d n x K with ⟨m, y, hy⟩
  exact ⟨m, y, (Measure.restrict_restrict_of_subset hKL).symm.trans
    ((congrArg (fun ν : Measure (Rd d) => ν.restrict K) hx).trans hy)⟩

theorem tupleCounting_map_add (d n : ℕ) (a : Rd d) (x : Fin n → Rd d) :
    (Riesz.Negative.tupleCounting d n x).map (fun z => a + z) =
      Riesz.Negative.tupleCounting d n (fun i => a + x i) := by
  simp only [Riesz.Negative.tupleCounting,
    Measure.map_finset_sum (f := fun z : Rd d => a + z)
      (measurable_const.add measurable_id).aemeasurable,
    Measure.map_dirac' (f := fun z : Rd d => a + z) (measurable_const.add measurable_id)]

theorem isCountingConfiguration_map_add (d : ℕ) (a : Rd d)
    (μ : Measure (Rd d)) (hμ : IsCountingConfiguration d μ) :
    IsCountingConfiguration d (μ.map (fun z => a + z)) := by
  intro k
  obtain ⟨m, hm⟩ := exists_nat_ge ((k : ℝ) + ‖a‖)
  have hsub : (fun z : Rd d => a + z) ⁻¹' Metric.closedBall 0 (k : ℝ) ⊆
      Metric.closedBall 0 (m : ℝ) := by
    intro z hz
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hz ⊢
    have hnorm : ‖z‖ ≤ ‖a + z‖ + ‖a‖ := by simpa using norm_sub_le (a + z) a
    exact hnorm.trans ((add_le_add hz le_rfl).trans hm)
  rcases finiteCountingOn_of_subset d μ hsub (hμ m) with ⟨n, x, hx⟩
  refine ⟨n, fun i => a + x i, ?_⟩
  rw [Measure.restrict_map (f := fun z : Rd d => a + z)
      (measurable_const.add measurable_id) measurableSet_closedBall,
    hx, tupleCounting_map_add]

/-- Translation retains every atom, including its multiplicity. -/
def translateCounting (d : ℕ) (a : Rd d) (μ : CountingConfiguration d) :
    CountingConfiguration d :=
  ⟨μ.val.map (fun z => a + z), isCountingConfiguration_map_add d a μ.val μ.property⟩

theorem translateCounting_val (d : ℕ) (a : Rd d) (μ : CountingConfiguration d) :
    (translateCounting d a μ).val = μ.val.map (fun z => a + z) := rfl

/-- Pullback of a compact test by the same translation. -/
def translatedCountingTest (d : ℕ) (a : Rd d) (f : C_c(Rd d, ℝ)) :
    C_c(Rd d, ℝ) := f.comp (Homeomorph.addLeft a).toCocompactMap

theorem translatedCountingTest_apply (d : ℕ) (a : Rd d) (f : C_c(Rd d, ℝ))
    (x : Rd d) : translatedCountingTest d a f x = f (a + x) := rfl

theorem integral_translateCounting (d : ℕ) (a : Rd d)
    (μ : CountingConfiguration d) (f : C_c(Rd d, ℝ)) :
    (∫ x, f x ∂(translateCounting d a μ).val) =
      ∫ x, translatedCountingTest d a f x ∂μ.val := by
  exact integral_map_of_stronglyMeasurable (measurable_const.add measurable_id)
    f.continuous.stronglyMeasurable

theorem continuous_translateCounting (d : ℕ) (a : Rd d) :
    Continuous (translateCounting d a) := by
  apply (countingCompactTest_isEmbedding d).continuous_iff.mpr
  exact continuous_pi fun f => by
    simpa only [Function.comp_def, countingCompactTest, integral_translateCounting] using
      continuous_countingIntegral d (translatedCountingTest d a f)

theorem measurable_translateCounting (d : ℕ) (a : Rd d) :
    Measurable (translateCounting d a) := by
  exact (continuous_translateCounting d a).measurable

theorem countingConfiguration_measurableSpace_eq_comap_code (d : ℕ) :
    (inferInstance : MeasurableSpace (CountingConfiguration d)) =
      MeasurableSpace.comap (countingTestCode d) inferInstance := by
  simpa only [borel_comap, BorelSpace.measurable_eq] using
    (countingConfiguration_measurableSpace_eq_borel d).trans
      (congrArg (@borel (CountingConfiguration d)) (countingConfiguration_topology_eq_induced d))

/-- The countable compact-test code determines every law on counting configurations. -/
theorem map_countingTestCode_injective (d : ℕ) :
    Function.Injective (fun Q : Measure (CountingConfiguration d) =>
      Q.map (countingTestCode d)) := by
  intro P Q h
  ext S hS
  have hS' : MeasurableSet[MeasurableSpace.comap (countingTestCode d) inferInstance] S :=
    (countingConfiguration_measurableSpace_eq_comap_code d) ▸ hS
  rcases MeasurableSpace.measurableSet_comap.mp hS' with ⟨T, hT, rfl⟩
  simpa only [Measure.map_apply (measurable_countingTestCode d) hT] using
    congrArg (fun P : Measure ((ℕ ⊕ (ℕ × ℕ)) → ℝ) => P T) h

theorem map_translateCounting_eq_of_finset (d : ℕ) (a : Rd d)
    (Q : Measure (CountingConfiguration d)) [IsFiniteMeasure Q]
    (h : ∀ I : Finset (ℕ ⊕ (ℕ × ℕ)),
      Q.map (fun μ => I.restrict (countingTestCode d (translateCounting d a μ))) =
        Q.map (fun μ => I.restrict (countingTestCode d μ))) :
    Q.map (translateCounting d a) = Q := by
  apply map_countingTestCode_injective d
  change (Q.map (translateCounting d a)).map (countingTestCode d) = Q.map (countingTestCode d)
  rw [Measure.map_map (measurable_countingTestCode d) (measurable_translateCounting d a)]
  exact (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
    ((measurable_countingTestCode d).comp (measurable_translateCounting d a)).aemeasurable
    (measurable_countingTestCode d).aemeasurable).mpr h

/-- Equality of all finite joint test laws gives the showcase's exact stationarity. -/
theorem isStationary_map_val_of_countingTestCode_finset (d : ℕ)
    (Q : Measure (CountingConfiguration d)) [IsFiniteMeasure Q]
    (h : ∀ (a : Rd d) (I : Finset (ℕ ⊕ (ℕ × ℕ))),
      Q.map (fun μ => I.restrict (countingTestCode d (translateCounting d a μ))) =
        Q.map (fun μ => I.restrict (countingTestCode d μ))) :
    IsStationary d (Q.map Subtype.val) := by
  intro a
  simpa only [Measure.map_map
      (Measure.measurable_map (fun z : Rd d => a + z) (measurable_const.add measurable_id))
      measurable_subtype_coe,
    Measure.map_map measurable_subtype_coe (measurable_translateCounting d a),
    Function.comp_def, translateCounting] using
    congrArg (fun P : Measure (CountingConfiguration d) => P.map Subtype.val)
      (map_translateCounting_eq_of_finset d a Q (h a))

end Riesz.Configuration
