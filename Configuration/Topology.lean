import Riesz.Configuration.LocalSimplicity
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.Topology.Maps.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.Basic

/-! Multiplicity-aware counting configurations in the showcase's measure space.
The measurable structure is inherited from the Giry measurable structure on
measures. Repeated tuple entries are deliberately permitted in finite restrictions.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Configuration

/-- A finite restriction is a sum of unit atoms, with repetitions allowed. -/
def FiniteCountingOn (d : ℕ) (K : Set (Rd d)) (μ : Measure (Rd d)) : Prop :=
  ∃ n : ℕ, ∃ x : Fin n → Rd d,
    μ.restrict K = Riesz.Negative.tupleCounting d n x

/-- A local counting criterion which preserves multiplicity in vague limits. -/
def IsCountingConfiguration (d : ℕ) (μ : Measure (Rd d)) : Prop :=
  ∀ k : ℕ, FiniteCountingOn d (Metric.closedBall (0 : Rd d) (k : ℝ)) μ

/-- Counting configurations retain the ambient Giry measurable structure. -/
abbrev CountingConfiguration (d : ℕ) :=
  {μ : Measure (Rd d) // IsCountingConfiguration d μ}

theorem finiteSimpleOn_finiteCountingOn (d : ℕ) (K : Set (Rd d))
    (μ : Measure (Rd d)) (hμ : FiniteSimpleOn d K μ) : FiniteCountingOn d K μ := by
  rcases hμ with ⟨n, x, hx, h⟩
  exact ⟨n, x, h⟩

theorem locallySimple_isCountingConfiguration (d : ℕ) (μ : Measure (Rd d))
    (hμ : LocallySimple d μ) : IsCountingConfiguration d μ := by
  exact fun k => finiteSimpleOn_finiteCountingOn d _ μ (hμ k)

theorem simple_isCountingConfiguration (d : ℕ) (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ) : IsCountingConfiguration d μ := by
  exact locallySimple_isCountingConfiguration d μ (simple_locallySimple d μ hμ)

theorem zero_isCountingConfiguration (d : ℕ) :
    IsCountingConfiguration d (0 : Measure (Rd d)) := by
  intro k
  refine ⟨0, Fin.elim0, ?_⟩
  simp [Riesz.Negative.tupleCounting]

/-- Lift a simple ambient measure, using the empty configuration otherwise. -/
def countingOfSimple (d : ℕ) (μ : Measure (Rd d)) : CountingConfiguration d :=
  ⟨if IsSimpleConfiguration d μ then μ else 0, by
    split
    · exact simple_isCountingConfiguration d μ ‹_›
    · exact zero_isCountingConfiguration d⟩

theorem measurable_countingOfSimple (d : ℕ) : Measurable (countingOfSimple d) := by
  exact (Measurable.ite (measurableSet_isSimpleConfiguration d)
    measurable_id measurable_const).subtype_mk

theorem countingOfSimple_val (d : ℕ) (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ) : (countingOfSimple d μ).val = μ := by
  simp [countingOfSimple, hμ]

/-- An ambient simple law represented on the multiplicity-aware subtype. -/
def countingLawOfSimple (d : ℕ) (P : ConfigurationLaw d) :
    Measure (CountingConfiguration d) := P.map (countingOfSimple d)

theorem countingLawOfSimple_map_val (d : ℕ) (P : ConfigurationLaw d)
    (hP : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ) :
    (countingLawOfSimple d P).map Subtype.val = P := by
  rw [countingLawOfSimple, Measure.map_map measurable_subtype_coe (measurable_countingOfSimple d)]
  exact (Measure.map_congr (hP.mono fun μ hμ => countingOfSimple_val d μ hμ)).trans
    Measure.map_id

instance countingLawOfSimple_isProbabilityMeasure (d : ℕ) (P : ConfigurationLaw d)
    [IsProbabilityMeasure P] : IsProbabilityMeasure (countingLawOfSimple d P) := by
  exact P.isProbabilityMeasure_map (measurable_countingOfSimple d).aemeasurable

theorem exists_countingLaw_of_admissible (d : ℕ) (P : ConfigurationLaw d)
    (hP : Admissible d P) : ∃ Q : Measure (CountingConfiguration d),
      IsProbabilityMeasure Q ∧ Q.map Subtype.val = P := by
  letI : IsProbabilityMeasure P := hP.1
  exact ⟨countingLawOfSimple d P, inferInstance, countingLawOfSimple_map_val d P hP.2.1⟩

theorem finiteCountingOn_finite_restrict (d : ℕ) (K : Set (Rd d))
    (μ : Measure (Rd d)) (hμ : FiniteCountingOn d K μ) : IsFiniteMeasure (μ.restrict K) := by
  rcases hμ with ⟨n, x, h⟩
  exact h.symm ▸ Riesz.Negative.tupleCounting_isFiniteMeasure d n x

theorem isCountingConfiguration_closedBall_lt_top (d : ℕ) (μ : Measure (Rd d))
    (hμ : IsCountingConfiguration d μ) (k : ℕ) :
    μ (Metric.closedBall (0 : Rd d) (k : ℝ)) < ∞ := by
  exact (isFiniteMeasure_restrict.mp (finiteCountingOn_finite_restrict d _ μ (hμ k))).lt_top

theorem isCountingConfiguration_finiteOnCompacts (d : ℕ) (μ : Measure (Rd d))
    (hμ : IsCountingConfiguration d μ) : IsFiniteMeasureOnCompacts μ := by
  constructor
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨k, hk⟩ := exists_nat_ge R
  refine (measure_mono (show K ⊆ Metric.closedBall (0 : Rd d) (k : ℝ) from ?_)).trans_lt
    (isCountingConfiguration_closedBall_lt_top d μ hμ k)
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using (hR x hx).trans hk

instance countingConfiguration_finiteOnCompacts (d : ℕ) (μ : CountingConfiguration d) :
    IsFiniteMeasureOnCompacts μ.val := isCountingConfiguration_finiteOnCompacts d μ.val μ.property

/-- Compact-test coordinates defining the vague topology. -/
def countingCompactTest (d : ℕ) (μ : CountingConfiguration d) : C_c(Rd d, ℝ) → ℝ :=
  fun f => ∫ x, f x ∂μ.val

theorem countingCompactTest_injective (d : ℕ) : Function.Injective (countingCompactTest d) := by
  intro μ ν h
  exact Subtype.ext (Measure.ext_of_integral_eq_on_compactlySupported fun f => congr_fun h f)

/-- Vague convergence is convergence of every compact-test coordinate. -/
instance countingConfiguration_topologicalSpace (d : ℕ) : TopologicalSpace (CountingConfiguration d) :=
  TopologicalSpace.induced (countingCompactTest d) inferInstance

theorem countingCompactTest_isEmbedding (d : ℕ) : Topology.IsEmbedding (countingCompactTest d) := by
  exact (countingCompactTest_injective d).isEmbedding_induced

instance countingConfiguration_t2Space (d : ℕ) : T2Space (CountingConfiguration d) :=
  (countingCompactTest_isEmbedding d).t2Space

theorem continuous_countingIntegral (d : ℕ) (f : C_c(Rd d, ℝ)) :
    Continuous (fun μ : CountingConfiguration d => ∫ x, f x ∂μ.val) := by
  exact (continuous_apply f).comp (countingCompactTest_isEmbedding d).continuous

theorem measurable_countingIntegral (d : ℕ) (f : C_c(Rd d, ℝ)) :
    Measurable (fun μ : CountingConfiguration d => ∫ x, f x ∂μ.val) := by
  convert (((Measure.measurable_lintegral f.continuous.measurable.ennreal_ofReal).comp
    measurable_subtype_coe).ennreal_toReal.sub
      (((Measure.measurable_lintegral f.continuous.measurable.neg.ennreal_ofReal).comp
        measurable_subtype_coe).ennreal_toReal)) using 1
  funext μ
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part f.integrable

theorem tendsto_countingConfiguration_iff (d : ℕ) {α : Type*} {l : Filter α}
    {u : α → CountingConfiguration d} {μ : CountingConfiguration d} :
    Filter.Tendsto u l (𝓝 μ) ↔ ∀ f : C_c(Rd d, ℝ),
      Filter.Tendsto (fun i => ∫ x, f x ∂(u i).val) l (𝓝 (∫ x, f x ∂μ.val)) := by
  exact (countingCompactTest_isEmbedding d).isInducing.tendsto_nhds_iff.trans tendsto_pi_nhds

/-- Compact-set counts are upper semicontinuous in the vague topology. -/
theorem upperSemicontinuous_countingCount (d : ℕ) (K : Set (Rd d)) (hK : IsCompact K) :
    UpperSemicontinuous (fun μ : CountingConfiguration d => μ.val K) := by
  simp_rw [hK.measure_eq_biInf_integral_hasCompactSupport]
  refine upperSemicontinuous_iInf fun f => upperSemicontinuous_iInf fun hf =>
    upperSemicontinuous_iInf fun hc => upperSemicontinuous_iInf fun _ =>
      upperSemicontinuous_iInf fun _ => ?_
  exact (ENNReal.continuous_ofReal.comp
    (continuous_countingIntegral d ⟨⟨f, hf⟩, hc⟩)).upperSemicontinuous

/-- Compact counts are measurable for the Borel structure of the vague topology. -/
theorem measurable_countingCount_borel (d : ℕ) (K : Set (Rd d)) (hK : IsCompact K) :
    @Measurable (CountingConfiguration d) ℝ≥0∞ (borel (CountingConfiguration d))
      inferInstance (fun μ => μ.val K) := by
  borelize (CountingConfiguration d)
  exact (upperSemicontinuous_countingCount d K hK).measurable

/-- A compact restriction is Giry measurable from the vague Borel space. -/
theorem measurable_countingRestrict_borel (d : ℕ) (K : Set (Rd d)) (hK : IsCompact K) :
    @Measurable (CountingConfiguration d) (Measure (Rd d)) (borel (CountingConfiguration d))
      inferInstance (fun μ => μ.val.restrict K) := by
  borelize (CountingConfiguration d)
  letI (μ : CountingConfiguration d) : IsFiniteMeasure (μ.val.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  refine Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
    (fun F hF => ?_) ?_
  · simpa only [Measure.restrict_apply hF.measurableSet] using
      measurable_countingCount_borel d (F ∩ K) (hK.inter_left hF)
  · simpa only [Measure.restrict_apply_univ] using measurable_countingCount_borel d K hK

/-- The ambient measure projection is Giry measurable for the vague Borel structure. -/
theorem measurable_countingVal_borel (d : ℕ) :
    @Measurable (CountingConfiguration d) (Measure (Rd d)) (borel (CountingConfiguration d))
      inferInstance Subtype.val := by
  borelize (CountingConfiguration d)
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hmono : Monotone (fun k : ℕ => s ∩ Metric.closedBall (0 : Rd d) (k : ℝ)) :=
    fun _ _ hij _ hx => ⟨hx.1, Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hij) hx.2⟩
  convert (Measurable.iSup fun k : ℕ => (Measure.measurable_coe hs).comp
    (measurable_countingRestrict_borel d (Metric.closedBall (0 : Rd d) (k : ℝ))
      (isCompact_closedBall _ _))) using 1
  funext μ
  simpa only [Function.comp_apply, Measure.restrict_apply hs,
    Metric.iUnion_inter_closedBall_nat] using hmono.measure_iUnion (μ := μ.val)

/-- The inherited Giry sigma-algebra is contained in the vague Borel sigma-algebra. -/
theorem countingConfiguration_measurableSpace_le_borel (d : ℕ) :
    (inferInstance : MeasurableSpace (CountingConfiguration d)) ≤ borel (CountingConfiguration d) := by
  exact (measurable_countingVal_borel d).comap_le

/-- Each fixed compact support admits a uniformly dense countable family of tests. -/
theorem exists_supportedCompactTestSequence (d n : ℕ) :
    ∃ F : ℕ → C_c(Rd d, ℝ),
      (∀ k, tsupport (F k) ⊆ Metric.closedBall (0 : Rd d) (n : ℝ)) ∧
      ∀ f : C_c(Rd d, ℝ),
        tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ) →
        ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x : Rd d, |f x - F k x| < ε := by
  let S := {f : C_c(Rd d, ℝ) // tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ)}
  let r : S → C(Metric.closedBall (0 : Rd d) (n : ℝ), ℝ) :=
    fun f => f.val.toContinuousMap.restrict _
  letI : TopologicalSpace S := TopologicalSpace.induced r inferInstance
  letI : SecondCountableTopology S := TopologicalSpace.secondCountableTopology_induced S _ r
  haveI : Nonempty S := ⟨⟨0, by simp⟩⟩
  refine ⟨fun k => (TopologicalSpace.denseSeq S k).val,
    fun k => (TopologicalSpace.denseSeq S k).property, ?_⟩
  intro f hf ε hε
  obtain ⟨k, hk⟩ := (TopologicalSpace.denseRange_denseSeq S).exists_mem_open
    (show IsOpen (r ⁻¹' Metric.ball (r ⟨f, hf⟩) ε) from
      Metric.isOpen_ball.preimage continuous_induced_dom)
    ⟨⟨f, hf⟩, Metric.mem_ball_self hε⟩
  refine ⟨k, fun x => ?_⟩
  by_cases hx : x ∈ Metric.closedBall (0 : Rd d) (n : ℝ)
  · simpa [r, Real.dist_eq, abs_sub_comm] using
      (ContinuousMap.dist_lt_iff hε).1 hk ⟨x, hx⟩
  · simpa only [image_eq_zero_of_notMem_tsupport (fun h => hx (hf h)),
      image_eq_zero_of_notMem_tsupport
        (fun h => hx ((TopologicalSpace.denseSeq S k).property h)), sub_self, abs_zero] using hε

/-- A compact cutoff controls the mass of each compact ball. -/
theorem exists_countingMassCutoff (d n : ℕ) :
    ∃ χ : C_c(Rd d, ℝ),
      (∀ x, 0 ≤ χ x) ∧ Set.EqOn χ 1 (Metric.closedBall (0 : Rd d) (n : ℝ)) := by
  obtain ⟨f, hf, _, hc, h01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall (0 : Rd d) (n : ℝ)) isClosed_empty (by simp)
  exact ⟨⟨f, hc⟩, fun x => (h01 x).1, hf⟩

/-- Integrating a nonnegative unit cutoff bounds the local counting mass. -/
theorem countingMass_le_cutoff (d n : ℕ) (μ : CountingConfiguration d)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (hχ1 : Set.EqOn χ 1 (Metric.closedBall (0 : Rd d) (n : ℝ))) :
    μ.val.real (Metric.closedBall (0 : Rd d) (n : ℝ)) ≤ ∫ x, χ x ∂μ.val := by
  have hle := (χ.integrable (μ := μ.val)).measure_le_integral (Filter.Eventually.of_forall hχ)
    (fun x hx => (hχ1 hx).ge)
  simpa only [Measure.real, ENNReal.toReal_ofReal (integral_nonneg hχ)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hle

/-- Uniform approximation on a common compact support controls test integrals. -/
theorem countingIntegral_sub_le (d n : ℕ) (μ : CountingConfiguration d)
    (f g : C_c(Rd d, ℝ)) (ε : ℝ)
    (hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ))
    (hg : tsupport g ⊆ Metric.closedBall (0 : Rd d) (n : ℝ))
    (hfg : ∀ x, |f x - g x| ≤ ε) :
    |(∫ x, f x ∂μ.val) - ∫ x, g x ∂μ.val| ≤
      ε * μ.val.real (Metric.closedBall (0 : Rd d) (n : ℝ)) := by
  rw [← integral_sub f.integrable g.integrable]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Metric.closedBall (0 : Rd d) (n : ℝ)) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hf h)),
        image_eq_zero_of_notMem_tsupport (fun h => hx (hg h)), sub_self])]
  simpa only [Real.norm_eq_abs] using norm_setIntegral_le_of_norm_le_const
    (μ := μ.val) (f := fun x => f x - g x)
    (isCompact_closedBall (0 : Rd d) (n : ℝ)).measure_lt_top (fun x _ => hfg x)

/-- One fixed family of compact cutoffs. -/
def countingMassCutoff (d n : ℕ) : C_c(Rd d, ℝ) :=
  (exists_countingMassCutoff d n).choose

theorem countingMassCutoff_spec (d n : ℕ) :
    (∀ x, 0 ≤ countingMassCutoff d n x) ∧
      Set.EqOn (countingMassCutoff d n) 1 (Metric.closedBall (0 : Rd d) (n : ℝ)) := by
  exact (exists_countingMassCutoff d n).choose_spec

/-- Fixed countable dense test families, each with a common compact support. -/
def countingSupportedTest (d n : ℕ) : ℕ → C_c(Rd d, ℝ) :=
  (exists_supportedCompactTestSequence d n).choose

theorem countingSupportedTest_spec (d n : ℕ) :
    (∀ k, tsupport (countingSupportedTest d n k) ⊆
      Metric.closedBall (0 : Rd d) (n : ℝ)) ∧
    ∀ f : C_c(Rd d, ℝ), tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ) →
      ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x, |f x - countingSupportedTest d n k x| < ε := by
  exact (exists_supportedCompactTestSequence d n).choose_spec

/-- Cutoffs and supported dense tests form a single countable family. -/
def countingTest (d : ℕ) : ℕ ⊕ (ℕ × ℕ) → C_c(Rd d, ℝ) :=
  Sum.elim (countingMassCutoff d) (fun nk => countingSupportedTest d nk.1 nk.2)

/-- Countably many compact-test integrals encoding the existing vague topology. -/
def countingTestCode (d : ℕ) (μ : CountingConfiguration d) : (ℕ ⊕ (ℕ × ℕ)) → ℝ :=
  fun i => ∫ x, countingTest d i x ∂μ.val

theorem continuous_countingTestCode (d : ℕ) : Continuous (countingTestCode d) := by
  exact continuous_pi fun i => continuous_countingIntegral d (countingTest d i)

theorem measurable_countingTestCode (d : ℕ) : Measurable (countingTestCode d) := by
  exact measurable_pi_lambda _ fun i => measurable_countingIntegral d (countingTest d i)

private theorem continuous_countingIntegral_induced (d : ℕ) (f : C_c(Rd d, ℝ)) :
    @Continuous (CountingConfiguration d) ℝ
      (TopologicalSpace.induced (countingTestCode d) inferInstance) inferInstance
      (fun μ => ∫ x, f x ∂μ.val) := by
  letI : TopologicalSpace (CountingConfiguration d) :=
    TopologicalSpace.induced (countingTestCode d) inferInstance
  have hcoord (i : ℕ ⊕ (ℕ × ℕ)) :
      Continuous (fun μ : CountingConfiguration d => countingTestCode d μ i) :=
    (continuous_apply i).comp (continuous_induced_dom (f := countingTestCode d))
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ) := fun x hx => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hR x hx).trans hn
  refine continuous_iff_continuousAt.2 fun μ => Metric.continuousAt_iff'.2 fun ε hε => ?_
  let M := (∫ x, countingMassCutoff d n x ∂μ.val) + 1
  have hM : 0 < M := add_pos_of_nonneg_of_pos
    (integral_nonneg (countingMassCutoff_spec d n).1) zero_lt_one
  obtain ⟨k, hk⟩ := (countingSupportedTest_spec d n).2 f hf (ε / (3 * M))
    (div_pos hε (mul_pos (by norm_num) hM))
  have herr (ν : CountingConfiguration d)
      (hν : (∫ x, countingMassCutoff d n x ∂ν.val) < M) :
      |(∫ x, f x ∂ν.val) - ∫ x, countingSupportedTest d n k x ∂ν.val| < ε / 3 := by
    calc
      _ ≤ ε / (3 * M) * ν.val.real (Metric.closedBall (0 : Rd d) (n : ℝ)) :=
        countingIntegral_sub_le d n ν f (countingSupportedTest d n k) _ hf
          ((countingSupportedTest_spec d n).1 k) (fun x => (hk x).le)
      _ < ε / (3 * M) * M := mul_lt_mul_of_pos_left
        ((countingMass_le_cutoff d n ν _ (countingMassCutoff_spec d n).1
          (countingMassCutoff_spec d n).2).trans_lt hν)
        (div_pos hε (mul_pos (by norm_num) hM))
      _ = ε / 3 := by field_simp
  have hcut : ∀ᶠ ν : CountingConfiguration d in 𝓝 μ,
      (∫ x, countingMassCutoff d n x ∂ν.val) < M :=
    Filter.Tendsto.eventually_lt_const (show countingTestCode d μ (Sum.inl n) < M
      from lt_add_one _) (hcoord (Sum.inl n)).continuousAt
  have hnear := (Metric.continuousAt_iff'.1
    ((hcoord (Sum.inr (n, k))).continuousAt (x := μ))) (ε / 3) (by positivity)
  filter_upwards [hcut, hnear] with ν hν hnear
  calc
    _ ≤ dist (∫ x, f x ∂ν.val) (∫ x, countingSupportedTest d n k x ∂ν.val) +
        dist (∫ x, countingSupportedTest d n k x ∂ν.val)
          (∫ x, countingSupportedTest d n k x ∂μ.val) +
        dist (∫ x, countingSupportedTest d n k x ∂μ.val) (∫ x, f x ∂μ.val) :=
      dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add
      (add_lt_add (by simpa only [Real.dist_eq] using herr ν hν) hnear)
      (by simpa only [Real.dist_eq, abs_sub_comm] using herr μ (lt_add_one _))
    _ = ε := by ring

/-- The countable test code induces the already defined vague topology. -/
theorem countingConfiguration_topology_eq_induced (d : ℕ) :
    (inferInstance : TopologicalSpace (CountingConfiguration d)) =
      TopologicalSpace.induced (countingTestCode d) inferInstance := by
  apply le_antisymm
  · exact continuous_iff_le_induced.1 (continuous_countingTestCode d)
  · letI : TopologicalSpace (CountingConfiguration d) :=
      TopologicalSpace.induced (countingTestCode d) inferInstance
    exact continuous_iff_le_induced.1
      (continuous_pi fun f => continuous_countingIntegral_induced d f)

/-- The countable code embeds the vague configuration space in a countable real product. -/
theorem countingTestCode_isEmbedding (d : ℕ) : Topology.IsEmbedding (countingTestCode d) := by
  exact (show Topology.IsInducing (countingTestCode d) from
    ⟨countingConfiguration_topology_eq_induced d⟩).isEmbedding

/-- The inherited Giry structure is exactly the Borel structure of the vague topology. -/
theorem countingConfiguration_measurableSpace_eq_borel (d : ℕ) :
    (inferInstance : MeasurableSpace (CountingConfiguration d)) =
      borel (CountingConfiguration d) := by
  refine le_antisymm (countingConfiguration_measurableSpace_le_borel d) ?_
  have hborel := congrArg (@borel (CountingConfiguration d))
    (countingConfiguration_topology_eq_induced d)
  rw [hborel, borel_comap]
  simpa only [BorelSpace.measurable_eq] using (measurable_countingTestCode d).comap_le

instance countingConfiguration_borelSpace (d : ℕ) : BorelSpace (CountingConfiguration d) :=
  ⟨countingConfiguration_measurableSpace_eq_borel d⟩

instance countingConfiguration_secondCountableTopology (d : ℕ) :
    SecondCountableTopology (CountingConfiguration d) :=
  (countingTestCode_isEmbedding d).secondCountableTopology

instance countingConfiguration_separableSpace (d : ℕ) :
    TopologicalSpace.SeparableSpace (CountingConfiguration d) :=
  (countingTestCode_isEmbedding d).separableSpace

instance countingConfiguration_metrizableSpace (d : ℕ) :
    TopologicalSpace.MetrizableSpace (CountingConfiguration d) :=
  (countingTestCode_isEmbedding d).metrizableSpace

end Riesz.Configuration
