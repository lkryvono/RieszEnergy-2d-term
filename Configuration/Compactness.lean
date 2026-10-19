import Riesz.Configuration.Topology
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Compact images of weighted finite tuples for local counting limits. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Configuration

/-- A finite weighted tuple, retaining all repeated sites. -/
def weightedTupleMeasure (d n : ℕ) (χ : C_c(Rd d, ℝ))
    (x : Fin n → Rd d) : FiniteMeasure (Rd d) :=
  ∑ i, Real.toNNReal (χ (x i)) • (diracProba (x i)).toFiniteMeasure

theorem continuous_weightedTupleMeasure (d n : ℕ) (χ : C_c(Rd d, ℝ)) :
    Continuous (weightedTupleMeasure d n χ) := by
  unfold weightedTupleMeasure
  exact continuous_finsetSum _ fun i _ =>
    (continuous_real_toNNReal.comp (χ.continuous.comp (continuous_apply i))).smul
      (ProbabilityMeasure.toFiniteMeasure_continuous.comp
        (continuous_diracProba.comp (continuous_apply i)))

theorem isCompact_weightedTupleMeasure_range (d n : ℕ) (χ : C_c(Rd d, ℝ))
    (K : Set (Rd d)) (hK : IsCompact K) :
    IsCompact (Set.range (fun x : Fin n → K =>
      weightedTupleMeasure d n χ (fun i => (x i).val))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isCompact_range ((continuous_weightedTupleMeasure d n χ).comp
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)))

/-- Weighted tuple measures with a bounded number of sites in one compact set. -/
def boundedWeightedTupleMeasures (d : ℕ) (χ : C_c(Rd d, ℝ))
    (K : Set (Rd d)) (N : ℕ) : Set (FiniteMeasure (Rd d)) :=
  ⋃ n ∈ Set.Iic N, Set.range (fun x : Fin n → K =>
    weightedTupleMeasure d n χ (fun i => (x i).val))

theorem isCompact_boundedWeightedTupleMeasures (d : ℕ) (χ : C_c(Rd d, ℝ))
    (K : Set (Rd d)) (hK : IsCompact K) (N : ℕ) :
    IsCompact (boundedWeightedTupleMeasures d χ K N) := by
  exact (Set.finite_Iic N).isCompact_biUnion
    (fun n _ => isCompact_weightedTupleMeasure_range d n χ K hK)

theorem weightedTupleMeasure_toMeasure (d n : ℕ) (χ : C_c(Rd d, ℝ))
    (x : Fin n → Rd d) :
    (weightedTupleMeasure d n χ x : Measure (Rd d)) =
      (Riesz.Negative.tupleCounting d n x).withDensity (fun y => ENNReal.ofReal (χ y)) := by
  simp only [weightedTupleMeasure, FiniteMeasure.toMeasure_sum, FiniteMeasure.toMeasure_smul]
  conv_rhs => rw [Riesz.Negative.tupleCounting, ← Measure.sum_fintype,
    withDensity_sum, Measure.sum_fintype]
  simp [dirac_withDensity, diracProba, ENNReal.ofReal]

theorem finiteCountingOn_tupleCounting (d n : ℕ) (x : Fin n → Rd d)
    (K : Set (Rd d)) : FiniteCountingOn d K (Riesz.Negative.tupleCounting d n x) := by
  refine ⟨Fintype.card {i : Fin n // x i ∈ K},
    fun j => x ((Fintype.equivFin {i : Fin n // x i ∈ K}).symm j), ?_⟩
  rw [Riesz.Negative.tupleCounting, ← Measure.sum_fintype,
    Measure.restrict_sum_of_countable, Measure.sum_fintype]
  simp only [restrict_dirac, Riesz.Negative.tupleCounting]
  rw [← Finset.sum_filter,
    Finset.sum_subtype (p := fun i => x i ∈ K) (F := inferInstance) _ (by simp)]
  exact ((Fintype.equivFin {i : Fin n // x i ∈ K}).symm.sum_comp
    (fun i => Measure.dirac (x i.val))).symm

theorem restrict_withDensity_of_eqOn_one (d : ℕ) (μ : Measure (Rd d))
    (χ : C_c(Rd d, ℝ)) (K : Set (Rd d)) (hK : MeasurableSet K)
    (hχ1 : Set.EqOn χ 1 K) :
    (μ.withDensity (fun y => ENNReal.ofReal (χ y))).restrict K = μ.restrict K := by
  rw [restrict_withDensity hK]
  have hχ : (fun y => ENNReal.ofReal (χ y)) =ᵐ[μ.restrict K] 1 :=
    (ae_restrict_mem hK).mono fun y hy => by simp [hχ1 hy]
  rw [withDensity_congr_ae hχ, withDensity_one]

theorem finiteCountingOn_of_weightedTupleMeasure (d n : ℕ) (μ : Measure (Rd d))
    (χ : C_c(Rd d, ℝ)) (K : Set (Rd d)) (hK : MeasurableSet K)
    (hχ1 : Set.EqOn χ 1 K) (x : Fin n → Rd d)
    (hμ : μ.withDensity (fun y => ENNReal.ofReal (χ y)) =
      (weightedTupleMeasure d n χ x : Measure (Rd d))) : FiniteCountingOn d K μ := by
  have hr := congrArg (fun ν : Measure (Rd d) => ν.restrict K) hμ
  rw [weightedTupleMeasure_toMeasure,
    restrict_withDensity_of_eqOn_one d _ χ K hK hχ1,
    restrict_withDensity_of_eqOn_one d _ χ K hK hχ1] at hr
  rcases finiteCountingOn_tupleCounting d n x K with ⟨m, y, hy⟩
  exact ⟨m, y, hr.trans hy⟩

theorem finiteCountingOn_of_tendsto_boundedWeightedTupleMeasures
    {α : Type*} (d : ℕ) (μ : Measure (Rd d)) (χ : C_c(Rd d, ℝ))
    (K L : Set (Rd d)) (hK : MeasurableSet K) (hχ1 : Set.EqOn χ 1 K)
    (hL : IsCompact L) (N : ℕ) (l : Filter α) [l.NeBot]
    (v : α → FiniteMeasure (Rd d)) (ρ : FiniteMeasure (Rd d))
    (hρ : μ.withDensity (fun y => ENNReal.ofReal (χ y)) = (ρ : Measure (Rd d)))
    (hv : Filter.Tendsto v l (𝓝 ρ))
    (hb : ∀ᶠ i in l, v i ∈ boundedWeightedTupleMeasures d χ L N) :
    FiniteCountingOn d K μ := by
  have hm := (isCompact_boundedWeightedTupleMeasures d χ L hL N).isClosed.mem_of_tendsto hv hb
  rcases Set.mem_iUnion.mp hm with ⟨n, hn⟩
  rcases Set.mem_iUnion.mp hn with ⟨_, x, hx⟩
  exact finiteCountingOn_of_weightedTupleMeasure d n μ χ K hK hχ1
    (fun i => (x i).val) (hρ.trans (congrArg (fun ν : FiniteMeasure (Rd d) =>
      (ν : Measure (Rd d))) hx).symm)

/-- A compact cutoff turns a locally finite measure into a finite measure. -/
def cutoffMeasure (d : ℕ) (μ : Measure (Rd d)) [IsFiniteMeasureOnCompacts μ]
    (χ : C_c(Rd d, ℝ)) : FiniteMeasure (Rd d) :=
  ⟨μ.withDensity (fun y => ENNReal.ofReal (χ y)),
    isFiniteMeasure_withDensity_ofReal χ.integrable.hasFiniteIntegral⟩

theorem integral_cutoffMeasure (d : ℕ) (μ : Measure (Rd d))
    [IsFiniteMeasureOnCompacts μ] (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (f : Rd d → ℝ) :
    (∫ x, f x ∂(cutoffMeasure d μ χ : Measure (Rd d))) = ∫ x, χ x * f x ∂μ := by
  change (∫ x, f x ∂μ.withDensity (fun y => ENNReal.ofReal (χ y))) = _
  simpa [ENNReal.toReal_ofReal, hχ, smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul (μ := μ)
      χ.continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f

theorem tendsto_cutoffMeasure_of_tendsto_integral {α : Type*} (d : ℕ)
    (u : α → CountingConfiguration d) (l : Filter α) (μ : Measure (Rd d))
    [IsFiniteMeasureOnCompacts μ]
    (h : ∀ f : C_c(Rd d, ℝ), Filter.Tendsto (fun i => ∫ x, f x ∂(u i).val)
      l (𝓝 (∫ x, f x ∂μ)))
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) :
    Filter.Tendsto (fun i => cutoffMeasure d (u i).val χ) l (𝓝 (cutoffMeasure d μ χ)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let g : C_c(Rd d, ℝ) :=
    ⟨⟨fun x => χ x * f x, χ.continuous.mul f.continuous⟩, χ.hasCompactSupport.mul_right⟩
  simpa [g, integral_cutoffMeasure d _ χ hχ] using h g

theorem cutoffMeasure_eq_weightedTupleMeasure (d n : ℕ) (μ : Measure (Rd d))
    [IsFiniteMeasureOnCompacts μ] (χ : C_c(Rd d, ℝ)) (L : Set (Rd d))
    (hL : MeasurableSet L) (hχ : tsupport χ ⊆ L) (x : Fin n → Rd d)
    (hμ : μ.restrict L = Riesz.Negative.tupleCounting d n x) :
    cutoffMeasure d μ χ = weightedTupleMeasure d n χ x := by
  apply FiniteMeasure.toMeasure_injective
  change μ.withDensity (fun y => ENNReal.ofReal (χ y)) = _
  rw [weightedTupleMeasure_toMeasure, ← hμ, ← withDensity_indicator hL]
  congr 1
  apply (Set.indicator_eq_self.mpr _).symm
  intro y hy
  exact hχ (subset_tsupport χ (fun h0 => hy (by simp [h0])))

theorem cutoffMeasure_mem_boundedWeightedTupleMeasures (d m N : ℕ)
    (μ : CountingConfiguration d) (χ : C_c(Rd d, ℝ))
    (hχ : tsupport χ ⊆ Metric.closedBall (0 : Rd d) (m : ℝ))
    (hb : μ.val.real (Metric.closedBall (0 : Rd d) (m : ℝ)) ≤ N) :
    cutoffMeasure d μ.val χ ∈ boundedWeightedTupleMeasures d χ
      (Metric.closedBall (0 : Rd d) (m : ℝ)) N := by
  rcases μ.property m with ⟨n, x, hμ⟩
  have hx : ∀ i, x i ∈ Metric.closedBall (0 : Rd d) (m : ℝ) :=
    (Riesz.Negative.tupleCounting_compl_eq_zero_iff d n x _
      Metric.isClosed_closedBall.measurableSet).mp (by
        rw [← hμ, Measure.restrict_apply Metric.isClosed_closedBall.measurableSet.compl]
        simp)
  have hm : μ.val (Metric.closedBall (0 : Rd d) (m : ℝ)) = (n : ℝ≥0∞) := by
    simpa only [Measure.restrict_apply_univ, Riesz.Negative.tupleCounting_univ] using
      congrArg (fun ν : Measure (Rd d) => ν Set.univ) hμ
  have hn : n ≤ N := by simpa only [Measure.real, hm, ENNReal.toReal_natCast,
    Nat.cast_le] using hb
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hn,
    ⟨fun i => ⟨x i, hx i⟩, (cutoffMeasure_eq_weightedTupleMeasure d n μ.val χ _
      Metric.isClosed_closedBall.measurableSet hχ x hμ).symm⟩⟩⟩

theorem eventually_countingMass_le_nat_of_tendsto_integral {α : Type*} (d m : ℕ)
    (u : α → CountingConfiguration d) (l : Filter α) (μ : Measure (Rd d))
    (h : ∀ f : C_c(Rd d, ℝ), Filter.Tendsto (fun i => ∫ x, f x ∂(u i).val)
      l (𝓝 (∫ x, f x ∂μ))) :
    ∃ N : ℕ, ∀ᶠ i in l, (u i).val.real (Metric.closedBall (0 : Rd d) (m : ℝ)) ≤ N := by
  obtain ⟨N, hN⟩ := exists_nat_gt (∫ x, countingMassCutoff d m x ∂μ)
  refine ⟨N, ((h (countingMassCutoff d m)).eventually (eventually_lt_nhds hN)).mono ?_⟩
  exact fun i hi => (countingMass_le_cutoff d m (u i) (countingMassCutoff d m)
    (countingMassCutoff_spec d m).1 (countingMassCutoff_spec d m).2).trans hi.le

/-- Vague limits which are locally finite retain integer multiplicities. -/
theorem isCountingConfiguration_of_tendsto_integral {α : Type*} (d : ℕ)
    (u : α → CountingConfiguration d) (l : Filter α) [l.NeBot]
    (μ : Measure (Rd d)) [IsFiniteMeasureOnCompacts μ]
    (h : ∀ f : C_c(Rd d, ℝ), Filter.Tendsto (fun i => ∫ x, f x ∂(u i).val)
      l (𝓝 (∫ x, f x ∂μ))) : IsCountingConfiguration d μ := by
  intro k
  obtain ⟨R, hR⟩ := (countingMassCutoff d k).hasCompactSupport.isBounded.exists_norm_le
  obtain ⟨m, hm⟩ := exists_nat_ge R
  have hχ : tsupport (countingMassCutoff d k) ⊆ Metric.closedBall (0 : Rd d) (m : ℝ) :=
    fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using (hR x hx).trans hm
  obtain ⟨N, hN⟩ := eventually_countingMass_le_nat_of_tendsto_integral d m u l μ h
  exact finiteCountingOn_of_tendsto_boundedWeightedTupleMeasures d μ (countingMassCutoff d k)
    _ _ Metric.isClosed_closedBall.measurableSet (countingMassCutoff_spec d k).2
    (isCompact_closedBall (0 : Rd d) (m : ℝ)) N l
    (fun i => cutoffMeasure d (u i).val (countingMassCutoff d k))
    (cutoffMeasure d μ (countingMassCutoff d k)) rfl
    (tendsto_cutoffMeasure_of_tendsto_integral d u l μ h _ (countingMassCutoff_spec d k).1)
    (hN.mono (fun i hi => cutoffMeasure_mem_boundedWeightedTupleMeasures d m N (u i) _ hχ hi))

end Riesz.Configuration
