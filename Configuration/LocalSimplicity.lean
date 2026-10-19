import Riesz.Negative.Sampling

/-! Measurable local criteria for the showcase's simple configuration class.
Finite restrictions use the already verified finite counting-measure classes. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Configuration

/-- A restriction has finitely many distinct sites, all of weight one. -/
def FiniteSimpleOn (d : ℕ) (K : Set (Rd d)) (μ : Measure (Rd d)) : Prop :=
  ∃ n : ℕ, ∃ x : Fin n → Rd d,
    Function.Injective x ∧ μ.restrict K = Riesz.Negative.tupleCounting d n x

/-- Integer-radius closed balls give a countable local criterion. -/
def LocallySimple (d : ℕ) (μ : Measure (Rd d)) : Prop :=
  ∀ k : ℕ, FiniteSimpleOn d (Metric.closedBall (0 : Rd d) (k : ℝ)) μ

def atomSites (d : ℕ) (μ : Measure (Rd d)) : Set (Rd d) :=
  {x | μ {x} = 1}

theorem tupleCounting_singleton_one (d n : ℕ) (x : Fin n → Rd d)
    (hx : Function.Injective x) (i : Fin n) :
    Riesz.Negative.tupleCounting d n x {x i} = 1 := by
  simp [Riesz.Negative.tupleCounting, Measure.finsetSum_apply, Set.indicator, hx.eq_iff]

theorem finiteSimpleOn_sites (d n : ℕ) (μ : Measure (Rd d)) (K : Set (Rd d))
    (x : Fin n → Rd d) (hx : Function.Injective x)
    (hμ : μ.restrict K = Riesz.Negative.tupleCounting d n x) :
    ∀ i, x i ∈ atomSites d μ := by
  intro i
  have hs := (congrArg (fun ν : Measure (Rd d) => ν {x i}) hμ).trans
    (tupleCounting_singleton_one d n x hx i)
  have hmem : x i ∈ K := by
    by_contra hi
    simp [Measure.restrict_apply (measurableSet_singleton _), hi] at hs
  exact (Measure.restrict_eq_self μ (Set.singleton_subset_iff.mpr hmem)).symm.trans hs

theorem finiteSimpleOn_ae_mem_sites (d : ℕ) (μ : Measure (Rd d)) (K : Set (Rd d))
    (hμ : FiniteSimpleOn d K μ) : ∀ᵐ x ∂μ.restrict K, x ∈ atomSites d μ := by
  rcases hμ with ⟨n, x, hx, h⟩
  simpa [h, Riesz.Negative.tupleCounting] using finiteSimpleOn_sites d n μ K x hx h

theorem measurable_restrict (d : ℕ) (K : Set (Rd d)) (hK : MeasurableSet K) :
    Measurable (fun μ : Measure (Rd d) => μ.restrict K) := by
  refine Measure.measurable_of_measurable_coe _ (fun D hD => ?_)
  simpa only [Measure.restrict_apply hD] using Measure.measurable_coe (hD.inter hK)

theorem measurableSet_finiteSimpleOn (d : ℕ) (K : Set (Rd d)) (hK : MeasurableSet K) :
    MeasurableSet {μ : Measure (Rd d) | FiniteSimpleOn d K μ} := by
  simpa [FiniteSimpleOn, Set.setOf_exists] using
    MeasurableSet.iUnion (fun n : ℕ =>
      (Riesz.Negative.measurableSet_simple_counting_class d n).preimage
        (measurable_restrict d K hK))

theorem measurableSet_locallySimple (d : ℕ) :
    MeasurableSet {μ : Measure (Rd d) | LocallySimple d μ} := by
  simpa only [LocallySimple, Set.setOf_forall] using
    MeasurableSet.iInter (fun k : ℕ => measurableSet_finiteSimpleOn d
      (Metric.closedBall (0 : Rd d) (k : ℝ)) measurableSet_closedBall)

theorem locallySimple_sites_locallyFinite (d : ℕ) (μ : Measure (Rd d))
    (hμ : LocallySimple d μ) :
    ∀ K : Set (Rd d), IsCompact K → (atomSites d μ ∩ K).Finite := by
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨k, hk⟩ := exists_nat_ge R
  rcases hμ k with ⟨n, x, hx, h⟩
  apply (Set.finite_range x).subset
  rintro y ⟨hy, hyK⟩
  have hb : y ∈ Metric.closedBall (0 : Rd d) (k : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hR y hyK).trans hk
  apply (Riesz.Negative.tupleCounting_singleton_ne_zero_iff d n x y).mp
  rw [← h, Measure.restrict_eq_self μ (Set.singleton_subset_iff.mpr hb),
    (show μ {y} = 1 from hy)]
  exact one_ne_zero

theorem locallySimple_sites_countable (d : ℕ) (μ : Measure (Rd d)) (hμ : LocallySimple d μ) :
    (atomSites d μ).Countable := by
  simpa only [← Set.inter_iUnion, Metric.iUnion_closedBall_nat, Set.inter_univ] using
    Set.countable_iUnion (fun k : ℕ => (locallySimple_sites_locallyFinite d μ hμ
      (Metric.closedBall (0 : Rd d) (k : ℝ)) (isCompact_closedBall _ _)).countable)

theorem locallySimple_ae_mem_sites (d : ℕ) (μ : Measure (Rd d)) (hμ : LocallySimple d μ) :
    ∀ᵐ x ∂μ, x ∈ atomSites d μ := by
  have h := (ae_restrict_iUnion_iff
    (fun k : ℕ => Metric.closedBall (0 : Rd d) (k : ℝ))
    (fun x => x ∈ atomSites d μ)).mpr (fun k => finiteSimpleOn_ae_mem_sites d μ _ (hμ k))
  simpa only [Metric.iUnion_closedBall_nat, Measure.restrict_univ] using h

theorem locallySimple_eq_sum (d : ℕ) (μ : Measure (Rd d)) (hμ : LocallySimple d μ) :
    μ = Measure.sum (fun x : atomSites d μ => Measure.dirac x.val) := by
  have hc := locallySimple_sites_countable d μ hμ
  letI := hc.toEncodable
  have hmap := map_comap_subtype_coe hc.measurableSet μ
  rw [Measure.restrict_eq_self_of_ae_mem (locallySimple_ae_mem_sites d μ hμ)] at hmap
  have hweights (x : atomSites d μ) :
      (μ.comap ((↑) : atomSites d μ → Rd d)) {x} = 1 := by
    rw [comap_subtype_coe_apply hc.measurableSet, Set.image_singleton]
    exact x.property
  rw [← Measure.sum_smul_dirac (μ.comap ((↑) : atomSites d μ → Rd d))] at hmap
  simpa only [Measure.map_sum measurable_subtype_coe.aemeasurable, Measure.map_smul,
    Measure.map_dirac' measurable_subtype_coe, hweights, one_smul] using hmap.symm

theorem restrict_sum_dirac (d : ℕ) (S K : Set (Rd d)) (hK : MeasurableSet K) :
    (Measure.sum (fun x : S => Measure.dirac x.val)).restrict K =
      Measure.sum (fun x : ↥(S ∩ K) => Measure.dirac x.val) := by
  ext D hD : 1
  rw [Measure.restrict_apply hD, Measure.sum_apply _ (hD.inter hK), Measure.sum_apply _ hD]
  let e : {x : S // x.val ∈ K} ≃ ↥(S ∩ K) :=
    ⟨fun x => ⟨x.val.val, x.val.property, x.property⟩,
      fun y => ⟨⟨y.val, y.property.1⟩, y.property.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [← e.tsum_eq (fun y : ↥(S ∩ K) => (Measure.dirac y.val) D)]
  erw [tsum_subtype {x : S | x.val ∈ K} (fun x : S => (Measure.dirac x.val) D)]
  refine tsum_congr (fun x => ?_)
  by_cases hx : x.val ∈ K <;> simp [Measure.dirac_apply', hD, hK, Set.indicator, hx]

theorem simple_locallySimple (d : ℕ) (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ) : LocallySimple d μ := by
  rcases hμ with ⟨S, hS, rfl⟩
  intro k
  let T := S ∩ Metric.closedBall (0 : Rd d) (k : ℝ)
  have hT : T.Finite := hS _ (isCompact_closedBall _ _)
  letI := hT.fintype
  have hrest := restrict_sum_dirac d S (Metric.closedBall (0 : Rd d) (k : ℝ))
    measurableSet_closedBall
  refine ⟨Fintype.card T, Riesz.Negative.simple_fixed_count_representation d
    (Fintype.card T) _ ⟨T, fun K _ => hT.inter_of_left K, hrest⟩ ?_⟩
  simp [hrest, T]

theorem locallySimple_iff_simple (d : ℕ) (μ : Measure (Rd d)) :
    LocallySimple d μ ↔ IsSimpleConfiguration d μ := by
  exact ⟨fun h => ⟨atomSites d μ, locallySimple_sites_locallyFinite d μ h,
    locallySimple_eq_sum d μ h⟩, simple_locallySimple d μ⟩

/-- The full simple event is Borel in the Giry measurable structure. -/
theorem measurableSet_isSimpleConfiguration (d : ℕ) :
    MeasurableSet {μ : Measure (Rd d) | IsSimpleConfiguration d μ} := by
  simpa only [← locallySimple_iff_simple] using measurableSet_locallySimple d

end Riesz.Configuration
