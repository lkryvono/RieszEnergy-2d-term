import Riesz.Negative.DiffuseCells

/-!
The fixed half-unit decomposition of the diffuse part of the repaired cube
measure. On the good event this part has a positive lower density bound, so
every cell is nonzero and its indexing is independent of the random input.
The supporting sets below are disjoint half-open cells.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

def halfUnitDiffusePieces (d m : ℕ) (ν : FiniteMeasure (Rd d))
    (z : HalfUnitCellIndex d m) : FiniteMeasure (Rd d) :=
  ν.restrict (halfUnitCell d m z)

abbrev halfUnitDiffuseCount (d m : ℕ) : ℕ :=
  Fintype.card (HalfUnitCellIndex d m)

def halfUnitDiffuseEquiv (d m : ℕ) :
    Fin (halfUnitDiffuseCount d m) ≃ HalfUnitCellIndex d m :=
  (Fintype.equivFin (HalfUnitCellIndex d m)).symm

def halfUnitDiffuseRegions (d m : ℕ) (i : Fin (halfUnitDiffuseCount d m)) :
    Set (Rd d) :=
  halfUnitCell d m (halfUnitDiffuseEquiv d m i)

def halfUnitDiffuseMeasures (d m : ℕ) (ν : FiniteMeasure (Rd d))
    (i : Fin (halfUnitDiffuseCount d m)) : FiniteMeasure (Rd d) :=
  halfUnitDiffusePieces d m ν (halfUnitDiffuseEquiv d m i)

theorem measurable_halfUnitDiffusePieces (d m : ℕ) :
    Measurable (halfUnitDiffusePieces d m) := by
  refine measurable_pi_lambda _ (fun z => ?_)
  refine Measurable.subtype_mk ?_
  refine Measure.measurable_of_measurable_coe _ (fun D hD => ?_)
  simp only [Measure.restrict_apply hD]
  exact (Measure.measurable_coe (hD.inter (halfUnitCell_measurable d m z))).comp
    measurable_subtype_coe

theorem measurable_halfUnitDiffuseMeasures (d m : ℕ) :
    Measurable (halfUnitDiffuseMeasures d m) := by
  exact measurable_pi_lambda _ (fun i =>
    (measurable_pi_apply (halfUnitDiffuseEquiv d m i)).comp
      (measurable_halfUnitDiffusePieces d m))

theorem halfUnitDiffusePieces_sum (d m : ℕ) (ν : FiniteMeasure (Rd d)) :
    (∑ z : HalfUnitCellIndex d m,
      (halfUnitDiffusePieces d m ν z : Measure (Rd d))) =
        (ν : Measure (Rd d)).restrict (cube d (m : ℝ)) := by
  simpa only [halfUnitDiffusePieces, FiniteMeasure.restrict_measure_eq,
    Measure.sum_fintype, halfUnitCells_cover_cube d m] using
    (Measure.restrict_iUnion (μ := (ν : Measure (Rd d)))
      (halfUnitCells_pairwise_disjoint d m) (halfUnitCell_measurable d m)).symm

theorem halfUnitDiffusePieces_nonzero (d m : ℕ) (ν : FiniteMeasure (Rd d))
    (c : ℝ≥0∞) (hc : 0 < c)
    (hlo : c • volume.restrict (cube d (m : ℝ)) ≤ (ν : Measure (Rd d)))
    (z : HalfUnitCellIndex d m) : halfUnitDiffusePieces d m ν z ≠ 0 := by
  apply (FiniteMeasure.restrict_nonzero_iff ν (halfUnitCell d m z)).mpr
  have hbound := hlo (halfUnitCell d m z)
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_eq_self volume (halfUnitCell_subset_cube d m z), volume_halfUnitCell] at hbound
  exact fun hzero => (ne_of_gt ((ENNReal.mul_pos_iff.mpr
    ⟨hc, ENNReal.pow_pos (by norm_num : 0 < ENNReal.ofReal (1 / 2 : ℝ)) d⟩).trans_le hbound))
      ((FiniteMeasure.null_iff_toMeasure_null ν (halfUnitCell d m z)).mp hzero)

theorem halfUnitDiffusePieces_mass_le_one (d m : ℕ) (hd : 2 ≤ d)
    (ν : FiniteMeasure (Rd d))
    (hup : (ν : Measure (Rd d)) ≤ (2 : ℝ≥0∞) • volume.restrict (cube d (m : ℝ)))
    (z : HalfUnitCellIndex d m) : (halfUnitDiffusePieces d m ν z).mass ≤ 1 := by
  apply ENNReal.coe_le_coe.mp
  simp only [FiniteMeasure.ennreal_mass, halfUnitDiffusePieces,
    FiniteMeasure.restrict_measure_eq, Measure.restrict_apply_univ, ENNReal.coe_one]
  have hbound := hup (halfUnitCell d m z)
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_eq_self volume (halfUnitCell_subset_cube d m z)] at hbound
  exact hbound.trans (twice_volume_halfUnitCell_le_one d m hd z)

theorem halfUnitDiffusePieces_nullSingleton (d m : ℕ) (hd : 2 ≤ d)
    (ν : FiniteMeasure (Rd d))
    (hup : (ν : Measure (Rd d)) ≤ (2 : ℝ≥0∞) • volume.restrict (cube d (m : ℝ)))
    (z : HalfUnitCellIndex d m) (y : Rd d) : halfUnitDiffusePieces d m ν z {y} = 0 := by
  haveI := cube_background_nullSingletonClass d m (lt_of_lt_of_le (by norm_num) hd)
  apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
  have hpiece : (halfUnitDiffusePieces d m ν z : Measure (Rd d)) ≤
      (2 : ℝ≥0∞) • volume.restrict (cube d (m : ℝ)) :=
    Measure.restrict_le_self.trans hup
  exact le_antisymm (by simpa only [Measure.smul_apply, measure_singleton, smul_zero]
    using (hpiece {y})) zero_le

theorem halfUnitDiffusePieces_concentrated (d m : ℕ) (ν : FiniteMeasure (Rd d))
    (z : HalfUnitCellIndex d m) :
    halfUnitDiffusePieces d m ν z (halfUnitCell d m z)ᶜ = 0 := by
  apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
  simp only [halfUnitDiffusePieces, FiniteMeasure.restrict_measure_eq,
    Measure.restrict_apply (halfUnitCell_measurable d m z).compl,
    Set.compl_inter_self, measure_empty]

theorem halfUnitDiffuseMeasures_sum (d m : ℕ) (ν : FiniteMeasure (Rd d))
    (hup : (ν : Measure (Rd d)) ≤ (2 : ℝ≥0∞) • volume.restrict (cube d (m : ℝ))) :
    cellMeasureSum d (halfUnitDiffuseCount d m) (halfUnitDiffuseMeasures d m ν) =
      (ν : Measure (Rd d)) := by
  change (∑ i, (halfUnitDiffusePieces d m ν (halfUnitDiffuseEquiv d m i) :
    Measure (Rd d))) = (ν : Measure (Rd d))
  rw [(halfUnitDiffuseEquiv d m).sum_comp
    (fun z => (halfUnitDiffusePieces d m ν z : Measure (Rd d))), halfUnitDiffusePieces_sum]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  apply le_antisymm ?_ zero_le
  have hbound := hup (cube d (m : ℝ))ᶜ
  simp only [Measure.smul_apply,
    Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
    Set.compl_inter_self, measure_empty, smul_zero] at hbound
  exact hbound

theorem halfUnitDiffuseMeasures_mass_sum (d m : ℕ) (ν : FiniteMeasure (Rd d))
    (hup : (ν : Measure (Rd d)) ≤ (2 : ℝ≥0∞) • volume.restrict (cube d (m : ℝ))) :
    (∑ i, ((halfUnitDiffuseMeasures d m ν i).mass : ℝ)) = (ν.mass : ℝ) := by
  rw [← cellMeasureSum_real_univ, halfUnitDiffuseMeasures_sum d m ν hup]
  rfl

/-- The continuous-cell hypotheses of the sampling-and-rounding estimate,
derived from domination of the actual diffuse measure on the good event. -/
theorem halfUnitDiffuseMeasures_sampling_inputs (d m : ℕ) (hd : 2 ≤ d)
    (ν : FiniteMeasure (Rd d)) (c : ℝ≥0∞) (hc : 0 < c)
    (hlo : c • volume.restrict (cube d (m : ℝ)) ≤ (ν : Measure (Rd d)))
    (hup : (ν : Measure (Rd d)) ≤ (2 : ℝ≥0∞) • volume.restrict (cube d (m : ℝ))) :
    (∀ i, halfUnitDiffuseMeasures d m ν i ≠ 0) ∧
    (∀ i, (halfUnitDiffuseMeasures d m ν i).mass ≤ 1) ∧
    (∀ i y, halfUnitDiffuseMeasures d m ν i {y} = 0) ∧
    (∀ i, halfUnitDiffuseMeasures d m ν i (halfUnitDiffuseRegions d m i)ᶜ = 0) ∧
    (∀ i j, i ≠ j → Disjoint (halfUnitDiffuseRegions d m i)
      (halfUnitDiffuseRegions d m j)) ∧
    (∀ i, halfUnitDiffuseRegions d m i ⊆ cube d (m : ℝ)) ∧
    (∀ i, ∀ y ∈ halfUnitDiffuseRegions d m i,
      ∀ z ∈ halfUnitDiffuseRegions d m i, ‖y - z‖ ≤ Real.sqrt d * (1 / 2)) := by
  exact ⟨fun i => halfUnitDiffusePieces_nonzero d m ν c hc hlo _,
    fun i => halfUnitDiffusePieces_mass_le_one d m hd ν hup _,
    fun i y => halfUnitDiffusePieces_nullSingleton d m hd ν hup _ y,
    fun i => halfUnitDiffusePieces_concentrated d m ν _,
    fun i j hij => halfUnitCells_pairwise_disjoint d m
      (fun h => hij ((halfUnitDiffuseEquiv d m).injective h)),
    fun i => halfUnitCell_subset_cube d m _,
    fun i y hy z hz => halfUnitCell_diameter_le d m _ y z hy hz⟩

end Riesz.Negative
