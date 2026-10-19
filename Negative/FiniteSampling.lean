import Riesz.Negative.CellSampling
import Riesz.Configuration.UniformSampling
import Mathlib.MeasureTheory.Constructions.Pi

/-! Finite simultaneous sampling of continuous cells on a fixed product
sample space. These samples are the sites used by atomic discretization. -/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Configuration
open scoped ENNReal Classical

namespace Riesz.Negative

def uniformCellMarks (n : ℕ) : Measure (Fin n → unitInterval) :=
  Measure.pi (fun _ : Fin n => (volume : Measure unitInterval))

instance uniformCellMarks_probability (n : ℕ) : IsProbabilityMeasure (uniformCellMarks n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi
    (fun _ : Fin n => (volume : Measure unitInterval))))

def sampledCellSites (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d))
    (u : Fin n → unitInterval) : Fin n → Rd d :=
  fun i => sampleFiniteMeasure (ν i) (u i)

theorem measurable_sampledCellSites (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d)) :
    Measurable (sampledCellSites d n ν) := by
  exact measurable_pi_lambda _ (fun i =>
    (measurable_sampleFiniteMeasure_fixed (ν i)).comp (measurable_pi_apply i))

theorem sampledCellSites_coordinate_measurePreserving (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (i : Fin n) :
    MeasurePreserving (fun u => sampledCellSites d n ν u i)
      (uniformCellMarks n) ((ν i).normalize : Measure (Rd d)) := by
  exact (measurePreserving_sampleFiniteMeasure (ν i)).comp
    (measurePreserving_eval (fun _ : Fin n => (volume : Measure unitInterval)) i)

theorem sampledCellSites_map (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d)) :
    Measure.map (sampledCellSites d n ν) (uniformCellMarks n) =
      Measure.pi (fun i => ((ν i).normalize : Measure (Rd d))) := by
  change Measure.map (fun u i => sampleFiniteMeasure (ν i) (u i))
    (Measure.pi (fun _ : Fin n => (volume : Measure unitInterval))) = _
  simpa only [sampleFiniteMeasure_map] using
    (Measure.pi_map_pi (μ := fun _ : Fin n => (volume : Measure unitInterval))
      (f := fun i => sampleFiniteMeasure (ν i))
      (fun i => (measurable_sampleFiniteMeasure_fixed (ν i)).aemeasurable))

theorem jointly_measurable_sampledCellSites {X : Type*} [MeasurableSpace X]
    (d n : ℕ) (ν : X → Fin n → FiniteMeasure (Rd d)) (hν : Measurable ν) :
    Measurable (fun p : X × (Fin n → unitInterval) => sampledCellSites d n (ν p.1) p.2) := by
  exact measurable_pi_lambda _ (fun i => measurable_sampleFiniteMeasure.comp
    (((measurable_pi_apply i).comp (hν.comp measurable_fst)).prodMk
      ((measurable_pi_apply i).comp measurable_snd)))

theorem measurable_cellSampleAtom (d : ℕ) (ν : FiniteMeasure (Rd d)) :
    Measurable (cellSampleAtom d ν) := by
  refine Measure.measurable_of_measurable_coe _ (fun D hD => ?_)
  change Measurable (fun b : Rd d => (ν.mass : ENNReal) * Measure.dirac b D)
  exact (measurable_const (a := (ν.mass : ENNReal))).mul
    ((Measure.measurable_coe hD).comp (Measure.measurable_dirac (α := Rd d)))

theorem sampledCellSites_atom_mean (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d))
    (i : Fin n) (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ u, cellSampleAtom d (ν i) (sampledCellSites d n ν u i) D
      ∂uniformCellMarks n) = (ν i) D := by
  exact ((sampledCellSites_coordinate_measurePreserving d n ν i).lintegral_comp
    (show Measurable (fun y : Rd d => cellSampleAtom d (ν i) y D) from
      (Measure.measurable_coe hD).comp (measurable_cellSampleAtom d (ν i)))).trans
    (cellSampleAtom_mean d (ν i) D hD)

theorem weightedAtomicMeasure_sampledCellSites_eq (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (u : Fin n → unitInterval) :
    weightedAtomicMeasure d n (sampledCellSites d n ν u) (fun i => ((ν i).mass : ℝ)) =
      ∑ i, cellSampleAtom d (ν i) (sampledCellSites d n ν u i) := by
  simp [weightedAtomicMeasure, cellSampleAtom]

theorem sampledCellSites_full_mean (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d))
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ u, weightedAtomicMeasure d n (sampledCellSites d n ν u)
      (fun i => ((ν i).mass : ℝ)) D ∂uniformCellMarks n) =
      (∑ i, (ν i : Measure (Rd d))) D := by
  simp_rw [weightedAtomicMeasure_sampledCellSites_eq, Measure.finsetSum_apply]
  rw [lintegral_finsetSum (f := fun (i : Fin n) (u : Fin n → unitInterval) =>
    cellSampleAtom d (ν i) (sampledCellSites d n ν u i) D) Finset.univ (fun i _ =>
    (Measure.measurable_coe hD).comp ((measurable_cellSampleAtom d (ν i)).comp
      ((measurable_pi_apply i).comp (measurable_sampledCellSites d n ν))))]
  exact Finset.sum_congr rfl (fun i _ =>
    (sampledCellSites_atom_mean d n ν i D hD).trans
      ((ν i).ennreal_coeFn_eq_coeFn_toMeasure D))

theorem sampledCellSites_supported (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d))
    (hν : ∀ i, ν i ≠ 0) (B : Fin n → Set (Rd d))
    (hsupport : ∀ i, ν i (B i)ᶜ = 0) :
    ∀ᵐ u ∂uniformCellMarks n, ∀ i, sampledCellSites d n ν u i ∈ B i := by
  exact ae_all_iff.mpr (fun i =>
    (sampledCellSites_coordinate_measurePreserving d n ν i).quasiMeasurePreserving.ae
      (cellSampleLaw_supported d (ν i) (hν i) (B i) (hsupport i)))

theorem sampledCellSites_avoid_finite (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d))
    (hν : ∀ i, ν i ≠ 0) (hatom : ∀ i y, ν i {y} = 0) (S : Finset (Rd d)) :
    ∀ᵐ u ∂uniformCellMarks n, ∀ i, sampledCellSites d n ν u i ∉ S := by
  exact ae_all_iff.mpr (fun i =>
    (sampledCellSites_coordinate_measurePreserving d n ν i).quasiMeasurePreserving.ae
      (cellSampleLaw_avoids_finite d (ν i) (hν i) (hatom i) S))

theorem sampledCellSites_injective (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d))
    (hν : ∀ i, ν i ≠ 0) (B : Fin n → Set (Rd d))
    (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    ∀ᵐ u ∂uniformCellMarks n, Function.Injective (sampledCellSites d n ν u) := by
  filter_upwards [sampledCellSites_supported d n ν hν B hsupport] with u hu
  exact fun i j hij => Classical.byContradiction (fun hne =>
    (Set.disjoint_left.mp (hdisjoint i j hne)) (hu i) (hij.symm ▸ hu j))

theorem sampledCellSites_cell_energy_budget (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hatom : ∀ i y, ν i {y} = 0) (q : ℝ) (hq : 0 < q)
    (L : Fin n → ℝ) (hL : ∀ i, 0 ≤ L i) (B : Fin n → Set (Rd d))
    (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdiam : ∀ i, ∀ x ∈ B i, ∀ z ∈ B i, ‖x - z‖ ≤ L i) :
    ∀ᵐ u ∂uniformCellMarks n,
      (∑ i, Riesz.Analysis.signedDiscrepancyEnergy q
        (cellSampleIncrement d (ν i) (sampledCellSites d n ν u i))) ≤
        ∑ i, (L i) ^ q * (2 * ((ν i).mass : ℝ)) ^ 2 / q := by
  filter_upwards [sampledCellSites_supported d n ν hν B hsupport] with u hu
  exact Finset.sum_le_sum (fun i _ => cellSampleIncrement_energy_le d (ν i)
    (hatom i) q (L i) hq (hL i) (B i) (hsupport i) (hdiam i)
    (sampledCellSites d n ν u i) (hu i))

theorem sampledCellSites_append_injective (d r n : ℕ)
    (x : Fin r → Rd d) (hx : Function.Injective x)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hatom : ∀ i y, ν i {y} = 0) (B : Fin n → Set (Rd d))
    (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    ∀ᵐ u ∂uniformCellMarks n,
      Function.Injective (Fin.append x (sampledCellSites d n ν u)) := by
  filter_upwards [sampledCellSites_injective d n ν hν B hsupport hdisjoint,
    sampledCellSites_avoid_finite d n ν hν hatom (Finset.univ.image x)] with u hu havoid
  exact Fin.append_injective_iff.mpr ⟨hx, hu, fun i j hij =>
    havoid j (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hij⟩)⟩

/-- Continuous cell sampling supplies distinct sites for the already checked
atomic discretization. The inner rounding law is fixed before samples are drawn. -/
theorem sampledCellSites_atomic_discretization (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (B : Fin n → Set (Rd d)) (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (q D : ℝ) (hq : 0 < q) (hD : 0 ≤ D)
    (hdiam : ∀ i j, ∀ y ∈ B i, ∀ z ∈ B j, ‖y - z‖ ≤ D)
    (hmass : ∀ i, (ν i).mass ≤ 1) (m : ℕ)
    (hsum : (∑ i, ((ν i).mass : ℝ)) = (m : ℝ)) :
    ∀ᵐ u ∂uniformCellMarks n,
      (∀ᵐ v ∂randomRoundingLaw n (fun i => ((ν i).mass : ℝ)),
        (occupiedSites (sampledCellSites d n ν u) v).card = m ∧
        weightedAtomicMeasure d n (sampledCellSites d n ν u) v =
          ∑ y ∈ occupiedSites (sampledCellSites d n ν u) v, Measure.dirac y) ∧
      (∀ f : Rd d → ℝ,
        (∫ v, (occupiedSites (sampledCellSites d n ν u) v).sum f
          ∂randomRoundingLaw n (fun i => ((ν i).mass : ℝ))) =
          ∑ i, ((ν i).mass : ℝ) * f (sampledCellSites d n ν u i)) ∧
      (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
        (weightedSignedMeasure d n (sampledCellSites d n ν u)
          (fun i => v i - ((ν i).mass : ℝ)))
        ∂randomRoundingLaw n (fun i => ((ν i).mass : ℝ))) ≤
          D ^ q / q * totalFractionalBudget (fun i => ((ν i).mass : ℝ)) := by
  filter_upwards [sampledCellSites_supported d n ν hν B hsupport,
    sampledCellSites_injective d n ν hν B hsupport hdisjoint] with u hu hinj
  exact atomic_discretization q D hq hD (sampledCellSites d n ν u) hinj
    (fun i j => hdiam i j _ (hu i) _ (hu j)) (fun i => ((ν i).mass : ℝ))
    (fun i => ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.mpr (hmass i)⟩) m hsum

theorem randomRoundingLaw_coordinate_lintegral {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (i : Fin n) :
    (∫⁻ v, ENNReal.ofReal (v i) ∂randomRoundingLaw n w) = ENNReal.ofReal (w i) := by
  have hcard : (fractionalSites w).card ≤ n + 1 :=
    (show (fractionalSites w).card ≤ n from
      (by simpa using (fractionalSites w).card_le_univ)).trans (Nat.le_succ n)
  have hnonneg : 0 ≤ᵐ[randomRoundingLaw n w] (fun v => v i) :=
    (randomRoundingLaw_final n w hw hcard).mono (fun v hv => (hv.1 i).1)
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_randomRoundingLaw n w (fun v => v i)) hnonneg).symm.trans
      (congrArg ENNReal.ofReal (randomRoundingLaw_coordinate_mean n w i))

/-- Atomic rounding preserves the complete measure mean, on every Borel set. -/
theorem randomRoundingLaw_weightedAtomic_mean {d n : ℕ}
    (x : Fin n → Rd d) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (D : Set (Rd d)) :
    (∫⁻ v, weightedAtomicMeasure d n x v D ∂randomRoundingLaw n w) =
      weightedAtomicMeasure d n x w D := by
  simp_rw [weightedAtomicMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_finsetSum (f := fun (i : Fin n) (v : Fin n → ℝ) =>
    ENNReal.ofReal (v i) * Measure.dirac (x i) D) Finset.univ (fun i _ =>
      (ENNReal.measurable_ofReal.comp (measurable_pi_apply i)).mul measurable_const)]
  exact Finset.sum_congr rfl (fun i _ =>
    (lintegral_mul_const (Measure.dirac (x i) D)
      (ENNReal.measurable_ofReal.comp (measurable_pi_apply i))).trans
      (congrArg (fun a => a * Measure.dirac (x i) D)
        (randomRoundingLaw_coordinate_lintegral w hw i)))

/-- Sampling and then rounding preserve the full continuous measure mean. -/
theorem sampledCellSites_rounded_full_mean (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hmass : ∀ i, (ν i).mass ≤ 1)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ u, ∫⁻ v, weightedAtomicMeasure d n (sampledCellSites d n ν u) v D
      ∂randomRoundingLaw n (fun i => ((ν i).mass : ℝ)) ∂uniformCellMarks n) =
      (∑ i, (ν i : Measure (Rd d))) D := by
  simp_rw [randomRoundingLaw_weightedAtomic_mean
    (w := fun i => ((ν i).mass : ℝ))
    (hw := fun i => ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.mpr (hmass i)⟩)]
  exact sampledCellSites_full_mean d n ν D hD

end Riesz.Negative
