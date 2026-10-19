import Riesz.Negative.SphericalTransport
import Riesz.Negative.DiffuseDecomposition
import Riesz.Negative.RandomRepairedInput

/-!
Actual sampling followed by arbitrary measurable partition rounding.
The energy estimate below is produced from diameter/cardinality bounds;
no expected-energy estimate is an input.
-/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Configuration Riesz.Geometry ProbabilityTheory
open scoped ENNReal Classical ProbabilityTheory

namespace Riesz.Negative

abbrev ResidualSamplingMarks (n : ℕ) := Fin n → unitInterval

def residualSamplingWeights (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d)) :
    Fin n → ℝ := fun i => ((ν i).mass : ℝ)

theorem residualSamplingWeights_valid (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hmass : ∀ i, (ν i).mass ≤ 1) :
    ∀ i, 0 ≤ residualSamplingWeights d n ν i ∧ residualSamplingWeights d n ν i ≤ 1 := by
  exact fun i => ⟨NNReal.coe_nonneg _, by exact_mod_cast hmass i⟩

def residualSamplingRoundingKernel (d n k : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d))
    (masks : ResidualSamplingMarks n → RoundingMasks n) (hmasks : Measurable masks) :
    Kernel (ResidualSamplingMarks n) (Fin n → ℝ) :=
  (multiscaleRoundingKernel (n := n) (k + 1)).comap
    (fun u => (masks u, residualSamplingWeights d n ν))
    (hmasks.prodMk measurable_const)

instance residualSamplingRoundingKernel_isMarkov (d n k : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d))
    (masks : ResidualSamplingMarks n → RoundingMasks n) (hmasks : Measurable masks) :
    IsMarkovKernel (residualSamplingRoundingKernel d n k ν masks hmasks) := by
  unfold residualSamplingRoundingKernel
  infer_instance

def residualSamplingRoundingMarks (d n k : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d))
    (masks : ResidualSamplingMarks n → RoundingMasks n) (hmasks : Measurable masks) :
    Measure ((ResidualSamplingMarks n) × (Fin n → ℝ)) :=
  (uniformCellMarks n).compProd (residualSamplingRoundingKernel d n k ν masks hmasks)

instance residualSamplingRoundingMarks_probability (d n k : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d))
    (masks : ResidualSamplingMarks n → RoundingMasks n) (hmasks : Measurable masks) :
    IsProbabilityMeasure (residualSamplingRoundingMarks d n k ν masks hmasks) := by
  unfold residualSamplingRoundingMarks
  infer_instance

def residualSampledMeasure (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d))
    (p : ResidualSamplingMarks n × (Fin n → ℝ)) : Measure (Rd d) :=
  weightedAtomicMeasure d n (sampledCellSites d n ν p.1) p.2

theorem measurable_residualSampledMeasure (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) : Measurable (residualSampledMeasure d n ν) := by
  exact (measurable_weightedAtomicMeasure d n).comp
    (((measurable_sampledCellSites d n ν).comp measurable_fst).prodMk measurable_snd)

instance residualSampledMeasure_finite (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d))
    (p : ResidualSamplingMarks n × (Fin n → ℝ)) :
    IsFiniteMeasure (residualSampledMeasure d n ν p) := by
  unfold residualSampledMeasure
  infer_instance

def residualSampledLaw (d n k : ℕ) (ν : Fin n → FiniteMeasure (Rd d))
    (masks : ResidualSamplingMarks n → RoundingMasks n) (hmasks : Measurable masks) :
    ConfigurationLaw d :=
  (residualSamplingRoundingMarks d n k ν masks hmasks).map (residualSampledMeasure d n ν)

instance residualSampledLaw_probability (d n k : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d))
    (masks : ResidualSamplingMarks n → RoundingMasks n) (hmasks : Measurable masks) :
    IsProbabilityMeasure (residualSampledLaw d n k ν masks hmasks) := by
  exact Measure.isProbabilityMeasure_map (measurable_residualSampledMeasure d n ν).aemeasurable

theorem residualSamplingRoundingMarks_full_mean (d n k : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hmass : ∀ i, (ν i).mass ≤ 1)
    (masks : ResidualSamplingMarks n → RoundingMasks n) (hmasks : Measurable masks)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ p, residualSampledMeasure d n ν p D
      ∂residualSamplingRoundingMarks d n k ν masks hmasks) = cellMeasureSum d n ν D := by
  rw [residualSamplingRoundingMarks, Measure.lintegral_compProd
    (f := fun p : ResidualSamplingMarks n × (Fin n → ℝ) => residualSampledMeasure d n ν p D)
    ((Measure.measurable_coe hD).comp (measurable_residualSampledMeasure d n ν))]
  change (∫⁻ u, ∫⁻ v, weightedAtomicMeasure d n (sampledCellSites d n ν u) v D
    ∂multiscaleRoundingLaw (k + 1) (masks u) (residualSamplingWeights d n ν)
      ∂uniformCellMarks n) = _
  simp_rw [multiscaleRoundingLaw_weightedAtomic_mean (k + 1) _ _ _
    (residualSamplingWeights_valid d n ν hmass) D]
  exact sampledCellSites_full_mean d n ν D hD

theorem residualSampledLaw_full_mean (d n k : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hmass : ∀ i, (ν i).mass ≤ 1)
    (masks : ResidualSamplingMarks n → RoundingMasks n) (hmasks : Measurable masks)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ μ, μ D ∂residualSampledLaw d n k ν masks hmasks) = cellMeasureSum d n ν D := by
  rw [residualSampledLaw, lintegral_map (Measure.measurable_coe hD)
    (measurable_residualSampledMeasure d n ν)]
  exact residualSamplingRoundingMarks_full_mean d n k ν hmass masks hmasks D hD

theorem residualSamplingRoundingMarks_spec (d n k M : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hmass : ∀ i, (ν i).mass ≤ 1)
    (B : Fin n → Set (Rd d)) (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (S : Set (Rd d)) (hS : MeasurableSet S) (hB : ∀ i, B i ⊆ S)
    (hM : ∑ i, ((ν i).mass : ℝ) = M)
    (masks : ResidualSamplingMarks n → RoundingMasks n) (hmasks : Measurable masks)
    (hroot : ∀ᵐ u ∂uniformCellMarks n, ∀ i j, masks u k (i, j) = true) :
    ∀ᵐ p ∂residualSamplingRoundingMarks d n k ν masks hmasks,
      (IsSimpleConfiguration d (residualSampledMeasure d n ν p) ∧
        residualSampledMeasure d n ν p Set.univ = (M : ℝ≥0∞)) ∧
      residualSampledMeasure d n ν p Sᶜ = 0 := by
  apply Measure.ae_compProd_of_ae_ae
    (((measurableSet_simple_fixed_count d M).preimage (measurable_residualSampledMeasure d n ν)).inter
      ((measurableSet_eq_fun (Measure.measurable_coe hS.compl) measurable_const).preimage
        (measurable_residualSampledMeasure d n ν)))
  filter_upwards [sampledCellSites_injective d n ν hν B hsupport hdisjoint,
    sampledCellSites_supported d n ν hν B hsupport, hroot] with u hu hy hr
  filter_upwards [multiscaleRoundingLaw_occupiedSites_spec k (masks u) hr
    (residualSamplingWeights d n ν) (residualSamplingWeights_valid d n ν hmass)
    M hM (sampledCellSites d n ν u) hu] with v hv
  refine ⟨⟨(congrArg (IsSimpleConfiguration d) hv.2).mpr (finsetCounting_simple d _), ?_⟩, ?_⟩
  · simp [residualSampledMeasure, hv.2, Measure.finsetSum_apply, hv.1]
  · exact weightedAtomicMeasure_concentrated d n (sampledCellSites d n ν u) v S
      (fun i => hB i (hy i))

theorem residualSampledLaw_spec (d n k M : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hmass : ∀ i, (ν i).mass ≤ 1)
    (B : Fin n → Set (Rd d)) (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (S : Set (Rd d)) (hS : MeasurableSet S) (hB : ∀ i, B i ⊆ S)
    (hM : ∑ i, ((ν i).mass : ℝ) = M)
    (masks : ResidualSamplingMarks n → RoundingMasks n) (hmasks : Measurable masks)
    (hroot : ∀ᵐ u ∂uniformCellMarks n, ∀ i j, masks u k (i, j) = true) :
    ∀ᵐ μ ∂residualSampledLaw d n k ν masks hmasks,
      (IsSimpleConfiguration d μ ∧ μ Set.univ = (M : ℝ≥0∞)) ∧ μ Sᶜ = 0 := by
  exact (ae_map_iff (measurable_residualSampledMeasure d n ν).aemeasurable
    ((measurableSet_simple_fixed_count d M).inter
      (measurableSet_eq_fun (Measure.measurable_coe hS.compl) measurable_const))).mpr
    (residualSamplingRoundingMarks_spec d n k M ν hν hmass B hsupport hdisjoint S hS hB
      hM masks hmasks hroot)

theorem residualSamplingRoundingMarks_energy_integrable (d n k M : ℕ) (q L : ℝ)
    (hq : 0 < q) (hq2 : q < 2)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hmass : ∀ i, (ν i).mass ≤ 1)
    (B : Fin n → Set (Rd d)) (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (S : Set (Rd d)) (hS : MeasurableSet S) (hB : ∀ i, B i ⊆ S)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L)
    (hM : ∑ i, ((ν i).mass : ℝ) = M)
    (masks : ResidualSamplingMarks n → RoundingMasks n) (hmasks : Measurable masks)
    (hroot : ∀ᵐ u ∂uniformCellMarks n, ∀ i j, masks u k (i, j) = true) :
    Integrable (fun p => Riesz.Analysis.signedDiscrepancyEnergy q
      ((residualSampledMeasure d n ν p).toSignedMeasure - (cellMeasureSum d n ν).toSignedMeasure))
      (residualSamplingRoundingMarks d n k ν masks hmasks) := by
  have hspec := residualSamplingRoundingMarks_spec d n k M ν hν hmass B hsupport
    hdisjoint S hS hB hM masks hmasks hroot
  have htotalmass : cellMeasureSum d n ν Set.univ = (M : ℝ≥0∞) := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by finiteness)).mp
    change (cellMeasureSum d n ν).real Set.univ = (M : ℝ≥0∞).toReal
    simpa only [cellMeasureSum_real_univ, ENNReal.toReal_natCast] using hM
  have hcommon (i : Fin n) : (ν i : Measure (Rd d)) Sᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr (hB i))
      ((FiniteMeasure.null_iff_toMeasure_null _ _).mp (hsupport i))
  have htotalsupport : cellMeasureSum d n ν Sᶜ = 0 := by
    simp only [cellMeasureSum, Measure.finsetSum_apply, hcommon, Finset.sum_const_zero]
  exact finiteDifferenceDiscrepancy_integrable _ d M q L hq hq2 (residualSampledMeasure d n ν)
    (measurable_residualSampledMeasure d n ν) (cellMeasureSum d n ν) htotalmass S hS
    htotalsupport hdiam (hspec.mono (fun p hp => ⟨hp.2, hp.1.2⟩))

theorem residualSamplingRoundingMarks_energy_le (d n k M : ℕ) (q L ℓ : ℝ)
    (hq : 0 < q) (hq2 : q < 2) (hℓ : 0 ≤ ℓ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hν : ∀ i, ν i ≠ 0)
    (hmass : ∀ i, (ν i).mass ≤ 1) (hatom : ∀ i y, ν i {y} = 0)
    (B : Fin n → Set (Rd d)) (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hlocal : ∀ i, ∀ x ∈ B i, ∀ y ∈ B i, ‖x - y‖ ≤ ℓ)
    (S : Set (Rd d)) (hS : IsCompact S) (hB : ∀ i, B i ⊆ S)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L)
    (hM : ∑ i, ((ν i).mass : ℝ) = M)
    {ι : Type*} [DecidableEq ι] [MeasurableSpace ι] [MeasurableEq ι]
    (labels : ResidualSamplingMarks n → ℕ → Fin n → ι) (hlabels : Measurable labels)
    (hroot : ∀ᵐ u ∂uniformCellMarks n, ∀ i j, labels u k i = labels u k j)
    (D : ℕ → ℝ) (hD : ∀ j < k + 1, 0 ≤ D j)
    (C : ℕ → ℕ)
    (hcard : ∀ᵐ u ∂uniformCellMarks n, ∀ j < k,
      (Finset.univ.image (labels u j)).card ≤ C j)
    (hlabeldiam : ∀ᵐ u ∂uniformCellMarks n, ∀ j < k + 1, ∀ i l,
      labels u j i = labels u j l →
        ‖sampledCellSites d n ν u i - sampledCellSites d n ν u l‖ ≤ D j) :
    let masks := fun u => partitionRoundingMasks (labels u)
    let hmasks := (measurable_partitionRoundingMasks (n := n) (ι := ι)).comp hlabels
    (∫ p, Riesz.Analysis.signedDiscrepancyEnergy q
      ((residualSampledMeasure d n ν p).toSignedMeasure - (cellMeasureSum d n ν).toSignedMeasure)
      ∂residualSamplingRoundingMarks d n k ν masks hmasks) ≤
      (8 * ℓ ^ q / q) * M + 2 * (D 0 ^ q / q * M +
        ∑ j ∈ Finset.range k, D (j + 1) ^ q / q * ((C j : ℝ) / 4)) := by
  dsimp only
  let masks := fun u => partitionRoundingMasks (labels u)
  have hmasks : Measurable masks := (measurable_partitionRoundingMasks (n := n) (ι := ι)).comp hlabels
  have hroot' : ∀ᵐ u ∂uniformCellMarks n, ∀ i j, masks u k (i, j) = true :=
    hroot.mono (fun u hu i j => by simp only [masks, partitionRoundingMasks, hu i j, decide_true])
  have htotal := residualSamplingRoundingMarks_energy_integrable d n k M q L hq hq2 ν hν
    hmass B hsupport hdisjoint S hS.measurableSet hB hdiam hM masks hmasks hroot'
  have houter := htotal.integral_compProd
  have hinner := htotal.ae_of_compProd
  have hcommon (i : Fin n) : (ν i : Measure (Rd d)) Sᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr (hB i))
      ((FiniteMeasure.null_iff_toMeasure_null _ _).mp (hsupport i))
  have hsample := sampledCellDiscrepancy_marks_integrable d n q L hq.le ν hν hatom S hcommon hdiam
  let G : ℝ := D 0 ^ q / q * M +
    ∑ j ∈ Finset.range k, D (j + 1) ^ q / q * ((C j : ℝ) / 4)
  have hbudget : totalFractionalBudget (residualSamplingWeights d n ν) ≤ M := by
    rw [← hM]
    exact Finset.sum_le_sum (fun i _ => by
      dsimp [totalFractionalBudget, fractionalBudget, residualSamplingWeights]
      nlinarith [sq_nonneg ((ν i).mass : ℝ)])
  have hround : ∀ᵐ u ∂uniformCellMarks n,
      (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
        (weightedSignedMeasure d n (sampledCellSites d n ν u)
          (fun i => v i - residualSamplingWeights d n ν i))
        ∂multiscaleRoundingLaw (k + 1) (masks u) (residualSamplingWeights d n ν)) ≤ G := by
    filter_upwards [sampledCellSites_injective d n ν hν B hsupport hdisjoint, hcard, hlabeldiam]
      with u hu hc hd
    have hb := partitionRoundingLaw_expected_energy_le k (labels u) q hq D hD
      (sampledCellSites d n ν u) hu hd (residualSamplingWeights d n ν)
      (residualSamplingWeights_valid d n ν hmass)
    refine hb.trans (add_le_add
      (mul_le_mul_of_nonneg_left hbudget (div_nonneg (Real.rpow_nonneg (hD 0 (by omega)) q) hq.le)) ?_)
    exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr (hc j (Finset.mem_range.mp hj))) (by norm_num))
      (div_nonneg (Real.rpow_nonneg (hD (j + 1)
        (Nat.succ_lt_succ (Finset.mem_range.mp hj))) q) hq.le))
  rw [residualSamplingRoundingMarks, Measure.integral_compProd htotal]
  have hbound : (∫ u, ∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
      ((residualSampledMeasure d n ν (u, v)).toSignedMeasure - (cellMeasureSum d n ν).toSignedMeasure)
      ∂residualSamplingRoundingKernel d n k ν masks hmasks u ∂uniformCellMarks n) ≤
      2 * (∫ u, Riesz.Analysis.signedDiscrepancyEnergy q
        (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u)) ∂uniformCellMarks n) + 2 * G := by
    apply le_trans (b := ∫ u, 2 * Riesz.Analysis.signedDiscrepancyEnergy q
      (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u)) + 2 * G ∂uniformCellMarks n)
    · refine integral_mono_ae houter ((hsample.const_mul 2).add (integrable_const _)) ?_
      filter_upwards [hinner, hround,
        sampledCellSites_injective d n ν hν B hsupport hdisjoint,
        sampledCellSites_supported d n ν hν B hsupport] with u hi hr hu hy
      have hri := multiscaleWeightedEnergy_integrable d n (k + 1) (masks u) q
        (sampledCellSites d n ν u) hu (residualSamplingWeights d n ν)
      letI : IsProbabilityMeasure (multiscaleRoundingLaw (k + 1) (masks u)
        (residualSamplingWeights d n ν)) := (multiscaleRoundingLaw_measurable_probability _).2 _ _
      have hp : ∀ᵐ v ∂multiscaleRoundingLaw (k + 1) (masks u) (residualSamplingWeights d n ν),
          Riesz.Analysis.signedDiscrepancyEnergy q
            ((residualSampledMeasure d n ν (u, v)).toSignedMeasure - (cellMeasureSum d n ν).toSignedMeasure) ≤
          2 * Riesz.Analysis.signedDiscrepancyEnergy q
            (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u)) +
          2 * Riesz.Analysis.signedDiscrepancyEnergy q (weightedSignedMeasure d n
            (sampledCellSites d n ν u) (fun i => v i - residualSamplingWeights d n ν i)) := by
        filter_upwards [multiscaleRoundingLaw_preserves (k + 1) (masks u)
          (residualSamplingWeights d n ν) (residualSamplingWeights_valid d n ν hmass)] with v hv
        have hdecomp : (residualSampledMeasure d n ν (u, v)).toSignedMeasure -
            (cellMeasureSum d n ν).toSignedMeasure =
            sampledCellDiscrepancy d n ν (sampledCellSites d n ν u) +
              weightedSignedMeasure d n (sampledCellSites d n ν u)
                (fun i => v i - residualSamplingWeights d n ν i) := by
          rw [← weightedAtomicMeasure_signed_difference d n (sampledCellSites d n ν u) v
            (residualSamplingWeights d n ν) (fun i => (hv.1 i).1) (fun i => NNReal.coe_nonneg _)]
          unfold residualSampledMeasure sampledCellDiscrepancy residualSamplingWeights
          abel
        rw [hdecomp]
        apply Riesz.Analysis.signedDiscrepancyEnergy_add_le q hq hq2 _ _
          (sampledCellDiscrepancy_mass_zero d n ν _) _ S hS
          (sampledCellDiscrepancy_concentrated d n ν hatom _ S (fun i => hB i (hy i)) hcommon)
          (weightedSignedMeasure_concentrated d n _ hu _ S (fun i => hB i (hy i)))
        rw [weightedSignedMeasure_univ, Finset.sum_sub_distrib, hv.2.1, sub_self]
      have hb := integral_mono_ae hi
        ((integrable_const _).add (hri.const_mul 2)) hp
      simp only [Kernel.prodMkLeft_apply, Kernel.comap_apply, residualSamplingRoundingKernel, multiscaleRoundingKernel,
        Kernel.coe_mk, Pi.add_apply, integral_add (integrable_const _) (hri.const_mul 2),
        integral_const_mul, integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
        one_smul] at hb
      exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (by norm_num)))
    · simp only [integral_add (hsample.const_mul 2) (integrable_const _), integral_const_mul,
        integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul, le_refl]
  have hsampbound := sampledCellSites_expected_energy_le_mass d n q L ℓ hq hℓ ν hν hmass
    hatom S hcommon hdiam B hsupport hlocal
  rw [hM] at hsampbound
  exact hbound.trans (by
    convert add_le_add_right (mul_le_mul_of_nonneg_left hsampbound (by norm_num : (0 : ℝ) ≤ 2))
      (2 * G) using 1 <;> ring)

/-! The atlas is selected once, before the residual mask, coarse starting
side and the main-cell chart distortion are chosen. -/

structure ResidualSphericalAtlas (d : ℕ) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_le : rho ≤ 1 / 2
  size : ℕ
  chart : Fin size → Rd d → Sphere d
  continuous : ∀ i, ContinuousOn (chart i) (Metric.ball 0 rho)
  injective : ∀ i, Set.InjOn (chart i) (Metric.ball 0 rho)
  area : ∀ i E, MeasurableSet E → E ⊆ Metric.ball 0 rho →
    sphericalMeasure d (chart i '' E) =
      (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E
  upper : ∀ i, ∀ x ∈ Metric.ball (0 : Rd d) rho, ∀ y ∈ Metric.ball 0 rho,
    chord d (chart i x) (chart i y) ≤ (3 / 2 : ℝ) * ‖x - y‖
  patch : Fin size → Set (Sphere d)
  measurable_patch : ∀ i, MeasurableSet (patch i)
  disjoint_patch : Pairwise (fun i j => Disjoint (patch i) (patch j))
  cover_patch : (⋃ i, patch i) = Set.univ
  subordinate : ∀ i, patch i ⊆ chart i '' Metric.ball 0 rho

theorem exists_residualSphericalAtlas (k : ℕ) : Nonempty (ResidualSphericalAtlas (k + 1)) := by
  obtain ⟨rho, hrho, hsmall, hc, hi, ha, hd⟩ :=
    exists_equalAreaCapPoint_chart k (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  obtain ⟨delta, hdelta, t, hWopen, hWcover, hWinside⟩ :=
    exists_finite_equalAreaCapPoint_open_cover k hrho
  let W : Problem1.Orthogonal (k + 1) → Set (Sphere (k + 1)) :=
    fun U => rotateSphere (k + 1) U⁻¹ ⁻¹'
      Metric.ball (normalPoint (k + 1) 1 0) delta
  let n := Fintype.card ↥t
  let e : ↥t ≃ Fin n := Fintype.equivFin ↥t
  let U : Fin n → Problem1.Orthogonal (k + 1) := fun i => (e.symm i).val
  let C : Fin n → Set (Sphere (k + 1)) := fun i => W (U i)
  let F : Fin n → Rd (k + 1) → Sphere (k + 1) :=
    fun i => rotateSphere (k + 1) (U i) ∘ equalAreaCapPoint k
  have hCopen : ∀ i, IsOpen (C i) := fun i => hWopen (U i)
  have hCcover : (⋃ i, C i) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    obtain ⟨V, hVt, hyV⟩ := Set.mem_iUnion₂.mp
      (show y ∈ ⋃ V ∈ t, W V from hWcover (Set.mem_univ y))
    refine Set.mem_iUnion.mpr ⟨e ⟨V, hVt⟩, ?_⟩
    simpa only [C, U, Equiv.symm_apply_apply] using hyV
  let P : Fin n → Set (Sphere (k + 1)) := disjointed C
  have hPmeas : ∀ i, MeasurableSet (P i) := by
    intro i
    rw [show P i = C i ∩ ⋂ j < i, (C j)ᶜ from disjointed_eq_inter_compl C i]
    exact (hCopen i).measurableSet.inter
      (MeasurableSet.iInter fun j : Fin n => MeasurableSet.iInter fun (_hj : j < i) =>
        (hCopen j).measurableSet.compl)
  refine ⟨⟨rho, hrho, hsmall, n, F, ?_, ?_, ?_, ?_, P, hPmeas,
    disjoint_disjointed C, ?_, ?_⟩⟩
  · exact fun i => (rotateSphere_isometry (k + 1) (U i)).continuous.comp_continuousOn hc
  · exact fun i x hx y hy hxy =>
      hi hx hy ((rotateSphere_isometry (k + 1) (U i)).injective hxy)
  · intro i E hE hsub
    rw [Set.image_comp, sphericalMeasure_rotateSphere_image]
    exact ha E hE hsub
  · intro i x hx y hy
    simpa only [F, Function.comp_apply, rotateSphere_chord, show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
      using (hd x hx y hy).2
  · simpa only [P, iUnion_disjointed] using hCcover
  · exact fun i => (disjointed_subset C i).trans (hWinside (U i))

def residualAtlasMask (d : ℕ) (A : ResidualSphericalAtlas d)
    (S : Set (Sphere d)) (i : Fin A.size) : Set (Rd d) :=
  Metric.ball 0 A.rho ∩ A.chart i ⁻¹' (S ∩ A.patch i)

theorem measurableSet_residualAtlasMask (d : ℕ) (A : ResidualSphericalAtlas d)
    (S : Set (Sphere d)) (hS : MeasurableSet S) (i : Fin A.size) :
    MeasurableSet (residualAtlasMask d A S i) := by
  have heq : residualAtlasMask d A S i = Metric.ball 0 A.rho ∩
      sphericalCellChartExtension d (Metric.ball 0 A.rho) (A.chart i) ⁻¹' (S ∩ A.patch i) := by
    ext x
    by_cases hx : x ∈ Metric.ball (0 : Rd d) A.rho
    · simp only [residualAtlasMask, Set.mem_inter_iff, Set.mem_preimage, hx, true_and,
        sphericalCellChartExtension, Set.piecewise_eq_of_mem _ _ _ hx]
    · simp only [residualAtlasMask, Set.mem_inter_iff, hx, false_and]
  rw [heq]
  exact Metric.isOpen_ball.measurableSet.inter
    ((measurable_sphericalCellChartExtension d _ _ Metric.isOpen_ball.measurableSet
      (A.continuous i)) (hS.inter (A.measurable_patch i)))

theorem residualAtlasMask_image (d : ℕ) (A : ResidualSphericalAtlas d)
    (S : Set (Sphere d)) (i : Fin A.size) :
    A.chart i '' residualAtlasMask d A S i = S ∩ A.patch i := by
  rw [residualAtlasMask, Set.image_inter_preimage]
  exact Set.inter_eq_right.mpr (Set.inter_subset_right.trans (A.subordinate i))

theorem residualAtlasMask_map_volume (d : ℕ) (A : ResidualSphericalAtlas d)
    (S : Set (Sphere d)) (hS : MeasurableSet S) (i : Fin A.size) :
    (volume.restrict (residualAtlasMask d A S i)).map
      (sphericalCellChartExtension d (Metric.ball 0 A.rho) (A.chart i)) =
      ENNReal.ofReal (omega d) • (sphericalMeasure d).restrict (S ∩ A.patch i) := by
  rw [map_volume_sphericalCellChartExtension d _ _ (A.continuous i) (A.injective i)
    (A.area i) _ (measurableSet_residualAtlasMask d A S hS i) Set.inter_subset_left,
    residualAtlasMask_image]

theorem residualAtlasMask_map_volume_sum (d : ℕ) (A : ResidualSphericalAtlas d)
    (S : Set (Sphere d)) (hS : MeasurableSet S) :
    (∑ i, (volume.restrict (residualAtlasMask d A S i)).map
      (sphericalCellChartExtension d (Metric.ball 0 A.rho) (A.chart i))) =
      ENNReal.ofReal (omega d) • (sphericalMeasure d).restrict S := by
  have hcover : (⋃ i, S ∩ A.patch i) = S := by
    rw [← Set.inter_iUnion, A.cover_patch, Set.inter_univ]
  have hsum : (∑ i, (sphericalMeasure d).restrict (S ∩ A.patch i)) =
      (sphericalMeasure d).restrict S := by
    simpa only [Measure.sum_fintype, hcover] using
      (Measure.restrict_iUnion (μ := sphericalMeasure d)
        (fun i j hij => (A.disjoint_patch hij).mono Set.inter_subset_right Set.inter_subset_right)
        (fun i => hS.inter (A.measurable_patch i))).symm
  simp_rw [residualAtlasMask_map_volume d A S hS]
  rw [← Finset.smul_sum, hsum]

def residualParameterShift (d : ℕ) (A : ResidualSphericalAtlas d) (R : ℝ) : Rd d :=
  WithLp.toLp 2 (fun _ => A.rho * R)

def residualParameterPullback (d : ℕ) (A : ResidualSphericalAtlas d) (R : ℝ)
    (p : Rd d) : Rd d := R⁻¹ • (p - residualParameterShift d A R)

theorem continuous_residualParameterPullback (d : ℕ) (A : ResidualSphericalAtlas d) (R : ℝ) :
    Continuous (residualParameterPullback d A R) := by
  exact (continuous_id.sub continuous_const).const_smul R⁻¹

theorem injective_residualParameterPullback (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) : Function.Injective (residualParameterPullback d A R) := by
  intro x y hxy
  have h := congrArg (fun p : Rd d => R • p) hxy
  simp only [residualParameterPullback, smul_smul, mul_inv_cancel₀ hR.ne', one_smul] at h
  exact add_right_cancel (show x + -residualParameterShift d A R =
    y + -residualParameterShift d A R by simpa only [sub_eq_add_neg] using h)

theorem map_volume_residualParameterPullback (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) :
    (volume : Measure (Rd d)).map (residualParameterPullback d A R) =
      ENNReal.ofReal (R ^ d) • volume := by
  have heq : residualParameterPullback d A R =
      (fun x : Rd d => R⁻¹ • x) ∘ (fun x => -residualParameterShift d A R + x) := by
    ext x
    simp only [residualParameterPullback, Function.comp_apply, sub_eq_neg_add]
  rw [heq, ← Measure.map_map (measurable_const_smul _) (measurable_const_add _),
    map_add_left_eq_self]
  simpa only [finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (pow_pos hR d)] using
    Measure.map_addHaar_smul (volume : Measure (Rd d)) (inv_ne_zero hR.ne')

def residualPhysicalParameterMask (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (S : Set (Sphere d)) (i : Fin A.size) : Set (Rd d) :=
  residualParameterPullback d A R ⁻¹' residualAtlasMask d A S i

theorem measurableSet_residualPhysicalParameterMask (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (S : Set (Sphere d)) (hS : MeasurableSet S) (i : Fin A.size) :
    MeasurableSet (residualPhysicalParameterMask d A R S i) := by
  exact (measurableSet_residualAtlasMask d A S hS i).preimage
    (continuous_residualParameterPullback d A R).measurable

theorem map_volume_residualPhysicalParameterMask (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (hS : MeasurableSet S) (i : Fin A.size) :
    (volume.restrict (residualPhysicalParameterMask d A R S i)).map
      (residualParameterPullback d A R) =
      ENNReal.ofReal (R ^ d) • volume.restrict (residualAtlasMask d A S i) := by
  have h := Measure.restrict_map (μ := (volume : Measure (Rd d)))
    (continuous_residualParameterPullback d A R).measurable
    (measurableSet_residualAtlasMask d A S hS i)
  simpa only [map_volume_residualParameterPullback d A R hR,
    Measure.restrict_smul, residualPhysicalParameterMask] using h.symm

def residualPhysicalAtlasMap (d : ℕ) (A : ResidualSphericalAtlas d) (R : ℝ)
    (i : Fin A.size) (p : Rd d) : Rd (d + 1) :=
  R • (sphericalCellChartExtension d (Metric.ball 0 A.rho) (A.chart i)
    (residualParameterPullback d A R p)).val

theorem measurable_residualPhysicalAtlasMap (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (i : Fin A.size) : Measurable (residualPhysicalAtlasMap d A R i) := by
  exact (continuous_subtype_val.measurable.comp
    ((measurable_sphericalCellChartExtension d _ _ Metric.isOpen_ball.measurableSet
      (A.continuous i)).comp (continuous_residualParameterPullback d A R).measurable)).const_smul R

theorem norm_residualPhysicalAtlasMap (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (i : Fin A.size) (p : Rd d) :
    ‖residualPhysicalAtlasMap d A R i p‖ = R := by
  simp only [residualPhysicalAtlasMap, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  rw [(sphericalCellChartExtension d _ _ _).property, mul_one]

theorem residualPhysicalAtlasMap_eq (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (i : Fin A.size) (p : Rd d)
    (hp : residualParameterPullback d A R p ∈ Metric.ball (0 : Rd d) A.rho) :
    residualPhysicalAtlasMap d A R i p = R • (A.chart i (residualParameterPullback d A R p)).val := by
  rw [residualPhysicalAtlasMap, sphericalCellChartExtension, Set.piecewise_eq_of_mem _ _ _ hp]

theorem residualPhysicalAtlasMap_continuousOn (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (i : Fin A.size) :
    ContinuousOn (residualPhysicalAtlasMap d A R i)
      (residualParameterPullback d A R ⁻¹' Metric.ball 0 A.rho) := by
  apply ((continuous_subtype_val.comp_continuousOn
    ((A.continuous i).comp (continuous_residualParameterPullback d A R).continuousOn
      (fun _ hx => hx))).const_smul R).congr
  exact fun p hp => residualPhysicalAtlasMap_eq d A R i p hp

theorem residualPhysicalAtlasMap_injOn (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (i : Fin A.size) :
    Set.InjOn (residualPhysicalAtlasMap d A R i)
      (residualParameterPullback d A R ⁻¹' Metric.ball 0 A.rho) := by
  intro x hx y hy hxy
  rw [residualPhysicalAtlasMap_eq d A R i x hx, residualPhysicalAtlasMap_eq d A R i y hy] at hxy
  have hh := congrArg (fun v : Rd (d + 1) => R⁻¹ • v) hxy
  simp only [smul_smul, inv_mul_cancel₀ hR.ne', one_smul] at hh
  exact injective_residualParameterPullback d A R hR
    (A.injective i hx hy (Subtype.val_injective hh))

theorem residualPhysicalAtlasMap_distance_le (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (i : Fin A.size) (x y : Rd d)
    (hx : residualParameterPullback d A R x ∈ Metric.ball (0 : Rd d) A.rho)
    (hy : residualParameterPullback d A R y ∈ Metric.ball (0 : Rd d) A.rho) :
    ‖residualPhysicalAtlasMap d A R i x - residualPhysicalAtlasMap d A R i y‖ ≤
      (3 / 2 : ℝ) * ‖x - y‖ := by
  rw [residualPhysicalAtlasMap_eq d A R i x hx, residualPhysicalAtlasMap_eq d A R i y hy,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have h := mul_le_mul_of_nonneg_left (A.upper i _ hx _ hy) hR.le
  change R * ‖(A.chart i (residualParameterPullback d A R x)).val -
      (A.chart i (residualParameterPullback d A R y)).val‖ ≤ _ at h
  have hp : ‖residualParameterPullback d A R x - residualParameterPullback d A R y‖ =
      R⁻¹ * ‖x - y‖ := by
    simp only [residualParameterPullback, ← smul_sub, sub_sub_sub_cancel_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  rw [hp] at h
  convert h using 1; field_simp [hR.ne']

theorem residualPhysicalAtlasMap_volume (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (hS : MeasurableSet S) (i : Fin A.size) :
    (volume.restrict (residualPhysicalParameterMask d A R S i)).map
      (residualPhysicalAtlasMap d A R i) =
      (ENNReal.ofReal (R ^ d * omega d) •
        (sphericalMeasure d).restrict (S ∩ A.patch i)).map (fun p : Sphere d => R • p.val) := by
  have hE := measurable_sphericalCellChartExtension d (Metric.ball 0 A.rho) (A.chart i)
    Metric.isOpen_ball.measurableSet (A.continuous i)
  have hV : Measurable (fun p : Sphere d => R • p.val) := continuous_subtype_val.measurable.const_smul R
  change (volume.restrict _).map
    (((fun p : Sphere d => R • p.val) ∘
      (sphericalCellChartExtension d (Metric.ball 0 A.rho) (A.chart i))) ∘
      residualParameterPullback d A R) = _
  rw [← Measure.map_map (hV.comp hE) (continuous_residualParameterPullback d A R).measurable,
    map_volume_residualPhysicalParameterMask d A R hR S hS i,
    Measure.map_smul, ← Measure.map_map hV hE,
    residualAtlasMask_map_volume d A S hS i, Measure.map_smul, smul_smul,
    ← ENNReal.ofReal_mul (pow_nonneg hR.le d)]
  rw [Measure.map_smul]

theorem residualPhysicalAtlasMap_volume_sum (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (hS : MeasurableSet S) :
    (∑ i, (volume.restrict (residualPhysicalParameterMask d A R S i)).map
      (residualPhysicalAtlasMap d A R i)) =
      (ENNReal.ofReal (R ^ d * omega d) • (sphericalMeasure d).restrict S).map
        (fun p : Sphere d => R • p.val) := by
  have hcover : (⋃ i, S ∩ A.patch i) = S := by
    rw [← Set.inter_iUnion, A.cover_patch, Set.inter_univ]
  have hsum : (∑ i, (sphericalMeasure d).restrict (S ∩ A.patch i)) =
      (sphericalMeasure d).restrict S := by
    simpa only [Measure.sum_fintype, hcover] using
      (Measure.restrict_iUnion (μ := sphericalMeasure d)
        (fun i j hij => (A.disjoint_patch hij).mono Set.inter_subset_right Set.inter_subset_right)
        (fun i => hS.inter (A.measurable_patch i))).symm
  simp_rw [residualPhysicalAtlasMap_volume d A R hR S hS]
  rw [← Measure.map_finset_sum' (f := fun p : Sphere d => R • p.val)
    (continuous_subtype_val.measurable.const_smul R).aemeasurable,
    ← Finset.smul_sum, hsum]

def residualParameterCubeSide (d : ℕ) (A : ResidualSphericalAtlas d) (R : ℝ) : ℕ :=
  ⌈2 * A.rho * R⌉₊ + 1

theorem residualPhysicalParameterMask_subset_cube (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (i : Fin A.size) :
    residualPhysicalParameterMask d A R S i ⊆ cube d (residualParameterCubeSide d A R : ℝ) := by
  intro p hp j
  have hy : ‖residualParameterPullback d A R p‖ < A.rho := by
    simpa only [Metric.mem_ball, dist_zero_right] using hp.1
  have hj : |residualParameterPullback d A R p j| < A.rho :=
    lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (residualParameterPullback d A R p) j) hy
  have heq : p j = R * residualParameterPullback d A R p j + A.rho * R := by
    simp only [residualParameterPullback, residualParameterShift, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul]
    field_simp [hR.ne']
    ring
  have hceil := Nat.le_ceil (2 * A.rho * R)
  rcases abs_lt.mp hj with ⟨hjl, hju⟩
  constructor
  · nlinarith
  · simp only [residualParameterCubeSide, Nat.cast_add, Nat.cast_one]
    nlinarith

def residualParameterMeasure (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (i : Fin A.size) : FiniteMeasure (Rd d) := by
  letI := cube_background_isFiniteMeasure d (residualParameterCubeSide d A R)
  exact ⟨volume.restrict (residualPhysicalParameterMask d A R S i),
    isFiniteMeasure_of_le (volume.restrict (cube d (residualParameterCubeSide d A R : ℝ)))
      (Measure.restrict_mono_set volume
        (residualPhysicalParameterMask_subset_cube d A R hR S i))⟩

theorem residualParameterMeasure_le_cube (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (i : Fin A.size) :
    (residualParameterMeasure d A R hR S i : Measure (Rd d)) ≤
      (2 : ℝ≥0∞) • volume.restrict (cube d (residualParameterCubeSide d A R : ℝ)) := by
  apply (Measure.restrict_mono_set volume
    (residualPhysicalParameterMask_subset_cube d A R hR S i)).trans
  intro E
  simp only [Measure.smul_apply, smul_eq_mul]
  exact le_mul_of_one_le_left zero_le (by norm_num)

abbrev ResidualRawFineIndex (d : ℕ) (A : ResidualSphericalAtlas d) (R : ℝ) :=
  Fin A.size × HalfUnitCellIndex d (residualParameterCubeSide d A R)

def residualFineParameterRegion (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (S : Set (Sphere d)) (z : ResidualRawFineIndex d A R) : Set (Rd d) :=
  halfUnitCell d (residualParameterCubeSide d A R) z.2 ∩ residualPhysicalParameterMask d A R S z.1

def residualRawFineMeasure (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (z : ResidualRawFineIndex d A R) :
    FiniteMeasure (Rd (d + 1)) :=
  (halfUnitDiffusePieces d (residualParameterCubeSide d A R)
    (residualParameterMeasure d A R hR S z.1) z.2).map (residualPhysicalAtlasMap d A R z.1)

def residualRawFineRegion (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (S : Set (Sphere d)) (z : ResidualRawFineIndex d A R) : Set (Rd (d + 1)) :=
  residualPhysicalAtlasMap d A R z.1 '' residualFineParameterRegion d A R S z

theorem measurableSet_residualFineParameterRegion (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (S : Set (Sphere d)) (hS : MeasurableSet S) (z : ResidualRawFineIndex d A R) :
    MeasurableSet (residualFineParameterRegion d A R S z) :=
  (halfUnitCell_measurable _ _ _).inter (measurableSet_residualPhysicalParameterMask d A R S hS z.1)

theorem residualFineParameterRegion_subset_domain (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (S : Set (Sphere d)) (z : ResidualRawFineIndex d A R) :
    residualFineParameterRegion d A R S z ⊆
      residualParameterPullback d A R ⁻¹' Metric.ball 0 A.rho := by
  exact fun p hp => hp.2.1

theorem residualRawFineMeasure_eq (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (z : ResidualRawFineIndex d A R) :
    (residualRawFineMeasure d A R hR S z : Measure (Rd (d + 1))) =
      (volume.restrict (residualFineParameterRegion d A R S z)).map
        (residualPhysicalAtlasMap d A R z.1) := by
  simp only [residualRawFineMeasure, FiniteMeasure.toMeasure_map, halfUnitDiffusePieces,
    FiniteMeasure.restrict_measure_eq, residualParameterMeasure, FiniteMeasure.toMeasure_mk,
    Measure.restrict_restrict (halfUnitCell_measurable _ _ _), residualFineParameterRegion]

theorem measurableSet_residualRawFineRegion (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (hS : MeasurableSet S)
    (z : ResidualRawFineIndex d A R) : MeasurableSet (residualRawFineRegion d A R S z) :=
  (measurableSet_residualFineParameterRegion d A R S hS z).image_of_continuousOn_injOn
    ((residualPhysicalAtlasMap_continuousOn d A R z.1).mono
      (residualFineParameterRegion_subset_domain d A R S z))
    ((residualPhysicalAtlasMap_injOn d A R hR z.1).mono
      (residualFineParameterRegion_subset_domain d A R S z))

theorem residualRawFineMeasure_concentrated (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (hS : MeasurableSet S)
    (z : ResidualRawFineIndex d A R) :
    residualRawFineMeasure d A R hR S z (residualRawFineRegion d A R S z)ᶜ = 0 := by
  apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
  rw [residualRawFineMeasure_eq, Measure.map_apply
    (measurable_residualPhysicalAtlasMap d A R z.1)
    (measurableSet_residualRawFineRegion d A R hR S hS z).compl,
    Measure.restrict_apply
      ((measurableSet_residualRawFineRegion d A R hR S hS z).compl.preimage
        (measurable_residualPhysicalAtlasMap d A R z.1))]
  have he : residualPhysicalAtlasMap d A R z.1 ⁻¹' (residualRawFineRegion d A R S z)ᶜ ∩
      residualFineParameterRegion d A R S z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    exact fun x hx => hx.1 (Set.mem_image_of_mem _ hx.2)
  rw [he, measure_empty]

theorem residualRawFineMeasure_mass_le_one (d : ℕ) (hd : 2 ≤ d)
    (A : ResidualSphericalAtlas d) (R : ℝ) (hR : 0 < R) (S : Set (Sphere d))
    (z : ResidualRawFineIndex d A R) : (residualRawFineMeasure d A R hR S z).mass ≤ 1 := by
  exact (FiniteMeasure.mass_map_le _ _).trans
    (halfUnitDiffusePieces_mass_le_one d _ hd (residualParameterMeasure d A R hR S z.1)
      (residualParameterMeasure_le_cube d A R hR S z.1) z.2)

theorem residualRawFineRegion_diameter (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (z : ResidualRawFineIndex d A R)
    (x y : Rd (d + 1)) (hx : x ∈ residualRawFineRegion d A R S z)
    (hy : y ∈ residualRawFineRegion d A R S z) :
    ‖x - y‖ ≤ (3 / 2 : ℝ) * Real.sqrt d := by
  rcases hx with ⟨p, hp, rfl⟩
  rcases hy with ⟨v, hv, rfl⟩
  have h := residualPhysicalAtlasMap_distance_le d A R hR z.1 p v hp.2.1 hv.2.1
  have hb := halfUnitCell_diameter_le d _ z.2 p v hp.1 hv.1
  have h0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  nlinarith

theorem residualRawFineRegion_subset_scaled_mask (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (S : Set (Sphere d)) (z : ResidualRawFineIndex d A R) :
    residualRawFineRegion d A R S z ⊆ (fun p : Sphere d => R • p.val) '' (S ∩ A.patch z.1) := by
  rintro x ⟨p, hp, rfl⟩
  exact ⟨A.chart z.1 (residualParameterPullback d A R p), hp.2.2,
    (residualPhysicalAtlasMap_eq d A R z.1 p hp.2.1).symm⟩

theorem residualRawFineRegions_pairwise_disjoint (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) :
    Pairwise (fun z w : ResidualRawFineIndex d A R =>
      Disjoint (residualRawFineRegion d A R S z) (residualRawFineRegion d A R S w)) := by
  intro z w hzw
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, hpx⟩ ⟨v, hv, hvx⟩
  by_cases htag : z.1 = w.1
  · have hpoint : p = v := residualPhysicalAtlasMap_injOn d A R hR z.1 hp.2.1
      (by simpa only [Set.mem_preimage, htag] using hv.2.1) (by simpa only [htag] using hpx.trans hvx.symm)
    have hcell : z.2 ≠ w.2 := fun h => hzw (Prod.ext htag h)
    exact Set.disjoint_left.mp (halfUnitCells_pairwise_disjoint d _ hcell)
      hp.1 (hpoint.symm ▸ hv.1)
  · have hscale : R • (A.chart z.1 (residualParameterPullback d A R p)).val =
        R • (A.chart w.1 (residualParameterPullback d A R v)).val := by
      rw [← residualPhysicalAtlasMap_eq d A R z.1 p hp.2.1,
        ← residualPhysicalAtlasMap_eq d A R w.1 v hv.2.1]
      exact hpx.trans hvx.symm
    have hpoint := congrArg (fun t : Rd (d + 1) => R⁻¹ • t) hscale
    simp only [smul_smul, inv_mul_cancel₀ hR.ne', one_smul] at hpoint
    exact Set.disjoint_left.mp (A.disjoint_patch htag) hp.2.2.2
      ((Subtype.val_injective hpoint).symm ▸ hv.2.2.2)

theorem residualRawFineMeasure_sum (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (hS : MeasurableSet S) :
    (∑ z : ResidualRawFineIndex d A R, (residualRawFineMeasure d A R hR S z : Measure (Rd (d + 1)))) =
      (ENNReal.ofReal (R ^ d * omega d) • (sphericalMeasure d).restrict S).map
        (fun p : Sphere d => R • p.val) := by
  rw [Fintype.sum_prod_type]
  have heq (i : Fin A.size) :
      (∑ z : HalfUnitCellIndex d (residualParameterCubeSide d A R),
        (residualRawFineMeasure d A R hR S (i, z) : Measure (Rd (d + 1)))) =
      (volume.restrict (residualPhysicalParameterMask d A R S i)).map
        (residualPhysicalAtlasMap d A R i) := by
    simp only [residualRawFineMeasure, FiniteMeasure.toMeasure_map]
    rw [← Measure.map_finset_sum (measurable_residualPhysicalAtlasMap d A R i).aemeasurable,
      halfUnitDiffusePieces_sum]
    change ((volume.restrict (residualPhysicalParameterMask d A R S i)).restrict
      (cube d (residualParameterCubeSide d A R : ℝ))).map _ = _
    rw [Measure.restrict_restrict (measurableSet_cube _ _),
      Set.inter_eq_right.mpr (residualPhysicalParameterMask_subset_cube d A R hR S i)]
  simp_rw [heq]
  exact residualPhysicalAtlasMap_volume_sum d A R hR S hS

def residualPhysicalBackground (d : ℕ) (R : ℝ) (S : Set (Sphere d)) : FiniteMeasure (Rd (d + 1)) :=
  ⟨(ENNReal.ofReal (R ^ d * omega d) • (sphericalMeasure d).restrict S).map
    (fun p : Sphere d => R • p.val), by
    letI : IsFiniteMeasure (ENNReal.ofReal (R ^ d * omega d) • (sphericalMeasure d).restrict S) :=
      ((sphericalMeasure d).restrict S).smul_finite ENNReal.ofReal_ne_top
    exact Measure.isFiniteMeasure_map _ _⟩

theorem residualPhysicalBackground_nullSingletonClass (d : ℕ) (hd : 2 ≤ d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) :
    NullSingletonClass (residualPhysicalBackground d R S : Measure (Rd (d + 1))) := by
  letI := sphericalMeasure_nullSingletonClass d hd
  refine ⟨fun x => ?_⟩
  change ((ENNReal.ofReal (R ^ d * omega d) • (sphericalMeasure d).restrict S).map
    (fun p : Sphere d => R • p.val)) {x} = 0
  rw [Measure.map_apply (f := fun p : Sphere d => R • p.val)
    (continuous_subtype_val.measurable.const_smul R)
    (measurableSet_singleton x), Measure.smul_apply, smul_eq_mul]
  have hsub : ((fun p : Sphere d => R • p.val) ⁻¹' {x}).Subsingleton := by
    intro p hp v hv
    apply Subtype.val_injective
    have h := congrArg (fun y : Rd (d + 1) => R⁻¹ • y)
      ((Set.mem_singleton_iff.mp hp).trans (Set.mem_singleton_iff.mp hv).symm)
    simpa only [smul_smul, inv_mul_cancel₀ hR.ne', one_smul] using h
  rw [hsub.measure_zero ((sphericalMeasure d).restrict S), mul_zero]

theorem residualRawFineMeasure_le_background (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (hS : MeasurableSet S)
    (z : ResidualRawFineIndex d A R) :
    (residualRawFineMeasure d A R hR S z : Measure (Rd (d + 1))) ≤ residualPhysicalBackground d R S := by
  change (residualRawFineMeasure d A R hR S z : Measure (Rd (d + 1))) ≤
    (ENNReal.ofReal (R ^ d * omega d) • (sphericalMeasure d).restrict S).map
      (fun p : Sphere d => R • p.val)
  rw [← residualRawFineMeasure_sum d A R hR S hS]
  exact Finset.single_le_sum (f := fun i : ResidualRawFineIndex d A R =>
    (residualRawFineMeasure d A R hR S i : Measure (Rd (d + 1))))
    (fun _ _ => bot_le) (Finset.mem_univ z)

theorem residualRawFineMeasure_nullSingleton (d : ℕ) (hd : 2 ≤ d)
    (A : ResidualSphericalAtlas d) (R : ℝ) (hR : 0 < R) (S : Set (Sphere d))
    (hS : MeasurableSet S) (z : ResidualRawFineIndex d A R) (x : Rd (d + 1)) :
    residualRawFineMeasure d A R hR S z {x} = 0 := by
  letI := residualPhysicalBackground_nullSingletonClass d hd R hR S
  apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
  exact le_antisymm (by simpa only [measure_singleton] using
    (residualRawFineMeasure_le_background d A R hR S hS z) {x}) zero_le

abbrev ResidualFineIndex (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) :=
  {z : ResidualRawFineIndex d A R // residualRawFineMeasure d A R hR S z ≠ 0}

abbrev residualFineCount (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) :=
  Fintype.card (ResidualFineIndex d A R hR S)

def residualFineEquiv (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) :
    Fin (residualFineCount d A R hR S) ≃ ResidualFineIndex d A R hR S :=
  (Fintype.equivFin _).symm

def residualFineMeasures (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d))
    (i : Fin (residualFineCount d A R hR S)) : FiniteMeasure (Rd (d + 1)) :=
  residualRawFineMeasure d A R hR S (residualFineEquiv d A R hR S i).val

def residualFineRegions (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d))
    (i : Fin (residualFineCount d A R hR S)) : Set (Rd (d + 1)) :=
  residualRawFineRegion d A R S (residualFineEquiv d A R hR S i).val

def residualFineTag (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d))
    (i : Fin (residualFineCount d A R hR S)) : Fin A.size :=
  (residualFineEquiv d A R hR S i).val.1

theorem residualFineMeasures_sum (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (hS : MeasurableSet S) :
    cellMeasureSum (d + 1) (residualFineCount d A R hR S) (residualFineMeasures d A R hR S) =
      (residualPhysicalBackground d R S : Measure (Rd (d + 1))) := by
  unfold cellMeasureSum residualFineMeasures
  rw [(residualFineEquiv d A R hR S).sum_comp
    (fun z => (residualRawFineMeasure d A R hR S z.val : Measure (Rd (d + 1))))]
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun z : ResidualRawFineIndex d A R => residualRawFineMeasure d A R hR S z ≠ 0)
    (fun z => (residualRawFineMeasure d A R hR S z : Measure (Rd (d + 1))))
  have hz : (∑ z : {z : ResidualRawFineIndex d A R //
      ¬residualRawFineMeasure d A R hR S z ≠ 0},
      (residualRawFineMeasure d A R hR S z.val : Measure (Rd (d + 1)))) = 0 := by
    exact Finset.sum_eq_zero (fun z _ => by
      have hz : residualRawFineMeasure d A R hR S z.val = 0 := not_ne_iff.mp z.property
      simp only [hz, FiniteMeasure.toMeasure_zero])
  rw [hz, add_zero] at hs
  rw [hs]
  exact residualRawFineMeasure_sum d A R hR S hS

theorem residualFineMeasures_sampling_inputs (d : ℕ) (hd : 2 ≤ d)
    (A : ResidualSphericalAtlas d) (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (hS : MeasurableSet S) :
    let _n := residualFineCount d A R hR S
    let ν := residualFineMeasures d A R hR S
    let B := residualFineRegions d A R hR S
    (∀ i, ν i ≠ 0) ∧ (∀ i, (ν i).mass ≤ 1) ∧ (∀ i y, ν i {y} = 0) ∧
      (∀ i, ν i (B i)ᶜ = 0) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i, B i ⊆ Metric.closedBall 0 R) ∧
      (∀ i, B i ⊆ (fun p : Sphere d => R • p.val) '' S) ∧
      (∀ i, ∀ x ∈ B i, ∀ y ∈ B i, ‖x - y‖ ≤ (3 / 2 : ℝ) * Real.sqrt d) := by
  refine ⟨fun i => (residualFineEquiv d A R hR S i).property,
    fun i => residualRawFineMeasure_mass_le_one d hd A R hR S _,
    fun i y => residualRawFineMeasure_nullSingleton d hd A R hR S hS _ y,
    fun i => residualRawFineMeasure_concentrated d A R hR S hS _, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact residualRawFineRegions_pairwise_disjoint d A R hR S (fun h =>
      hij ((residualFineEquiv d A R hR S).injective (Subtype.ext h)))
  · rintro i x ⟨p, hp, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (norm_residualPhysicalAtlasMap d A R hR _ p).le
  · intro i
    exact (residualRawFineRegion_subset_scaled_mask d A R S _).trans
      (Set.image_mono Set.inter_subset_left)
  · exact fun i x hx y hy => residualRawFineRegion_diameter d A R hR S _ x y hx hy

theorem residualPhysicalAtlasEmbedding (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (i : Fin A.size) :
    MeasurableEmbedding ((residualParameterPullback d A R ⁻¹' Metric.ball 0 A.rho).restrict
      (residualPhysicalAtlasMap d A R i)) :=
  ContinuousOn.measurableEmbedding
    (Metric.isOpen_ball.measurableSet.preimage (continuous_residualParameterPullback d A R).measurable)
    (residualPhysicalAtlasMap_continuousOn d A R i) (residualPhysicalAtlasMap_injOn d A R hR i)

private theorem residualParameterShift_mem_domain (d : ℕ) (A : ResidualSphericalAtlas d) (R : ℝ) :
    residualParameterPullback d A R (residualParameterShift d A R) ∈ Metric.ball (0 : Rd d) A.rho := by
  simpa only [residualParameterPullback, sub_self, smul_zero, Metric.mem_ball, dist_self]
    using A.rho_pos

def residualPhysicalAtlasInverse (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (i : Fin A.size) : Rd (d + 1) → Rd d := by
  let B := residualParameterPullback d A R ⁻¹' Metric.ball (0 : Rd d) A.rho
  letI : Nonempty B := ⟨⟨residualParameterShift d A R, residualParameterShift_mem_domain d A R⟩⟩
  exact fun x => ((residualPhysicalAtlasEmbedding d A R hR i).invFun x).val

theorem measurable_residualPhysicalAtlasInverse (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (i : Fin A.size) : Measurable (residualPhysicalAtlasInverse d A R hR i) := by
  letI : Nonempty (residualParameterPullback d A R ⁻¹' Metric.ball (0 : Rd d) A.rho) :=
    ⟨⟨residualParameterShift d A R, residualParameterShift_mem_domain d A R⟩⟩
  unfold residualPhysicalAtlasInverse
  exact measurable_subtype_coe.comp (residualPhysicalAtlasEmbedding d A R hR i).measurable_invFun

theorem residualPhysicalAtlasInverse_left (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (i : Fin A.size) (p : Rd d)
    (hp : residualParameterPullback d A R p ∈ Metric.ball (0 : Rd d) A.rho) :
    residualPhysicalAtlasInverse d A R hR i (residualPhysicalAtlasMap d A R i p) = p := by
  letI : Nonempty (residualParameterPullback d A R ⁻¹' Metric.ball (0 : Rd d) A.rho) :=
    ⟨⟨residualParameterShift d A R, residualParameterShift_mem_domain d A R⟩⟩
  unfold residualPhysicalAtlasInverse
  exact congrArg Subtype.val ((residualPhysicalAtlasEmbedding d A R hR i).leftInverse_invFun ⟨p, hp⟩)

theorem residualParameterDomain_subset_cube (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (p : Rd d)
    (hp : residualParameterPullback d A R p ∈ Metric.ball (0 : Rd d) A.rho) :
    p ∈ cube d (2 * A.rho * R) := by
  intro j
  have hy : ‖residualParameterPullback d A R p‖ < A.rho := by
    simpa only [Metric.mem_ball, dist_zero_right] using hp
  have hj : |residualParameterPullback d A R p j| < A.rho :=
    lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (residualParameterPullback d A R p) j) hy
  have heq : p j = R * residualParameterPullback d A R p j + A.rho * R := by
    simp only [residualParameterPullback, residualParameterShift, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul]
    field_simp [hR.ne']
    ring
  rcases abs_lt.mp hj with ⟨hjl, hju⟩
  constructor <;> nlinarith

private instance residualCoarseLabel_singletons (d t : ℕ) :
    MeasurableSingletonClass (Unit ⊕ (Fin t × (Fin d → ℕ))) where
  measurableSet_singleton a := match a with
    | Sum.inl u => by simpa only [Set.image_singleton] using
        (measurableSet_singleton u).inl_image (β := Fin t × (Fin d → ℕ))
    | Sum.inr v => by simpa only [Set.image_singleton] using
        (measurableSet_singleton v).inr_image (α := Unit)

def residualCoarseLabels (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (k : ℕ) (r : ℝ)
    (u : ResidualSamplingMarks (residualFineCount d A R hR S)) :
    ℕ → Fin (residualFineCount d A R hR S) → Unit ⊕ (Fin A.size × (Fin d → ℕ)) :=
  fun j i => if j < k then Sum.inr (residualFineTag d A R hR S i,
    cubeCellLabel d ((2 : ℝ) ^ j * r)
      (residualPhysicalAtlasInverse d A R hR (residualFineTag d A R hR S i)
        (sampledCellSites (d + 1) _ (residualFineMeasures d A R hR S) u i))) else Sum.inl ()

theorem measurable_residualCoarseLabels (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (k : ℕ) (r : ℝ) :
    Measurable (residualCoarseLabels d A R hR S k r) := by
  refine measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun i => ?_))
  by_cases hj : j < k
  · simp only [residualCoarseLabels, if_pos hj]
    exact measurable_inr.comp (measurable_const.prodMk ((measurable_cubeCellLabel d).comp
      (measurable_const.prodMk ((measurable_residualPhysicalAtlasInverse d A R hR _).comp
        ((measurable_pi_apply i).comp (measurable_sampledCellSites (d + 1) _ _))))))
  · simp only [residualCoarseLabels, if_neg hj]
    exact measurable_const

theorem residualCoarseLabels_root (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (k : ℕ) (r : ℝ)
    (u : ResidualSamplingMarks (residualFineCount d A R hR S)) :
    ∀ i j, residualCoarseLabels d A R hR S k r u k i =
      residualCoarseLabels d A R hR S k r u k j := by
  intro i j
  simp only [residualCoarseLabels, lt_self_iff_false, if_false]

theorem tagged_cellLabel_image_card_le {n d K t : ℕ}
    (tag : Fin n → Fin t) (label : Fin n → Fin d → ℕ)
    (hlabel : ∀ i j, label i j < K) :
    (Finset.univ.image (fun i => (Sum.inr (tag i, label i) : Unit ⊕ (Fin t × (Fin d → ℕ))))).card ≤ t * K ^ d := by
  let boundedLabel : Fin n → Fin t × (Fin d → Fin K) :=
    fun i => (tag i, fun j => ⟨label i j, hlabel i j⟩)
  calc
    _ = ((Finset.univ.image boundedLabel).image
        (fun z : Fin t × (Fin d → Fin K) => (Sum.inr (z.1, fun j => (z.2 j : ℕ)) : Unit ⊕ (Fin t × (Fin d → ℕ))))).card :=
      congrArg Finset.card Finset.image_image.symm
    _ ≤ (Finset.univ.image boundedLabel).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin t × (Fin d → Fin K))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = t * K ^ d := by simp

theorem residualCoarseLabels_card (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (hS : MeasurableSet S)
    (k : ℕ) (r : ℝ) (hr : 0 < r) (hscale : 2 * A.rho * R ≤ (2 : ℝ) ^ k * r) :
    ∀ᵐ u ∂uniformCellMarks (residualFineCount d A R hR S), ∀ j < k,
      (Finset.univ.image (residualCoarseLabels d A R hR S k r u j)).card ≤
        A.size * (2 ^ (k - j)) ^ d := by
  filter_upwards [sampledCellSites_supported (d + 1) _ (residualFineMeasures d A R hR S)
    (fun i => (residualFineEquiv d A R hR S i).property) (residualFineRegions d A R hR S)
    (fun i => residualRawFineMeasure_concentrated d A R hR S hS _)] with u hu
  intro j hj
  rw [show residualCoarseLabels d A R hR S k r u j =
      (fun i => Sum.inr (residualFineTag d A R hR S i,
        cubeCellLabel d ((2 : ℝ) ^ j * r)
          (residualPhysicalAtlasInverse d A R hR (residualFineTag d A R hR S i)
            (sampledCellSites (d + 1) _ (residualFineMeasures d A R hR S) u i))))
      from funext (fun i => if_pos hj)]
  apply tagged_cellLabel_image_card_le
  intro i a
  rcases hu i with ⟨p, hp, hpx⟩
  dsimp only [residualFineTag]
  rw [← hpx, residualPhysicalAtlasInverse_left d A R hR _ p hp.2.1]
  have hside : (2 : ℝ) ^ (k - j) * ((2 : ℝ) ^ j * r) = (2 : ℝ) ^ k * r := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hj)]
  apply cubeCellLabel_lt d (2 ^ (k - j)) _ (by positivity) p
  simpa only [Nat.cast_pow, Nat.cast_ofNat, hside] using
    cube_subset_cube d _ _ hscale (residualParameterDomain_subset_cube d A R hR p hp.2.1)

def residualCoarseDiameterFactor (d : ℕ) (A : ResidualSphericalAtlas d) : ℝ :=
  max ((3 / 2 : ℝ) * Real.sqrt d) A.rho⁻¹

theorem residualCoarseDiameterFactor_nonneg (d : ℕ) (A : ResidualSphericalAtlas d) :
    0 ≤ residualCoarseDiameterFactor d A :=
  (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)).trans (le_max_left _ _)

theorem residualCoarseLabels_diameter (d : ℕ) (A : ResidualSphericalAtlas d)
    (R : ℝ) (hR : 0 < R) (S : Set (Sphere d)) (hS : MeasurableSet S)
    (k : ℕ) (r : ℝ) (hr : 0 < r) (hscale : 2 * A.rho * R ≤ (2 : ℝ) ^ k * r) :
    ∀ᵐ u ∂uniformCellMarks (residualFineCount d A R hR S), ∀ j < k + 1, ∀ i l,
      residualCoarseLabels d A R hR S k r u j i = residualCoarseLabels d A R hR S k r u j l →
      ‖sampledCellSites (d + 1) _ (residualFineMeasures d A R hR S) u i -
        sampledCellSites (d + 1) _ (residualFineMeasures d A R hR S) u l‖ ≤
      residualCoarseDiameterFactor d A * ((2 : ℝ) ^ j * r) := by
  filter_upwards [sampledCellSites_supported (d + 1) _ (residualFineMeasures d A R hR S)
    (fun i => (residualFineEquiv d A R hR S i).property) (residualFineRegions d A R hR S)
    (fun i => residualRawFineMeasure_concentrated d A R hR S hS _)] with u hu
  intro j hj i l he
  rcases hu i with ⟨p, hp, hpx⟩
  rcases hu l with ⟨v, hv, hvx⟩
  by_cases hjk : j < k
  · simp only [residualCoarseLabels, if_pos hjk, Sum.inr.injEq, Prod.mk.injEq] at he
    have htag := he.1
    have hc := he.2
    dsimp only [residualFineTag] at hc htag
    rw [← hpx, residualPhysicalAtlasInverse_left d A R hR _ p hp.2.1,
      ← hvx, residualPhysicalAtlasInverse_left d A R hR _ v hv.2.1] at hc
    have hbound := cubeCellLabel_dist_le d _ (by positivity) p v
      (fun a => (residualParameterDomain_subset_cube d A R hR p hp.2.1 a).1)
      (fun a => (residualParameterDomain_subset_cube d A R hR v hv.2.1 a).1) hc
    rw [← hpx, ← hvx]
    rw [← htag]
    have hb := residualPhysicalAtlasMap_distance_le d A R hR
      (residualFineTag d A R hR S i) p v hp.2.1 hv.2.1
    exact hb.trans ((mul_le_mul_of_nonneg_left hbound (by norm_num)).trans
      (by
        simpa only [residualCoarseDiameterFactor, mul_assoc] using
          mul_le_mul_of_nonneg_right (le_max_left ((3 / 2 : ℝ) * Real.sqrt d) A.rho⁻¹)
            (by positivity : 0 ≤ (2 : ℝ) ^ j * r)))
  · have hjk' : j = k := by omega
    subst j
    rw [← hpx, ← hvx]
    have hb : ‖residualPhysicalAtlasMap d A R (residualFineEquiv d A R hR S i).val.1 p -
        residualPhysicalAtlasMap d A R (residualFineEquiv d A R hR S l).val.1 v‖ ≤ 2 * R :=
      (norm_sub_le _ _).trans (by rw [norm_residualPhysicalAtlasMap d A R hR,
        norm_residualPhysicalAtlasMap d A R hR]; linarith)
    have hh : 2 * R ≤ residualCoarseDiameterFactor d A * ((2 : ℝ) ^ k * r) := by
      calc
        2 * R = A.rho⁻¹ * (2 * A.rho * R) := by field_simp [A.rho_pos.ne']
        _ ≤ A.rho⁻¹ * ((2 : ℝ) ^ k * r) := mul_le_mul_of_nonneg_left hscale (inv_nonneg.mpr A.rho_pos.le)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    exact hb.trans hh

/-! Coarse depth and scalar summation. -/

theorem exists_residualCoarseDepth (d : ℕ) (A : ResidualSphericalAtlas d)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ∃ k : ℕ, 2 * A.rho * R ≤ (2 : ℝ) ^ k * r ∧ (2 : ℝ) ^ k * r ≤ 2 * R := by
  by_cases hs : 2 * A.rho * R ≤ r
  · refine ⟨0, by simpa only [pow_zero, one_mul] using hs, ?_⟩
    simpa only [pow_zero, one_mul] using hrR.trans (by linarith)
  · have hx : 1 ≤ 2 * A.rho * R / r :=
      (le_div_iff₀ hr).2 (by linarith)
    obtain ⟨j, hlo, hhi⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
    have hlo' : (2 : ℝ) ^ j * r ≤ 2 * A.rho * R := (le_div_iff₀ hr).mp hlo
    have hhi' : 2 * A.rho * R < (2 : ℝ) ^ (j + 1) * r := (div_lt_iff₀ hr).mp hhi
    refine ⟨j + 1, hhi'.le, ?_⟩
    rw [pow_succ]
    have hR : 0 ≤ R := hr.le.trans hrR
    have hρ := mul_le_mul_of_nonneg_right A.rho_le hR
    nlinarith

def residualGeometricCoefficient (d t : ℕ) (H q : ℝ) : ℝ :=
  (t : ℝ) * H ^ q / q * ((2 : ℝ) ^ q / 4) /
    (1 - (2 : ℝ) ^ q / (2 : ℝ) ^ d)

theorem residualGeometricCoefficient_nonneg (d t : ℕ) (H q : ℝ)
    (hH : 0 ≤ H) (hq : 0 < q) (hqd : q < (d : ℝ)) :
    0 ≤ residualGeometricCoefficient d t H q := by
  have hθ : (2 : ℝ) ^ q / (2 : ℝ) ^ d < 1 :=
    (div_lt_one (by positivity : 0 < (2 : ℝ) ^ d)).2
      (by simpa only [Real.rpow_natCast] using
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) hqd)
  unfold residualGeometricCoefficient
  positivity

private theorem residualScaleCost_eq (d k j t : ℕ) (hj : j ≤ k) (H r q : ℝ)
    (hH : 0 ≤ H) (hr : 0 ≤ r) :
    (H * ((2 : ℝ) ^ (j + 1) * r)) ^ q / q *
        (((t * (2 ^ (k - j)) ^ d : ℕ) : ℝ) / 4) =
      ((t : ℝ) * (H * r) ^ q / q *
        ((2 : ℝ) ^ q * ((2 : ℝ) ^ k) ^ d / 4)) *
          ((2 : ℝ) ^ q / (2 : ℝ) ^ d) ^ j := by
  have hscale : H * ((2 : ℝ) ^ (j + 1) * r) = (H * r) * (2 : ℝ) ^ (j + 1) := by ring
  rw [hscale, Real.mul_rpow (mul_nonneg hH hr) (by positivity),
    Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
  have hpower : ((2 : ℝ) ^ (j + 1)) ^ q = ((2 : ℝ) ^ q) ^ (j + 1) := by
    rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)) (j + 1) q,
      mul_comm ((j + 1 : ℕ) : ℝ) q,
      Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ)) q (j + 1)]
  rw [hpower, pow_succ, pow_sub₀ (2 : ℝ) (by norm_num) hj, mul_pow, inv_pow]
  have hflip : ((2 : ℝ) ^ j) ^ d = ((2 : ℝ) ^ d) ^ j := by
    rw [← pow_mul, Nat.mul_comm j d, pow_mul]
  rw [hflip, div_pow]
  ring

theorem residualScaleSum_le (d k t : ℕ) (H r q : ℝ) (hH : 0 ≤ H)
    (hr : 0 < r) (hq : 0 < q) (hqd : q < (d : ℝ)) :
    (∑ j ∈ Finset.range k, (H * ((2 : ℝ) ^ (j + 1) * r)) ^ q / q *
      (((t * (2 ^ (k - j)) ^ d : ℕ) : ℝ) / 4)) ≤
        residualGeometricCoefficient d t H q *
          (((2 : ℝ) ^ k * r) ^ d * r ^ (q - (d : ℝ))) := by
  have hθ : 0 ≤ (2 : ℝ) ^ q / (2 : ℝ) ^ d := by positivity
  have hθ_one : (2 : ℝ) ^ q / (2 : ℝ) ^ d < 1 :=
    (div_lt_one (by positivity : 0 < (2 : ℝ) ^ d)).2
      (by simpa only [Real.rpow_natCast] using
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) hqd)
  have hsum :
      (∑ j ∈ Finset.range k, (H * ((2 : ℝ) ^ (j + 1) * r)) ^ q / q *
        (((t * (2 ^ (k - j)) ^ d : ℕ) : ℝ) / 4)) =
      ((t : ℝ) * (H * r) ^ q / q *
        ((2 : ℝ) ^ q * ((2 : ℝ) ^ k) ^ d / 4)) *
        ∑ j ∈ Finset.range k, ((2 : ℝ) ^ q / (2 : ℝ) ^ d) ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j hj =>
      residualScaleCost_eq d k j t (Nat.le_of_lt (Finset.mem_range.mp hj)) H r q hH hr.le)
  have hb := mul_le_mul_of_nonneg_left
    (finite_geometric_sum_le _ hθ hθ_one k)
    (by positivity : 0 ≤ (t : ℝ) * (H * r) ^ q / q *
      ((2 : ℝ) ^ q * ((2 : ℝ) ^ k) ^ d / 4))
  have hvolume : ((2 : ℝ) ^ k * r) ^ d * r ^ (q - (d : ℝ)) =
      ((2 : ℝ) ^ k) ^ d * r ^ q := by
    rw [mul_pow, Real.rpow_sub hr, Real.rpow_natCast]
    field_simp [(pow_pos hr d).ne']
  rw [hsum]
  apply hb.trans_eq
  rw [hvolume, Real.mul_rpow hH hr.le]
  unfold residualGeometricCoefficient
  ring

def residualSphericalMassCoefficient (d : ℕ) (A : ResidualSphericalAtlas d) (q : ℝ) : ℝ :=
  8 * ((3 / 2 : ℝ) * Real.sqrt d) ^ q / q +
    2 * residualCoarseDiameterFactor d A ^ q / q

def residualSphericalBulkCoefficient (d : ℕ) (A : ResidualSphericalAtlas d) (q : ℝ) : ℝ :=
  2 * residualGeometricCoefficient d A.size (residualCoarseDiameterFactor d A) q * (2 : ℝ) ^ d

def residualSphericalFillingConstant (d : ℕ) (A : ResidualSphericalAtlas d) (q : ℝ) : ℝ :=
  residualSphericalMassCoefficient d A q + residualSphericalBulkCoefficient d A q + 1

theorem residualSphericalFillingConstant_pos (d : ℕ) (A : ResidualSphericalAtlas d)
    (q : ℝ) (hq : 0 < q) (hqd : q < (d : ℝ)) :
    0 < residualSphericalFillingConstant d A q := by
  have hH := residualCoarseDiameterFactor_nonneg d A
  have hG := residualGeometricCoefficient_nonneg d A.size _ q hH hq hqd
  have hmass : 0 ≤ residualSphericalMassCoefficient d A q := by
    unfold residualSphericalMassCoefficient
    positivity
  have hbulk : 0 ≤ residualSphericalBulkCoefficient d A q := by
    unfold residualSphericalBulkCoefficient
    positivity
  unfold residualSphericalFillingConstant
  linarith

theorem residualSphericalBudget_le (d k M : ℕ) (A : ResidualSphericalAtlas d)
    (q r R : ℝ) (hq : 0 < q) (hqd : q < (d : ℝ)) (hr : 1 ≤ r)
    (hupper : (2 : ℝ) ^ k * r ≤ 2 * R) :
    (8 * ((3 / 2 : ℝ) * Real.sqrt d) ^ q / q) * M +
      2 * ((residualCoarseDiameterFactor d A * r) ^ q / q * M +
        ∑ j ∈ Finset.range k,
          (residualCoarseDiameterFactor d A * ((2 : ℝ) ^ (j + 1) * r)) ^ q / q *
            (((A.size * (2 ^ (k - j)) ^ d : ℕ) : ℝ) / 4)) ≤
      residualSphericalFillingConstant d A q *
        (r ^ q * M + R ^ d * r ^ (q - (d : ℝ))) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hR : 0 ≤ R := by
    have hscale : 0 ≤ (2 : ℝ) ^ k * r := by positivity
    linarith
  have hH := residualCoarseDiameterFactor_nonneg d A
  have hG := residualGeometricCoefficient_nonneg d A.size _ q hH hq hqd
  have hsum := residualScaleSum_le d k A.size _ r q hH hrpos hq hqd
  have hvolume : ((2 : ℝ) ^ k * r) ^ d * r ^ (q - (d : ℝ)) ≤
      (2 : ℝ) ^ d * (R ^ d * r ^ (q - (d : ℝ))) := by
    rw [← mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_right (by gcongr) (Real.rpow_nonneg hrpos.le _)
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_left hvolume hG)
  have hsmall : 1 ≤ r ^ q := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hr hq.le
  have hsample : (8 * ((3 / 2 : ℝ) * Real.sqrt d) ^ q / q) * M ≤
      (8 * ((3 / 2 : ℝ) * Real.sqrt d) ^ q / q) * (r ^ q * M) :=
    mul_le_mul_of_nonneg_left
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg M)) (by positivity)
  have hmass : 0 ≤ residualSphericalMassCoefficient d A q := by
    unfold residualSphericalMassCoefficient
    positivity
  have hbulk : 0 ≤ residualSphericalBulkCoefficient d A q := by
    unfold residualSphericalBulkCoefficient
    positivity
  have hcell : 0 ≤ r ^ q * (M : ℝ) := by positivity
  have hvol : 0 ≤ R ^ d * r ^ (q - (d : ℝ)) := by positivity
  rw [Real.mul_rpow hH hrpos.le]
  calc
    _ ≤ (8 * ((3 / 2 : ℝ) * Real.sqrt d) ^ q / q) * (r ^ q * M) +
        2 * (residualCoarseDiameterFactor d A ^ q * r ^ q / q * M +
          residualGeometricCoefficient d A.size (residualCoarseDiameterFactor d A) q *
            ((2 : ℝ) ^ d * (R ^ d * r ^ (q - (d : ℝ))))) := by
      linarith only [hsample, hsum']
    _ = residualSphericalMassCoefficient d A q * (r ^ q * M) +
        residualSphericalBulkCoefficient d A q * (R ^ d * r ^ (q - (d : ℝ))) := by
      unfold residualSphericalMassCoefficient residualSphericalBulkCoefficient
      ring
    _ ≤ _ := by
      unfold residualSphericalFillingConstant
      nlinarith only [hcell, hvol, mul_nonneg hmass hvol, mul_nonneg hbulk hcell]

/-- An actual random configuration on a finite common mark space. The residual
mask can be any Borel set with integer physical area. The atlas is fixed before
the coarse scale, radius, and mask; no boundary regularity is assumed. -/
theorem exists_residualSphericalFilling_marks (d : ℕ) (hd : 2 ≤ d)
    (A : ResidualSphericalAtlas d) (q r R : ℝ) (hq : 0 < q) (hq2 : q < 2)
    (hr : 1 ≤ r) (hrR : r ≤ R) (hR : 0 < R)
    (S : Set (Sphere d)) (hS : MeasurableSet S) (M : ℕ)
    (hM : (residualPhysicalBackground d R S : Measure (Rd (d + 1))) Set.univ = M) :
    ∃ k : ℕ,
      let n := residualFineCount d A R hR S
      let ν := residualFineMeasures d A R hR S
      let labels := residualCoarseLabels d A R hR S k r
      let masks := fun u => partitionRoundingMasks (labels u)
      let hmasks := (measurable_partitionRoundingMasks (n := n)).comp
        (measurable_residualCoarseLabels d A R hR S k r)
      let P := residualSamplingRoundingMarks (d + 1) n k ν masks hmasks
      let F := residualSampledMeasure (d + 1) n ν
      IsProbabilityMeasure P ∧ Measurable F ∧
      (∀ᵐ p ∂P, (IsSimpleConfiguration (d + 1) (F p) ∧ F p Set.univ = (M : ℝ≥0∞)) ∧
        F p ((fun x : Sphere d => R • x.val) '' S)ᶜ = 0) ∧
      (∀ D : Set (Rd (d + 1)), MeasurableSet D →
        (∫⁻ p, F p D ∂P) = (residualPhysicalBackground d R S : Measure (Rd (d + 1))) D) ∧
      Integrable (fun p => Riesz.Analysis.signedDiscrepancyEnergy q
        ((F p).toSignedMeasure - (residualPhysicalBackground d R S : Measure (Rd (d + 1))).toSignedMeasure)) P ∧
      (∫ p, Riesz.Analysis.signedDiscrepancyEnergy q
        ((F p).toSignedMeasure - (residualPhysicalBackground d R S : Measure (Rd (d + 1))).toSignedMeasure) ∂P) ≤
        residualSphericalFillingConstant d A q * (r ^ q * M + R ^ d * r ^ (q - (d : ℝ))) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  obtain ⟨k, hscale, hupper⟩ := exists_residualCoarseDepth d A r R hrpos hrR
  refine ⟨k, ?_⟩
  dsimp only
  let n := residualFineCount d A R hR S
  let ν := residualFineMeasures d A R hR S
  let B := residualFineRegions d A R hR S
  let labels := residualCoarseLabels d A R hR S k r
  let masks := fun u => partitionRoundingMasks (labels u)
  have hmasks : Measurable masks :=
    (measurable_partitionRoundingMasks (n := n)).comp
      (measurable_residualCoarseLabels d A R hR S k r)
  obtain ⟨hν, hmass, hatom, hsupport, hdisjoint, hball, hmask, hlocal⟩ :=
    residualFineMeasures_sampling_inputs d hd A R hR S hS
  have hsum := residualFineMeasures_sum d A R hR S hS
  have hmasssum : ∑ i, ((ν i).mass : ℝ) = M := by
    have he := congrArg ENNReal.toReal
      ((congrArg (fun μ : Measure (Rd (d + 1)) => μ Set.univ) hsum).trans hM)
    change (cellMeasureSum (d + 1) n ν).real Set.univ = (M : ℝ≥0∞).toReal at he
    simpa only [cellMeasureSum_real_univ, ENNReal.toReal_natCast] using he
  have hroot : ∀ᵐ u ∂uniformCellMarks n, ∀ i j, labels u k i = labels u k j :=
    Filter.Eventually.of_forall (residualCoarseLabels_root d A R hR S k r)
  have hroot' : ∀ᵐ u ∂uniformCellMarks n, ∀ i j, masks u k (i, j) = true :=
    hroot.mono (fun u hu i j => by simp only [masks, partitionRoundingMasks, hu i j, decide_true])
  have hscaled : MeasurableSet ((fun x : Sphere d => R • x.val) '' S) := by
    exact (((Homeomorph.smulOfNeZero R hR.ne' : Rd (d + 1) ≃ₜ Rd (d + 1)).isClosedEmbedding.comp
      (isClosed_eq continuous_norm continuous_const :
        IsClosed {x : Rd (d + 1) | ‖x‖ = (1 : ℝ)}).isClosedEmbedding_subtypeVal).measurableEmbedding.measurableSet_image).mpr hS
  have hdiam (x : Rd (d + 1)) (hx : x ∈ Metric.closedBall 0 R)
      (y : Rd (d + 1)) (hy : y ∈ Metric.closedBall 0 R) : ‖x - y‖ ≤ 2 * R := by
    have hx' : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hy' : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    exact (norm_sub_le x y).trans (by linarith)
  refine ⟨residualSamplingRoundingMarks_probability (d + 1) n k ν masks hmasks,
    measurable_residualSampledMeasure (d + 1) n ν, ?_, ?_, ?_, ?_⟩
  · exact residualSamplingRoundingMarks_spec (d + 1) n k M ν hν hmass B hsupport
      hdisjoint _ hscaled hmask hmasssum masks hmasks hroot'
  · intro D hD
    rw [residualSamplingRoundingMarks_full_mean (d + 1) n k ν hmass masks hmasks D hD, hsum]
  · have hi := residualSamplingRoundingMarks_energy_integrable (d + 1) n k M q (2 * R)
      hq hq2 ν hν hmass B hsupport hdisjoint (Metric.closedBall 0 R)
      Metric.isClosed_closedBall.measurableSet hball hdiam hmasssum masks hmasks hroot'
    exact hi.congr (Filter.Eventually.of_forall (fun p =>
      congrArg (fun ξ => Riesz.Analysis.signedDiscrepancyEnergy q
        ((residualSampledMeasure (d + 1) n ν p).toSignedMeasure - ξ))
        (Measure.toSignedMeasure_congr hsum)))
  · have hqd : q < (d : ℝ) := hq2.trans_le (Nat.cast_le.mpr hd)
    have hb := residualSamplingRoundingMarks_energy_le (d + 1) n k M q (2 * R)
      ((3 / 2 : ℝ) * Real.sqrt d) hq hq2 (by positivity)
      ν hν hmass hatom B hsupport hdisjoint hlocal (Metric.closedBall 0 R)
      (isCompact_closedBall 0 R) hball hdiam hmasssum labels
      (measurable_residualCoarseLabels d A R hR S k r) hroot
      (fun j => residualCoarseDiameterFactor d A * ((2 : ℝ) ^ j * r))
      (fun j hj => mul_nonneg (residualCoarseDiameterFactor_nonneg d A) (by positivity))
      (fun j => A.size * (2 ^ (k - j)) ^ d)
      (residualCoarseLabels_card d A R hR S hS k r hrpos hscale)
      (residualCoarseLabels_diameter d A R hR S hS k r hrpos hscale)
    have hs := residualSphericalBudget_le d k M A q r R hq hqd hr hupper
    have hb' := hb.trans (by simpa only [pow_zero, one_mul] using hs)
    exact (integral_congr_ae (Filter.Eventually.of_forall (fun p =>
      congrArg (fun ξ => Riesz.Analysis.signedDiscrepancyEnergy q
        ((residualSampledMeasure (d + 1) n ν p).toSignedMeasure - ξ))
        (Measure.toSignedMeasure_congr hsum)))).symm.trans_le hb'

/-! Measurable labeling of the actual finite random configuration. The
bounded quadratic kernel is used only to transfer Bochner integrals through
the two counting-measure pushforwards; the energy is the original signed Dq. -/

theorem exists_finiteTupleRealization_of_bounded_marks
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d M : ℕ) (q L : ℝ) (hq : 0 < q) (hq2 : q < 2)
    (F : Ω → Measure (Rd d)) [∀ p, IsFiniteMeasure (F p)] (hF : Measurable F)
    (ν : FiniteMeasure (Rd d)) (hνmass : (ν : Measure (Rd d)) Set.univ = M)
    (S : Set (Rd d)) (hS : MeasurableSet S) (hν : (ν : Measure (Rd d)) Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L)
    (hgood : ∀ᵐ p ∂P, (IsSimpleConfiguration d (F p) ∧ F p Set.univ = (M : ℝ≥0∞)) ∧
      F p Sᶜ = 0)
    (hmean : ∀ D : Set (Rd d), MeasurableSet D → (∫⁻ p, F p D ∂P) = ν D) :
    ∃ Q : Measure (Fin M → Rd d), IsProbabilityMeasure Q ∧
      (∀ᵐ x ∂Q, Function.Injective x ∧ ∀ i, x i ∈ S) ∧
      tupleMeanMeasure d M Q = (ν : Measure (Rd d)) ∧
      Integrable (negativeTupleSignedEnergy d M q ν) Q ∧
      (∫ x, negativeTupleSignedEnergy d M q ν x ∂Q) =
        ∫ p, Riesz.Analysis.signedDiscrepancyEnergy q
          ((F p).toSignedMeasure - (ν : Measure (Rd d)).toSignedMeasure) ∂P := by
  let Γ := P.map F
  letI : IsProbabilityMeasure Γ := Measure.isProbabilityMeasure_map hF.aemeasurable
  have hΓ : ∀ᵐ μ ∂Γ, IsSimpleConfiguration d μ ∧ μ Set.univ = (M : ℝ≥0∞) :=
    (ae_map_iff hF.aemeasurable (measurableSet_simple_fixed_count d M)).mpr
      (hgood.mono (fun p hp => hp.1))
  obtain ⟨Q, hQ, hinj, hmap⟩ := exists_tuple_law_of_simple_fixed_count d M Γ hΓ
  letI : IsProbabilityMeasure Q := hQ
  letI : ∀ x : Fin M → Rd d, IsFiniteMeasure (tupleCounting d M x) :=
    fun x => tupleCounting_isFiniteMeasure d M x
  have hΓsupport : ∀ᵐ μ ∂Γ, μ Sᶜ = 0 :=
    (ae_map_iff hF.aemeasurable
      (measurableSet_eq_fun (Measure.measurable_coe hS.compl) measurable_const)).mpr
      (hgood.mono (fun p hp => hp.2))
  have hsupport : ∀ᵐ x ∂Q, tupleCounting d M x Sᶜ = 0 := by
    rw [← hmap] at hΓsupport
    exact (ae_map_iff (measurable_tupleCounting d M).aemeasurable
      (measurableSet_eq_fun (Measure.measurable_coe hS.compl) measurable_const)).mp hΓsupport
  have hQgood : ∀ᵐ x ∂Q, Function.Injective x ∧ ∀ i, x i ∈ S := by
    filter_upwards [hinj, hsupport] with x hx hs
    exact ⟨hx, (tupleCounting_compl_eq_zero_iff d M x S hS).mp hs⟩
  have hQmean : tupleMeanMeasure d M Q = (ν : Measure (Rd d)) := by
    apply Measure.ext
    intro D hD
    rw [tupleMeanMeasure_apply d M Q D hD]
    calc
      (∫⁻ x, tupleCounting d M x D ∂Q) =
          ∫⁻ μ, μ D ∂Q.map (tupleCounting d M) :=
        (lintegral_map (Measure.measurable_coe hD) (measurable_tupleCounting d M)).symm
      _ = ∫⁻ μ, μ D ∂P.map F := by rw [hmap]
      _ = ∫⁻ p, F p D ∂P := lintegral_map (Measure.measurable_coe hD) hF
      _ = (ν : Measure (Rd d)) D := (hmean D hD).trans
        (FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν D)
  have hQi : Integrable (negativeTupleSignedEnergy d M q ν) Q := by
    exact finiteDifferenceDiscrepancy_integrable Q d M q L hq hq2
      (tupleCounting d M) (measurable_tupleCounting d M) (ν : Measure (Rd d)) hνmass
      S hS hν hdiam (hsupport.mono (fun x hx => ⟨hx, tupleCounting_univ d M x⟩))
  let G : Measure (Rd d) → ℝ := fun μ =>
    Riesz.Analysis.differenceKernelQuadratic (fun x y : Rd d => K_s (-q) ‖x - y‖)
      (boundedMeasureKernel d M μ) (ν : Measure (Rd d))
  have hG : StronglyMeasurable G := by
    apply stronglyMeasurable_boundedQuadratic
    simpa only [K_s, neg_neg, Pi.sub_apply] using
      (((measurable_fst.sub measurable_snd).norm.pow_const q).div_const (-q)).stronglyMeasurable
  have hGE (μ : Measure (Rd d)) [IsFiniteMeasure μ]
      (hm : μ Set.univ = (M : ℝ≥0∞)) (hs : μ Sᶜ = 0) :
      G μ = Riesz.Analysis.signedDiscrepancyEnergy q
        (μ.toSignedMeasure - (ν : Measure (Rd d)).toSignedMeasure) := by
    dsimp only [G]
    simp only [boundedMeasureKernel, Kernel.coe_mk, if_pos hm.le]
    exact (Riesz.Analysis.signedDiscrepancyEnergy_sub_toSignedMeasure q L hq hq2
      μ (ν : Measure (Rd d)) (congrArg ENNReal.toReal (hm.trans hνmass.symm))
      S hS hs hν hdiam).symm
  have heQ : ∀ᵐ x ∂Q, G (tupleCounting d M x) = negativeTupleSignedEnergy d M q ν x :=
    hsupport.mono (fun x hx => hGE _ (tupleCounting_univ d M x) hx)
  have heP : ∀ᵐ p ∂P, G (F p) = Riesz.Analysis.signedDiscrepancyEnergy q
      ((F p).toSignedMeasure - (ν : Measure (Rd d)).toSignedMeasure) :=
    hgood.mono (fun p hp => hGE _ hp.1.2 hp.2)
  refine ⟨Q, hQ, hQgood, hQmean, hQi, ?_⟩
  calc
    _ = ∫ x, G (tupleCounting d M x) ∂Q := integral_congr_ae (Filter.EventuallyEq.symm heQ)
    _ = ∫ μ, G μ ∂Γ := by
      rw [← hmap]
      exact (integral_map_of_stronglyMeasurable (measurable_tupleCounting d M) hG).symm
    _ = ∫ p, G (F p) ∂P := integral_map_of_stronglyMeasurable hF hG
    _ = _ := integral_congr_ae heP

/-- Actual fixed-count residual tuple law, with the exact physical restricted
area as mean and a coarse-start signed-energy estimate. -/
theorem exists_residualSphericalFilling_tuple (d : ℕ) (hd : 2 ≤ d)
    (A : ResidualSphericalAtlas d) (q r R : ℝ) (hq : 0 < q) (hq2 : q < 2)
    (hr : 1 ≤ r) (hrR : r ≤ R) (hR : 0 < R)
    (S : Set (Sphere d)) (hS : MeasurableSet S) (M : ℕ)
    (hM : (residualPhysicalBackground d R S : Measure (Rd (d + 1))) Set.univ = M) :
    ∃ Q : Measure (Fin M → Rd (d + 1)), IsProbabilityMeasure Q ∧
      (∀ᵐ x ∂Q, Function.Injective x ∧
        ∀ i, x i ∈ (fun y : Sphere d => R • y.val) '' S) ∧
      tupleMeanMeasure (d + 1) M Q = (residualPhysicalBackground d R S : Measure (Rd (d + 1))) ∧
      Integrable (negativeTupleSignedEnergy (d + 1) M q (residualPhysicalBackground d R S)) Q ∧
      (∫ x, negativeTupleSignedEnergy (d + 1) M q (residualPhysicalBackground d R S) x ∂Q) ≤
        residualSphericalFillingConstant d A q * (r ^ q * M + R ^ d * r ^ (q - (d : ℝ))) := by
  obtain ⟨k, hk⟩ := exists_residualSphericalFilling_marks d hd A q r R hq hq2 hr hrR hR S hS M hM
  let n := residualFineCount d A R hR S
  let ν := residualFineMeasures d A R hR S
  let labels := residualCoarseLabels d A R hR S k r
  let masks := fun u => partitionRoundingMasks (labels u)
  let hmasks := (measurable_partitionRoundingMasks (n := n)).comp
    (measurable_residualCoarseLabels d A R hR S k r)
  let P := residualSamplingRoundingMarks (d + 1) n k ν masks hmasks
  let F := residualSampledMeasure (d + 1) n ν
  change IsProbabilityMeasure P ∧ Measurable F ∧ _ at hk
  rcases hk with ⟨hP, hF, hgood, hmean, hi, hb⟩
  letI : IsProbabilityMeasure P := hP
  let T := (fun y : Sphere d => R • y.val) '' S
  have hT : MeasurableSet T := by
    exact (((Homeomorph.smulOfNeZero R hR.ne' : Rd (d + 1) ≃ₜ Rd (d + 1)).isClosedEmbedding.comp
      (isClosed_eq continuous_norm continuous_const :
        IsClosed {x : Rd (d + 1) | ‖x‖ = (1 : ℝ)}).isClosedEmbedding_subtypeVal).measurableEmbedding.measurableSet_image).mpr hS
  have hνT : (residualPhysicalBackground d R S : Measure (Rd (d + 1))) Tᶜ = 0 := by
    rw [← hmean Tᶜ hT.compl]
    simpa only [lintegral_zero] using lintegral_congr_ae (hgood.mono (fun p hp => hp.2))
  have hdiam (x : Rd (d + 1)) (hx : x ∈ T) (y : Rd (d + 1)) (hy : y ∈ T) :
      ‖x - y‖ ≤ 2 * R := by
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    exact (norm_sub_le _ _).trans (by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hR, a.property, b.property, mul_one]
      linarith)
  obtain ⟨Q, hQ, hQgood, hQmean, hQi, heq⟩ :=
    exists_finiteTupleRealization_of_bounded_marks P (d + 1) M q (2 * R) hq hq2 F hF
      (residualPhysicalBackground d R S) hM T hT hνT hdiam hgood
      (fun D hD => (hmean D hD).trans
        (FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure (residualPhysicalBackground d R S) D).symm)
  exact ⟨Q, hQ, hQgood, hQmean, hQi, heq.trans_le hb⟩

end Riesz.Negative
