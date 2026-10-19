import Riesz.Negative.DyadicRounding
import Riesz.Negative.SamplingEnergy
import Riesz.Analysis.DiscrepancyYoung
import Riesz.Analysis.DiscrepancyDifference

/-!
Continuous cell sampling followed by the actual multiscale rounding law.
The sampling and rounding corrections are combined by the verified Young
bound, retaining exact measure means and integer point counts.
-/

noncomputable section

open MeasureTheory RieszShowcase ProbabilityTheory
open scoped ENNReal Classical ProbabilityTheory

namespace Riesz.Negative

theorem weightedAtomicMeasure_toSigned_of_nonneg (d n : ℕ)
    (x : Fin n → Rd d) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (weightedAtomicMeasure d n x w).toSignedMeasure = weightedSignedMeasure d n x w := by
  simp [weightedAtomicMeasure_toSigned, weightedSignedMeasure, hw]

theorem weightedAtomicMeasure_append (d a n : ℕ)
    (x : Fin a → Rd d) (y : Fin n → Rd d) (w : Fin a → ℝ) (z : Fin n → ℝ) :
    weightedAtomicMeasure d (a + n) (Fin.append x y) (Fin.append w z) =
      weightedAtomicMeasure d a x w + weightedAtomicMeasure d n y z := by
  simp [weightedAtomicMeasure, Fin.sum_univ_add]

theorem weightedAtomicMeasure_signed_difference (d n : ℕ) (x : Fin n → Rd d)
    (v w : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    (weightedAtomicMeasure d n x v).toSignedMeasure -
      (weightedAtomicMeasure d n x w).toSignedMeasure =
        weightedSignedMeasure d n x (fun i => v i - w i) := by
  simp only [weightedAtomicMeasure_toSigned_of_nonneg d n x v hv,
    weightedAtomicMeasure_toSigned_of_nonneg d n x w hw,
    weightedSignedMeasure]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ =>
    (sub_smul (v i) (w i) (Measure.dirac (x i)).toSignedMeasure).symm)

theorem weightedSignedMeasure_univ (d n : ℕ) (x : Fin n → Rd d) (w : Fin n → ℝ) :
    weightedSignedMeasure d n x w Set.univ = ∑ i, w i := by
  simp [weightedSignedMeasure, _root_.sum_apply, _root_.smul_apply,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ, measureReal_def]

theorem weightedAtomicMeasure_concentrated (d n : ℕ) (x : Fin n → Rd d)
    (w : Fin n → ℝ) (S : Set (Rd d)) (hx : ∀ i, x i ∈ S) :
    weightedAtomicMeasure d n x w Sᶜ = 0 := by
  simp [weightedAtomicMeasure, Measure.finsetSum_apply, Measure.smul_apply, hx]

theorem weightedSignedMeasure_concentrated (d n : ℕ) (x : Fin n → Rd d)
    (hinj : Function.Injective x) (w : Fin n → ℝ) (S : Set (Rd d))
    (hx : ∀ i, x i ∈ S) : (weightedSignedMeasure d n x w).totalVariation Sᶜ = 0 := by
  simp only [SignedMeasure.totalVariation,
    (weightedSignedMeasure_jordan_parts d n x hinj w).1,
    (weightedSignedMeasure_jordan_parts d n x hinj w).2, Measure.add_apply,
    weightedAtomicMeasure_concentrated d n x w S hx,
    weightedAtomicMeasure_concentrated d n x (fun i => -w i) S hx, add_zero]

theorem cellMeasureSum_real_univ (d n : ℕ) (ν : Fin n → FiniteMeasure (Rd d)) :
    (cellMeasureSum d n ν).real Set.univ = ∑ i, ((ν i).mass : ℝ) := by
  rw [measureReal_def, cellMeasureSum, Measure.finsetSum_apply]
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top (ν i : Measure (Rd d)) Set.univ)]
  rfl

theorem sampledCellDiscrepancy_mass_zero (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (y : Fin n → Rd d) :
    sampledCellDiscrepancy d n ν y Set.univ = 0 := by
  rw [sampledCellDiscrepancy,
    weightedAtomicMeasure_toSigned_of_nonneg d n y _ (fun i => NNReal.coe_nonneg _),
    _root_.sub_apply, weightedSignedMeasure_univ,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    cellMeasureSum_real_univ, sub_self]

theorem sampledCellDiscrepancy_concentrated (d n : ℕ)
    (ν : Fin n → FiniteMeasure (Rd d)) (hatom : ∀ i y, ν i {y} = 0)
    (y : Fin n → Rd d) (S : Set (Rd d)) (hy : ∀ i, y i ∈ S)
    (hsupport : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0) :
    (sampledCellDiscrepancy d n ν y).totalVariation Sᶜ = 0 := by
  simp [SignedMeasure.totalVariation,
    (sampledCellDiscrepancy_jordan_parts d n ν hatom y).1,
    (sampledCellDiscrepancy_jordan_parts d n ν hatom y).2,
    weightedAtomicMeasure_concentrated d n y _ S hy,
    cellMeasureSum, hsupport]

def sampledAtomicSites (d a n : ℕ) (x : Fin a → Rd d)
    (ν : Fin n → FiniteMeasure (Rd d)) (u : Fin n → unitInterval) : Fin (a + n) → Rd d :=
  Fin.append x (sampledCellSites d n ν u)

def sampledAtomicWeights (d a n : ℕ) (w : Fin a → ℝ)
    (ν : Fin n → FiniteMeasure (Rd d)) : Fin (a + n) → ℝ :=
  Fin.append w (fun i => ((ν i).mass : ℝ))

def samplingRoundingInput (d a n : ℕ) (x : Fin a → Rd d) (w : Fin a → ℝ)
    (ν : Fin n → FiniteMeasure (Rd d)) : Measure (Rd d) :=
  weightedAtomicMeasure d a x w + cellMeasureSum d n ν

instance samplingRoundingInput_isFiniteMeasure (d a n : ℕ) (x : Fin a → Rd d)
    (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d)) :
    IsFiniteMeasure (samplingRoundingInput d a n x w ν) :=
  inferInstanceAs (IsFiniteMeasure (weightedAtomicMeasure d a x w + cellMeasureSum d n ν))

def sampledRoundingDiscrepancy (d a n : ℕ) (x : Fin a → Rd d) (w : Fin a → ℝ)
    (ν : Fin n → FiniteMeasure (Rd d)) (u : Fin n → unitInterval) (v : Fin (a + n) → ℝ) :
    SignedMeasure (Rd d) :=
  (weightedAtomicMeasure d (a + n) (sampledAtomicSites d a n x ν u) v).toSignedMeasure -
    (samplingRoundingInput d a n x w ν).toSignedMeasure

theorem sampledAtomicWeights_valid (d a n : ℕ) (w : Fin a → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (ν : Fin n → FiniteMeasure (Rd d))
    (hmass : ∀ i, (ν i).mass ≤ 1) :
    ∀ i, 0 ≤ sampledAtomicWeights d a n w ν i ∧ sampledAtomicWeights d a n w ν i ≤ 1 := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · exact fun j => by simpa [sampledAtomicWeights] using hw j
  · exact fun j => by simpa [sampledAtomicWeights] using
      (And.intro (NNReal.coe_nonneg (ν j).mass) (NNReal.coe_le_coe.mpr (hmass j)))

def sampledDyadicRoundingLaw (d a n k : ℕ) (r : ℝ) (x : Fin a → Rd d) (w : Fin a → ℝ)
    (ν : Fin n → FiniteMeasure (Rd d)) (u : Fin n → unitInterval) : Measure (Fin (a + n) → ℝ) :=
  multiscaleRoundingLaw (k + 1)
    (partitionRoundingMasks (dyadicCubeLabels d (a + n) r (sampledAtomicSites d a n x ν u)))
    (sampledAtomicWeights d a n w ν)

instance sampledDyadicRoundingLaw_probability (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d))
    (u : Fin n → unitInterval) : IsProbabilityMeasure (sampledDyadicRoundingLaw d a n k r x w ν u) :=
  (multiscaleRoundingLaw_measurable_probability (k + 1)).2 _ _

theorem measurable_sampledAtomicSites (d a n : ℕ) (x : Fin a → Rd d)
    (ν : Fin n → FiniteMeasure (Rd d)) : Measurable (sampledAtomicSites d a n x ν) := by
  unfold sampledAtomicSites sampledCellSites
  refine measurable_pi_lambda _ (Fin.addCases ?_ ?_)
  · exact fun i => by simpa only [Fin.append_left] using
      (measurable_const : Measurable (fun _ : Fin n → unitInterval => x i))
  · exact fun i => by simpa only [Fin.append_right] using
      (show Measurable (fun u : Fin n → unitInterval =>
        Riesz.Configuration.sampleFiniteMeasure (ν i) (u i)) from
        (Riesz.Configuration.measurable_sampleFiniteMeasure_fixed (ν i)).comp (measurable_pi_apply i))

theorem measurable_sampledDyadicRoundingLaw (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d)) :
    Measurable (sampledDyadicRoundingLaw d a n k r x w ν) := by
  exact (measurable_dyadicCubeRoundingLaw d (a + n) k).comp
    (f := fun u : Fin n → unitInterval =>
      ((r, sampledAtomicSites d a n x ν u), sampledAtomicWeights d a n w ν))
    ((measurable_const.prodMk (measurable_sampledAtomicSites d a n x ν)).prodMk measurable_const)

def sampledDyadicRoundingKernel (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d)) :
    Kernel (Fin n → unitInterval) (Fin (a + n) → ℝ) where
  toFun := sampledDyadicRoundingLaw d a n k r x w ν
  measurable' := measurable_sampledDyadicRoundingLaw d a n k r x w ν

instance sampledDyadicRoundingKernel_isMarkov (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d)) :
    IsMarkovKernel (sampledDyadicRoundingKernel d a n k r x w ν) where
  isProbabilityMeasure _ := inferInstanceAs (IsProbabilityMeasure (sampledDyadicRoundingLaw _ _ _ _ _ _ _ _ _))

def sampledRoundingMarks (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d)) :
    Measure ((Fin n → unitInterval) × (Fin (a + n) → ℝ)) :=
  (uniformCellMarks n).compProd (sampledDyadicRoundingKernel d a n k r x w ν)

theorem measurable_weightedAtomicMeasure (d n : ℕ) :
    Measurable (fun p : (Fin n → Rd d) × (Fin n → ℝ) => weightedAtomicMeasure d n p.1 p.2) := by
  unfold weightedAtomicMeasure
  refine Measure.measurable_of_measurable_coe _ (fun D hD => ?_)
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  exact Finset.measurable_fun_sum _ (fun i _ =>
    (ENNReal.measurable_ofReal.comp ((measurable_pi_apply i).comp measurable_snd)).mul
      ((Measure.measurable_coe hD).comp
        (Measure.measurable_dirac.comp ((measurable_pi_apply i).comp measurable_fst))))

instance sampledRoundingMarks_probability (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d)) :
    IsProbabilityMeasure (sampledRoundingMarks d a n k r x w ν) :=
  inferInstanceAs (IsProbabilityMeasure
    ((uniformCellMarks n).compProd (sampledDyadicRoundingKernel d a n k r x w ν)))

def sampledRoundedMeasure (d a n : ℕ) (x : Fin a → Rd d)
    (ν : Fin n → FiniteMeasure (Rd d))
    (p : (Fin n → unitInterval) × (Fin (a + n) → ℝ)) : Measure (Rd d) :=
  weightedAtomicMeasure d (a + n) (sampledAtomicSites d a n x ν p.1) p.2

theorem measurable_sampledRoundedMeasure (d a n : ℕ) (x : Fin a → Rd d)
    (ν : Fin n → FiniteMeasure (Rd d)) : Measurable (sampledRoundedMeasure d a n x ν) := by
  exact (measurable_weightedAtomicMeasure d (a + n)).comp
    (f := fun p : (Fin n → unitInterval) × (Fin (a + n) → ℝ) =>
      (sampledAtomicSites d a n x ν p.1, p.2))
    (((measurable_sampledAtomicSites d a n x ν).comp measurable_fst).prodMk measurable_snd)

theorem sampledRoundingMarks_full_mean (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (ν : Fin n → FiniteMeasure (Rd d)) (hmass : ∀ i, (ν i).mass ≤ 1)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ p, sampledRoundedMeasure d a n x ν p D ∂sampledRoundingMarks d a n k r x w ν) =
      samplingRoundingInput d a n x w ν D := by
  rw [sampledRoundingMarks, Measure.lintegral_compProd
    (f := fun p : (Fin n → unitInterval) × (Fin (a + n) → ℝ) =>
      sampledRoundedMeasure d a n x ν p D)
    ((Measure.measurable_coe hD).comp (measurable_sampledRoundedMeasure d a n x ν))]
  change (∫⁻ u, ∫⁻ v, weightedAtomicMeasure d (a + n) (sampledAtomicSites d a n x ν u) v D
    ∂sampledDyadicRoundingLaw d a n k r x w ν u ∂uniformCellMarks n) = _
  simp_rw [sampledDyadicRoundingLaw, multiscaleRoundingLaw_weightedAtomic_mean _ _ _ _
    (sampledAtomicWeights_valid d a n w hw ν hmass) D]
  simp only [sampledAtomicSites, sampledAtomicWeights, weightedAtomicMeasure_append, Measure.add_apply]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    sampledCellSites_full_mean d n ν D hD]
  rfl

theorem sampledAtomicWeights_sum (d a n : ℕ) (w : Fin a → ℝ)
    (ν : Fin n → FiniteMeasure (Rd d)) :
    (∑ i, sampledAtomicWeights d a n w ν i) = (∑ i, w i) + ∑ i, ((ν i).mass : ℝ) := by
  simp [sampledAtomicWeights, Fin.sum_univ_add]

theorem weightedAtomicMeasure_append_toSigned (d a n : ℕ)
    (x : Fin a → Rd d) (y : Fin n → Rd d) (w : Fin a → ℝ) (z : Fin n → ℝ) :
    (weightedAtomicMeasure d (a + n) (Fin.append x y) (Fin.append w z)).toSignedMeasure =
      (weightedAtomicMeasure d a x w).toSignedMeasure +
        (weightedAtomicMeasure d n y z).toSignedMeasure := by
  simp [weightedAtomicMeasure_toSigned, Fin.sum_univ_add]

theorem sampledRoundingDiscrepancy_eq (d a n : ℕ) (x : Fin a → Rd d)
    (w : Fin a → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (ν : Fin n → FiniteMeasure (Rd d)) (hmass : ∀ i, (ν i).mass ≤ 1)
    (u : Fin n → unitInterval) (v : Fin (a + n) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    sampledRoundingDiscrepancy d a n x w ν u v =
      sampledCellDiscrepancy d n ν (sampledCellSites d n ν u) +
        weightedSignedMeasure d (a + n) (sampledAtomicSites d a n x ν u)
          (fun i => v i - sampledAtomicWeights d a n w ν i) := by
  unfold sampledRoundingDiscrepancy samplingRoundingInput
  rw [Measure.toSignedMeasure_add,
    ← weightedAtomicMeasure_signed_difference d (a + n) (sampledAtomicSites d a n x ν u)
      v (sampledAtomicWeights d a n w ν) hv
      (fun i => (sampledAtomicWeights_valid d a n w hw ν hmass i).1)]
  unfold sampledAtomicSites sampledAtomicWeights sampledCellDiscrepancy
  rw [weightedAtomicMeasure_append_toSigned]
  abel

theorem sampledAtomicSites_mem (d a n : ℕ) (x : Fin a → Rd d)
    (ν : Fin n → FiniteMeasure (Rd d)) (u : Fin n → unitInterval)
    (S : Set (Rd d)) (hx : ∀ i, x i ∈ S) (hy : ∀ i, sampledCellSites d n ν u i ∈ S) :
    ∀ i, sampledAtomicSites d a n x ν u i ∈ S := by
  exact Fin.addCases (fun i => by simpa [sampledAtomicSites] using hx i)
    (fun i => by simpa [sampledAtomicSites] using hy i)

theorem sampledRoundingDiscrepancy_energy_le (d a n : ℕ) (q : ℝ)
    (hq : 0 < q) (hq_two : q < 2) (x : Fin a → Rd d) (w : Fin a → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (ν : Fin n → FiniteMeasure (Rd d))
    (hmass : ∀ i, (ν i).mass ≤ 1) (hatom : ∀ i y, ν i {y} = 0)
    (u : Fin n → unitInterval) (v : Fin (a + n) → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hsum : ∑ i, v i = ∑ i, sampledAtomicWeights d a n w ν i)
    (hinj : Function.Injective (sampledAtomicSites d a n x ν u))
    (S : Set (Rd d)) (hcompact : IsCompact S) (hx : ∀ i, x i ∈ S)
    (hy : ∀ i, sampledCellSites d n ν u i ∈ S)
    (hsupport : ∀ i, (ν i : Measure (Rd d)) Sᶜ = 0) :
    Riesz.Analysis.signedDiscrepancyEnergy q (sampledRoundingDiscrepancy d a n x w ν u v) ≤
      2 * Riesz.Analysis.signedDiscrepancyEnergy q
        (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u)) +
      2 * Riesz.Analysis.signedDiscrepancyEnergy q
        (weightedSignedMeasure d (a + n) (sampledAtomicSites d a n x ν u)
          (fun i => v i - sampledAtomicWeights d a n w ν i)) := by
  rw [sampledRoundingDiscrepancy_eq d a n x w hw ν hmass u v hv]
  refine Riesz.Analysis.signedDiscrepancyEnergy_add_le q hq hq_two _ _
    (sampledCellDiscrepancy_mass_zero d n ν _) ?_ S hcompact
    (sampledCellDiscrepancy_concentrated d n ν hatom _ S hy hsupport)
    (weightedSignedMeasure_concentrated d (a + n) _ hinj _ S
      (sampledAtomicSites_mem d a n x ν u S hx hy))
  rw [weightedSignedMeasure_univ, Finset.sum_sub_distrib, hsum, sub_self]

theorem finsetCounting_simple (d : ℕ) (S : Finset (Rd d)) :
    IsSimpleConfiguration d (∑ y ∈ S, Measure.dirac y) := by
  refine ⟨(S : Set (Rd d)), fun K _ => S.finite_toSet.inter_of_left K, ?_⟩
  simp [Measure.sum_fintype, Finset.sum_attach]

theorem sampledDyadicRoundingLaw_spec (d a n k : ℕ) (r : ℝ) (hr : 0 < r)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (ν : Fin n → FiniteMeasure (Rd d)) (hmass : ∀ i, (ν i).mass ≤ 1)
    (u : Fin n → unitInterval) (hinj : Function.Injective (sampledAtomicSites d a n x ν u))
    (hsites : ∀ i, sampledAtomicSites d a n x ν u i ∈ cube d ((2 : ℝ) ^ k * r))
    (M : ℕ) (hM : (∑ i, w i) + ∑ i, ((ν i).mass : ℝ) = M) :
    ∀ᵐ v ∂sampledDyadicRoundingLaw d a n k r x w ν u,
      IsSimpleConfiguration d (sampledRoundedMeasure d a n x ν (u, v)) ∧
      sampledRoundedMeasure d a n x ν (u, v) (cube d ((2 : ℝ) ^ k * r))ᶜ = 0 ∧
      sampledRoundedMeasure d a n x ν (u, v) Set.univ = (M : ℝ≥0∞) := by
  filter_upwards [dyadicCubeRounding_occupiedSites_spec d (a + n) k r hr
    (sampledAtomicSites d a n x ν u) hinj hsites (sampledAtomicWeights d a n w ν)
    (sampledAtomicWeights_valid d a n w hw ν hmass) M
    ((sampledAtomicWeights_sum d a n w ν).trans hM)] with v hv
  refine ⟨(congrArg (IsSimpleConfiguration d) hv.2).mpr (finsetCounting_simple d _),
    weightedAtomicMeasure_concentrated d (a + n) _ v _ hsites, ?_⟩
  simp [sampledRoundedMeasure, hv.2, Measure.finsetSum_apply, hv.1]

theorem sampledRoundingMarks_spec (d a n k : ℕ) (r : ℝ) (hr : 0 < r)
    (x : Fin a → Rd d) (hinj : Function.Injective x)
    (hx : ∀ i, x i ∈ cube d ((2 : ℝ) ^ k * r)) (w : Fin a → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (ν : Fin n → FiniteMeasure (Rd d))
    (hν : ∀ i, ν i ≠ 0) (hmass : ∀ i, (ν i).mass ≤ 1) (hatom : ∀ i y, ν i {y} = 0)
    (B : Fin n → Set (Rd d)) (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hB : ∀ i, B i ⊆ cube d ((2 : ℝ) ^ k * r))
    (M : ℕ) (hM : (∑ i, w i) + ∑ i, ((ν i).mass : ℝ) = M) :
    ∀ᵐ p ∂sampledRoundingMarks d a n k r x w ν,
      (IsSimpleConfiguration d (sampledRoundedMeasure d a n x ν p) ∧
        sampledRoundedMeasure d a n x ν p Set.univ = (M : ℝ≥0∞)) ∧
      sampledRoundedMeasure d a n x ν p (cube d ((2 : ℝ) ^ k * r))ᶜ = 0 := by
  apply Measure.ae_compProd_of_ae_ae
    (((measurableSet_simple_fixed_count d M).preimage (measurable_sampledRoundedMeasure d a n x ν)).inter
      ((measurableSet_eq_fun (Measure.measurable_coe (measurableSet_cube d ((2 : ℝ) ^ k * r)).compl)
        measurable_const).preimage (measurable_sampledRoundedMeasure d a n x ν)))
  filter_upwards [sampledCellSites_append_injective d a n x hinj ν hν hatom B hsupport hdisjoint,
    sampledCellSites_supported d n ν hν B hsupport] with u hu hy
  exact (sampledDyadicRoundingLaw_spec d a n k r hr x w hw ν hmass u hu
    (sampledAtomicSites_mem d a n x ν u _ hx (fun i => hB i (hy i))) M hM).mono
      (fun v hv => ⟨⟨hv.1, hv.2.2⟩, hv.2.1⟩)

def sampledRoundedLaw (d a n k : ℕ) (r : ℝ) (x : Fin a → Rd d) (w : Fin a → ℝ)
    (ν : Fin n → FiniteMeasure (Rd d)) : ConfigurationLaw d :=
  Measure.map (sampledRoundedMeasure d a n x ν) (sampledRoundingMarks d a n k r x w ν)

instance sampledRoundedLaw_probability (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d)) :
    IsProbabilityMeasure (sampledRoundedLaw d a n k r x w ν) :=
  Measure.isProbabilityMeasure_map (measurable_sampledRoundedMeasure d a n x ν).aemeasurable

theorem sampledRoundedLaw_full_mean (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (ν : Fin n → FiniteMeasure (Rd d)) (hmass : ∀ i, (ν i).mass ≤ 1)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ μ, μ D ∂sampledRoundedLaw d a n k r x w ν) = samplingRoundingInput d a n x w ν D := by
  rw [sampledRoundedLaw, lintegral_map (Measure.measurable_coe hD)
    (measurable_sampledRoundedMeasure d a n x ν)]
  exact sampledRoundingMarks_full_mean d a n k r x w hw ν hmass D hD

/-- A positive-measure bound for the energy representation used below. -/
theorem negativeDifferenceQuadratic_le (d : ℕ) (q L : ℝ) (hq : 0 < q)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbound : ∀ᵐ p : Rd d × Rd d ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L) :
    Riesz.Analysis.differenceKernelQuadratic (fun x y : Rd d => K_s (-q) ‖x - y‖) μ ν ≤
      2 * L ^ q * μ.real Set.univ * ν.real Set.univ / q := by
  have h := div_le_div_of_nonneg_right
    (Riesz.Analysis.neg_rpow_quadratic_le q L hq.le μ ν hbound) hq.le
  convert! h using 1
  simp only [Riesz.Analysis.differenceKernelQuadratic, K_s, neg_neg, div_neg,
    integral_neg, integral_div]
  ring

theorem finiteDifferenceDiscrepancy_bounds (d M : ℕ) (q L : ℝ)
    (hq : 0 < q) (hq_two : q < 2) (μ ν : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμmass : μ Set.univ = M) (hνmass : ν Set.univ = M)
    (S : Set (Rd d)) (hS : MeasurableSet S) (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L) :
    0 ≤ Riesz.Analysis.signedDiscrepancyEnergy q (μ.toSignedMeasure - ν.toSignedMeasure) ∧
      Riesz.Analysis.signedDiscrepancyEnergy q (μ.toSignedMeasure - ν.toSignedMeasure) ≤
        2 * L ^ q * (M : ℝ) ^ 2 / q := by
  have hμreal : μ.real Set.univ = M := by simp [measureReal_def, hμmass]
  have hνreal : ν.real Set.univ = M := by simp [measureReal_def, hνmass]
  rw [Riesz.Analysis.signedDiscrepancyEnergy_sub_toSignedMeasure q L hq hq_two μ ν
    (hμreal.trans hνreal.symm) S hS hμ hν hdiam]
  refine ⟨Riesz.Analysis.negative_riesz_quadratic_nonneg (-q) L (neg_lt_neg hq_two)
    (neg_lt_zero.mpr hq) μ ν (hμreal.trans hνreal.symm)
    (Riesz.Analysis.ae_distance_le_of_concentrated μ μ S L hμ hμ hdiam)
    (Riesz.Analysis.ae_distance_le_of_concentrated μ ν S L hμ hν hdiam)
    (Riesz.Analysis.ae_distance_le_of_concentrated ν ν S L hν hν hdiam), ?_⟩
  simpa only [hμreal, hνreal, pow_two, mul_assoc] using
    negativeDifferenceQuadratic_le d q L hq μ ν
      (Riesz.Analysis.ae_distance_le_of_concentrated μ ν S L hμ hν hdiam)

theorem finiteDifferenceDiscrepancy_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d M : ℕ) (q L : ℝ) (hq : 0 < q) (hq_two : q < 2)
    (F : Ω → Measure (Rd d)) [∀ u, IsFiniteMeasure (F u)] (hF : Measurable F)
    (ν : Measure (Rd d)) [IsFiniteMeasure ν] (hνmass : ν Set.univ = M)
    (S : Set (Rd d)) (hS : MeasurableSet S) (hν : ν Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L)
    (hspec : ∀ᵐ u ∂P, F u Sᶜ = 0 ∧ F u Set.univ = M) :
    AEStronglyMeasurable (fun u => Riesz.Analysis.signedDiscrepancyEnergy q
      ((F u).toSignedMeasure - ν.toSignedMeasure)) P := by
  have hk : StronglyMeasurable (fun p : Rd d × Rd d => K_s (-q) ‖p.1 - p.2‖) := by
    simpa only [K_s, neg_neg, Pi.sub_apply] using
      (((measurable_fst.sub measurable_snd).norm.pow_const q).div_const (-q)).stronglyMeasurable
  have hmeas := (stronglyMeasurable_boundedQuadratic d M ν
    (fun x y => K_s (-q) ‖x - y‖) hk).comp_measurable hF
  refine hmeas.aestronglyMeasurable.congr ?_
  filter_upwards [hspec] with u hu
  simp only [Function.comp_apply, boundedMeasureKernel, Kernel.coe_mk, if_pos hu.2.le]
  exact (Riesz.Analysis.signedDiscrepancyEnergy_sub_toSignedMeasure q L hq hq_two (F u) ν
    (congrArg ENNReal.toReal (hu.2.trans hνmass.symm)) S hS hu.1 hν hdiam).symm

theorem finiteDifferenceDiscrepancy_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d M : ℕ) (q L : ℝ)
    (hq : 0 < q) (hq_two : q < 2)
    (F : Ω → Measure (Rd d)) [∀ u, IsFiniteMeasure (F u)] (hF : Measurable F)
    (ν : Measure (Rd d)) [IsFiniteMeasure ν] (hνmass : ν Set.univ = M)
    (S : Set (Rd d)) (hS : MeasurableSet S) (hν : ν Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L)
    (hspec : ∀ᵐ u ∂P, F u Sᶜ = 0 ∧ F u Set.univ = M) :
    Integrable (fun u => Riesz.Analysis.signedDiscrepancyEnergy q
      ((F u).toSignedMeasure - ν.toSignedMeasure)) P := by
  refine (integrable_const (2 * L ^ q * (M : ℝ) ^ 2 / q)).mono'
    (finiteDifferenceDiscrepancy_aestronglyMeasurable P d M q L hq hq_two F hF ν hνmass
      S hS hν hdiam hspec) ?_
  filter_upwards [hspec] with u hu
  have hb := finiteDifferenceDiscrepancy_bounds d M q L hq hq_two (F u) ν hu.2 hνmass
    S hS hu.1 hν hdiam
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

theorem sampledRoundingDiscrepancy_marks_integrable (d a n k : ℕ) (r q L : ℝ)
    (hr : 0 < r) (hq : 0 < q) (hq_two : q < 2)
    (x : Fin a → Rd d) (hinj : Function.Injective x)
    (hx : ∀ i, x i ∈ cube d ((2 : ℝ) ^ k * r)) (w : Fin a → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (ν : Fin n → FiniteMeasure (Rd d))
    (hν : ∀ i, ν i ≠ 0) (hmass : ∀ i, (ν i).mass ≤ 1) (hatom : ∀ i y, ν i {y} = 0)
    (B : Fin n → Set (Rd d)) (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hB : ∀ i, B i ⊆ cube d ((2 : ℝ) ^ k * r))
    (M : ℕ) (hM : (∑ i, w i) + ∑ i, ((ν i).mass : ℝ) = M)
    (S : Set (Rd d)) (hS : MeasurableSet S)
    (hcube : cube d ((2 : ℝ) ^ k * r) ⊆ S)
    (hdiam : ∀ y ∈ S, ∀ z ∈ S, ‖y - z‖ ≤ L) :
    Integrable (fun p : (Fin n → unitInterval) × (Fin (a + n) → ℝ) =>
      Riesz.Analysis.signedDiscrepancyEnergy q (sampledRoundingDiscrepancy d a n x w ν p.1 p.2))
      (sampledRoundingMarks d a n k r x w ν) := by
  have hspec := sampledRoundingMarks_spec d a n k r hr x hinj hx w hw ν hν hmass hatom
    B hsupport hdisjoint hB M hM
  have hinputmass : samplingRoundingInput d a n x w ν Set.univ = M := by
    rw [← sampledRoundingMarks_full_mean d a n k r x w hw ν hmass Set.univ MeasurableSet.univ]
    rw [lintegral_congr_ae (hspec.mono (fun p hp => hp.1.2))]
    simp
  have hinputsupport : samplingRoundingInput d a n x w ν Sᶜ = 0 := by
    rw [← sampledRoundingMarks_full_mean d a n k r x w hw ν hmass Sᶜ hS.compl]
    simpa only [lintegral_zero] using lintegral_congr_ae (hspec.mono (fun p hp =>
      measure_mono_null (Set.compl_subset_compl.mpr hcube) hp.2))
  letI : ∀ p : (Fin n → unitInterval) × (Fin (a + n) → ℝ),
      IsFiniteMeasure (sampledRoundedMeasure d a n x ν p) := fun p =>
    inferInstanceAs (IsFiniteMeasure (weightedAtomicMeasure d (a + n)
      (sampledAtomicSites d a n x ν p.1) p.2))
  exact finiteDifferenceDiscrepancy_integrable (sampledRoundingMarks d a n k r x w ν)
    d M q L hq hq_two (sampledRoundedMeasure d a n x ν)
    (measurable_sampledRoundedMeasure d a n x ν) (samplingRoundingInput d a n x w ν)
    hinputmass S hS hinputsupport hdiam
    (hspec.mono (fun p hp => ⟨measure_mono_null (Set.compl_subset_compl.mpr hcube) hp.2, hp.1.2⟩))

theorem multiscaleWeightedEnergy_integrable (d n k : ℕ) (masks : RoundingMasks n)
    (q : ℝ) (x : Fin n → Rd d) (hx : Function.Injective x) (w : Fin n → ℝ) :
    Integrable (fun v => Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun i => v i - w i))) (multiscaleRoundingLaw k masks w) := by
  simp_rw [weightedSignedMeasure_energy d n q x hx]
  exact integrable_multiscaleRoundingLaw k masks w _ (measurable_weightQuadratic_diff d n q x w)

/-- The actual composed law obeys the sampling-plus-rounding estimate.
All real integrals are justified by the preceding integrability results. -/
theorem sampledRoundingDiscrepancy_expected_energy_le (d a n k : ℕ) (r q L : ℝ)
    (hr : 0 < r) (hq : 0 < q) (hq_two : q < 2) (hqd : q < (d : ℝ))
    (x : Fin a → Rd d) (hinj : Function.Injective x)
    (hx : ∀ i, x i ∈ cube d ((2 : ℝ) ^ k * r)) (w : Fin a → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (ν : Fin n → FiniteMeasure (Rd d))
    (hν : ∀ i, ν i ≠ 0) (hmass : ∀ i, (ν i).mass ≤ 1) (hatom : ∀ i y, ν i {y} = 0)
    (B : Fin n → Set (Rd d)) (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hB : ∀ i, B i ⊆ cube d ((2 : ℝ) ^ k * r))
    (M : ℕ) (hM : (∑ i, w i) + ∑ i, ((ν i).mass : ℝ) = M)
    (S : Set (Rd d)) (hS : IsCompact S)
    (hcube : cube d ((2 : ℝ) ^ k * r) ⊆ S)
    (hdiam : ∀ y ∈ S, ∀ z ∈ S, ‖y - z‖ ≤ L) :
    (∫ p : (Fin n → unitInterval) × (Fin (a + n) → ℝ),
      Riesz.Analysis.signedDiscrepancyEnergy q
        (sampledRoundingDiscrepancy d a n x w ν p.1 p.2)
      ∂sampledRoundingMarks d a n k r x w ν) ≤
        2 * (∫ u, Riesz.Analysis.signedDiscrepancyEnergy q
          (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u)) ∂uniformCellMarks n) +
        2 * cubeRoundingConstant d q *
          (r ^ q * totalFractionalBudget (sampledAtomicWeights d a n w ν) +
            ((2 : ℝ) ^ k * r) ^ d * r ^ (q - (d : ℝ))) := by
  have htotal := sampledRoundingDiscrepancy_marks_integrable d a n k r q L hr hq hq_two
    x hinj hx w hw ν hν hmass hatom B hsupport hdisjoint hB M hM S hS.measurableSet hcube hdiam
  have houter := htotal.integral_compProd
  have hinner := htotal.ae_of_compProd
  have hcommon (i : Fin n) : (ν i : Measure (Rd d)) Sᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr ((hB i).trans hcube))
      ((FiniteMeasure.null_iff_toMeasure_null _ _).mp (hsupport i))
  have hsample := sampledCellDiscrepancy_marks_integrable d n q L hq.le ν hν hatom S hcommon hdiam
  rw [sampledRoundingMarks, Measure.integral_compProd htotal]
  refine le_trans (b := ∫ u, 2 * Riesz.Analysis.signedDiscrepancyEnergy q
    (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u)) +
      2 * cubeRoundingConstant d q *
        (r ^ q * totalFractionalBudget (sampledAtomicWeights d a n w ν) +
          ((2 : ℝ) ^ k * r) ^ d * r ^ (q - (d : ℝ))) ∂uniformCellMarks n)
    (integral_mono_ae houter ((hsample.const_mul 2).add (integrable_const _)) ?_) ?_
  · filter_upwards [hinner,
      sampledCellSites_append_injective d a n x hinj ν hν hatom B hsupport hdisjoint,
      sampledCellSites_supported d n ν hν B hsupport] with u hi hu hy
    have hround := multiscaleWeightedEnergy_integrable d (a + n) (k + 1)
      (partitionRoundingMasks (dyadicCubeLabels d (a + n) r (sampledAtomicSites d a n x ν u)))
      q (sampledAtomicSites d a n x ν u) hu (sampledAtomicWeights d a n w ν)
    haveI : IsProbabilityMeasure (multiscaleRoundingLaw (k + 1)
        (partitionRoundingMasks (dyadicCubeLabels d (a + n) r (sampledAtomicSites d a n x ν u)))
        (sampledAtomicWeights d a n w ν)) := (multiscaleRoundingLaw_measurable_probability (k + 1)).2 _ _
    have hpoint : ∀ᵐ v ∂sampledDyadicRoundingLaw d a n k r x w ν u,
        Riesz.Analysis.signedDiscrepancyEnergy q (sampledRoundingDiscrepancy d a n x w ν u v) ≤
          2 * Riesz.Analysis.signedDiscrepancyEnergy q
            (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u)) +
          2 * Riesz.Analysis.signedDiscrepancyEnergy q
            (weightedSignedMeasure d (a + n) (sampledAtomicSites d a n x ν u)
              (fun i => v i - sampledAtomicWeights d a n w ν i)) := by
      filter_upwards [multiscaleRoundingLaw_preserves (k + 1)
        (partitionRoundingMasks (dyadicCubeLabels d (a + n) r (sampledAtomicSites d a n x ν u)))
        (sampledAtomicWeights d a n w ν) (sampledAtomicWeights_valid d a n w hw ν hmass)] with v hv
      exact sampledRoundingDiscrepancy_energy_le d a n q hq hq_two x w hw ν hmass hatom u v
        (fun i => (hv.1 i).1) hv.2.1 hu S hS (fun i => hcube (hx i))
        (fun i => hcube (hB i (hy i))) hcommon
    have hb := integral_mono_ae hi
      ((integrable_const (2 * Riesz.Analysis.signedDiscrepancyEnergy q
        (sampledCellDiscrepancy d n ν (sampledCellSites d n ν u)))).add (hround.const_mul 2)) hpoint
    simp only [Kernel.prodMkLeft_apply, sampledDyadicRoundingKernel, Kernel.coe_mk,
      sampledDyadicRoundingLaw, Pi.add_apply, integral_add (integrable_const _) (hround.const_mul 2),
      integral_const_mul, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hb
    have hdya := dyadicCubeRounding_uniform_energy_le d (a + n) k r q hr hq hqd
      (sampledAtomicSites d a n x ν u) hu
      (sampledAtomicSites_mem d a n x ν u _ hx (fun i => hB i (hy i)))
      (sampledAtomicWeights d a n w ν) (sampledAtomicWeights_valid d a n w hw ν hmass)
    simpa only [sampledDyadicRoundingKernel, Kernel.coe_mk, sampledDyadicRoundingLaw, mul_assoc] using hb.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdya (by norm_num : (0 : ℝ) ≤ 2)))
  · simp only [integral_add (hsample.const_mul 2) (integrable_const _), integral_const_mul,
      integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul, le_refl]

theorem sampledAtomicWeights_budget_le (d a n : ℕ) (w : Fin a → ℝ)
    (ν : Fin n → FiniteMeasure (Rd d)) :
    totalFractionalBudget (sampledAtomicWeights d a n w ν) ≤
      totalFractionalBudget w + ∑ i, ((ν i).mass : ℝ) := by
  simp only [totalFractionalBudget, sampledAtomicWeights, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right]
  refine add_le_add le_rfl (Finset.sum_le_sum (fun i _ => ?_))
  dsimp [fractionalBudget]
  nlinarith [sq_nonneg ((ν i).mass : ℝ)]

/-- The continuous-cell version of the cube discretization estimate. The
constant depends only on dimension, exponent and the fixed local diameter. -/
theorem sampledRoundingDiscrepancy_expected_energy_le_mass (d a n k : ℕ) (r q ℓ : ℝ)
    (hr : 1 ≤ r) (hq : 0 < q) (hq_two : q < 2) (hqd : q < (d : ℝ)) (hℓ : 0 ≤ ℓ)
    (x : Fin a → Rd d) (hinj : Function.Injective x)
    (hx : ∀ i, x i ∈ cube d ((2 : ℝ) ^ k * r)) (w : Fin a → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (ν : Fin n → FiniteMeasure (Rd d))
    (hν : ∀ i, ν i ≠ 0) (hmass : ∀ i, (ν i).mass ≤ 1) (hatom : ∀ i y, ν i {y} = 0)
    (B : Fin n → Set (Rd d)) (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hB : ∀ i, B i ⊆ cube d ((2 : ℝ) ^ k * r))
    (hdiam : ∀ i, ∀ y ∈ B i, ∀ z ∈ B i, ‖y - z‖ ≤ ℓ)
    (M : ℕ) (hM : (∑ i, w i) + ∑ i, ((ν i).mass : ℝ) = M) :
    (∫ p : (Fin n → unitInterval) × (Fin (a + n) → ℝ),
      Riesz.Analysis.signedDiscrepancyEnergy q
        (sampledRoundingDiscrepancy d a n x w ν p.1 p.2)
      ∂sampledRoundingMarks d a n k r x w ν) ≤
        (8 * ℓ ^ q / q + 2 * cubeRoundingConstant d q) *
          (r ^ q * (totalFractionalBudget w + ∑ i, ((ν i).mass : ℝ)) +
            ((2 : ℝ) ^ k * r) ^ d * r ^ (q - (d : ℝ))) := by
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp (cube_isBounded d ((2 : ℝ) ^ k * r)).closure
  have hcommonDiam (y : Rd d) (hy : y ∈ closure (cube d ((2 : ℝ) ^ k * r)))
      (z : Rd d) (hz : z ∈ closure (cube d ((2 : ℝ) ^ k * r))) : ‖y - z‖ ≤ L := by
    simpa only [dist_eq_norm] using hL hy hz
  have hbase := sampledRoundingDiscrepancy_expected_energy_le d a n k r q L
    (lt_of_lt_of_le zero_lt_one hr) hq hq_two hqd x hinj hx w hw ν hν hmass hatom
    B hsupport hdisjoint hB M hM _ (cube_isBounded d ((2 : ℝ) ^ k * r)).isCompact_closure
    subset_closure hcommonDiam
  have hcommon (i : Fin n) : (ν i : Measure (Rd d)) (closure (cube d ((2 : ℝ) ^ k * r)))ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr ((hB i).trans subset_closure))
      ((FiniteMeasure.null_iff_toMeasure_null _ _).mp (hsupport i))
  have hsample := sampledCellSites_expected_energy_le_mass d n q L ℓ hq hℓ ν hν hmass hatom
    _ hcommon hcommonDiam B hsupport hdiam
  have hbudget := sampledAtomicWeights_budget_le d a n w ν
  have hwBudget : 0 ≤ totalFractionalBudget w :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).1 (sub_nonneg.mpr (hw i).2))
  have hmass0 : 0 ≤ ∑ i, ((ν i).mass : ℝ) := Finset.sum_nonneg (fun i _ => NNReal.coe_nonneg _)
  have hrpow := Real.one_le_rpow hr hq.le
  have hC := (cubeRoundingConstant_pos d q hq hqd).le
  have hmass_le : (∑ i, ((ν i).mass : ℝ)) ≤
      r ^ q * (totalFractionalBudget w + ∑ i, ((ν i).mass : ℝ)) +
        ((2 : ℝ) ^ k * r) ^ d * r ^ (q - (d : ℝ)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrpow) (add_nonneg hwBudget hmass0),
      (show 0 ≤ ((2 : ℝ) ^ k * r) ^ d * r ^ (q - (d : ℝ)) from by positivity)]
  simp only [div_eq_mul_inv] at hsample ⊢
  nlinarith only [hbase, hsample, mul_le_mul_of_nonneg_left hbudget
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
        (Real.rpow_nonneg (zero_le_one.trans hr) q)),
    mul_le_mul_of_nonneg_left hmass_le
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (Real.rpow_nonneg hℓ q))
        (inv_nonneg.mpr hq.le))]

end Riesz.Negative
