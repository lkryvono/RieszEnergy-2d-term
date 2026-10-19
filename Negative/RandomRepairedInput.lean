import Riesz.Negative.SampledRounding
import Riesz.Negative.DiffuseDecomposition

/-!
Sampling and rounding repaired inputs on a fixed common mark space.
The original finite atom labels are retained, including zero-weight labels.
-/

noncomputable section

open MeasureTheory RieszShowcase ProbabilityTheory
open scoped ENNReal Classical ProbabilityTheory

namespace Riesz.Negative

/-- The mark space depends on the diffuse-cell count, not the original atom count. -/
abbrev RandomRepairedMarks (n : ℕ) := (Fin n → unitInterval) × unitInterval

def randomRepairedInputMarks (n : ℕ) : Measure (RandomRepairedMarks n) :=
  (uniformCellMarks n).prod (volume : Measure unitInterval)

/-- One jointly measurable sampler for the entire finite multiscale law. -/
def sampleMultiscaleRounding {n : ℕ} (k : ℕ) :
    (RoundingMasks n × (Fin n → ℝ)) → unitInterval → (Fin n → ℝ) :=
  Classical.choose (exists_multiscaleRounding_sampler (n := n) k)

/-- The sampled state uses one final uniform mark for all rounding passes. -/
def randomRepairedInputState (d a n k : ℕ) (r : ℝ) (x : Fin a → Rd d)
    (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d))
    (p : RandomRepairedMarks n) : (Fin n → unitInterval) × (Fin (a + n) → ℝ) :=
  (p.1, sampleMultiscaleRounding (k + 1)
    (partitionRoundingMasks (dyadicCubeLabels d (a + n) r
      (sampledAtomicSites d a n x ν p.1)), sampledAtomicWeights d a n w ν) p.2)

/-- The actual counting-measure output, before specializing the repaired input. -/
def randomRepairedInputBranch (d a n k : ℕ) (r : ℝ) (x : Fin a → Rd d)
    (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d))
    (p : RandomRepairedMarks n) : Measure (Rd d) :=
  sampledRoundedMeasure d a n x ν (randomRepairedInputState d a n k r x w ν p)

/-- An independent uniform sampler realizes a composition-product exactly. -/
theorem map_product_sampler_eq_compProd {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsSFiniteKernel κ]
    (f : X → unitInterval → Y) (hf : Measurable (Function.uncurry f))
    (hmap : ∀ x, Measure.map (f x) (volume : Measure unitInterval) = κ x) :
    Measure.map (fun p : X × unitInterval => (p.1, f p.1 p.2))
      (μ.prod (volume : Measure unitInterval)) = μ.compProd κ := by
  ext D hD
  have hF : Measurable (fun p : X × unitInterval => (p.1, f p.1 p.2)) :=
    measurable_fst.prodMk hf
  rw [Measure.map_apply hF hD, Measure.prod_apply (hD.preimage hF), Measure.compProd_apply hD]
  apply lintegral_congr
  intro a
  rw [← hmap a, Measure.map_apply hf.of_uncurry_left (measurable_prodMk_left hD)]
  rfl

theorem sampleMultiscaleRounding_spec {n : ℕ} (k : ℕ) :
    Measurable (Function.uncurry (sampleMultiscaleRounding (n := n) k)) ∧
    ∀ b : RoundingMasks n × (Fin n → ℝ),
      Measure.map (sampleMultiscaleRounding k b) (volume : Measure unitInterval) =
      multiscaleRoundingLaw k b.1 b.2 := by
  exact Classical.choose_spec (exists_multiscaleRounding_sampler (n := n) k)

theorem jointly_measurable_sampledAtomicSites {X : Type*} [MeasurableSpace X]
    (d a n : ℕ) (x : X → Fin a → Rd d) (hx : Measurable x)
    (ν : X → Fin n → FiniteMeasure (Rd d)) (hν : Measurable ν) :
    Measurable (fun p : X × (Fin n → unitInterval) =>
      sampledAtomicSites d a n (x p.1) (ν p.1) p.2) := by
  refine measurable_pi_lambda _ (Fin.addCases ?_ ?_)
  · intro i
    simpa only [sampledAtomicSites, Fin.append_left, Function.comp_def] using
      (((measurable_pi_apply i).comp hx).comp
        (measurable_fst : Measurable (Prod.fst : X × (Fin n → unitInterval) → X)))
  · exact fun i => by simpa only [sampledAtomicSites, Fin.append_right, Function.comp_def] using
      (measurable_pi_apply i).comp (jointly_measurable_sampledCellSites d n ν hν)

theorem jointly_measurable_sampledAtomicWeights {X : Type*} [MeasurableSpace X]
    (d a n : ℕ) (w : X → Fin a → ℝ) (hw : Measurable w)
    (ν : X → Fin n → FiniteMeasure (Rd d)) (hν : Measurable ν) :
    Measurable (fun z => sampledAtomicWeights d a n (w z) (ν z)) := by
  refine measurable_pi_lambda _ (Fin.addCases ?_ ?_)
  · exact fun i => by simpa only [sampledAtomicWeights, Fin.append_left, Function.comp_def] using
      (measurable_pi_apply i).comp hw
  · exact fun i => by simpa only [sampledAtomicWeights, Fin.append_right, Function.comp_def] using
      (Riesz.Configuration.measurable_finiteMeasure_mass.comp
        ((measurable_pi_apply i).comp hν)).coe_nnreal_real

theorem jointly_measurable_randomRepairedInputState {X : Type*} [MeasurableSpace X]
    (d a n k : ℕ) (r : X → ℝ) (hr : Measurable r)
    (x : X → Fin a → Rd d) (hx : Measurable x)
    (w : X → Fin a → ℝ) (hw : Measurable w)
    (ν : X → Fin n → FiniteMeasure (Rd d)) (hν : Measurable ν) :
    Measurable (fun p : X × RandomRepairedMarks n =>
      randomRepairedInputState d a n k (r p.1) (x p.1) (w p.1) (ν p.1) p.2) := by
  have hsites := (jointly_measurable_sampledAtomicSites d a n x hx ν hν).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd) :
      Measurable (fun p : X × RandomRepairedMarks n => (p.1, p.2.1)))
  have hmasks := measurable_partitionRoundingMasks.comp
    ((measurable_dyadicCubeLabels d (a + n)).comp ((hr.comp measurable_fst).prodMk hsites))
  have hweights := (jointly_measurable_sampledAtomicWeights d a n w hw ν hν).comp
    (measurable_fst : Measurable (Prod.fst : X × RandomRepairedMarks n → X))
  have hsample := (sampleMultiscaleRounding_spec (n := a + n) (k + 1)).1.comp
    ((hmasks.prodMk hweights).prodMk (measurable_snd.comp measurable_snd))
  exact (measurable_fst.comp measurable_snd).prodMk hsample

theorem jointly_measurable_randomRepairedInputBranch {X : Type*} [MeasurableSpace X]
    (d a n k : ℕ) (r : X → ℝ) (hr : Measurable r)
    (x : X → Fin a → Rd d) (hx : Measurable x)
    (w : X → Fin a → ℝ) (hw : Measurable w)
    (ν : X → Fin n → FiniteMeasure (Rd d)) (hν : Measurable ν) :
    Measurable (fun p : X × RandomRepairedMarks n =>
      randomRepairedInputBranch d a n k (r p.1) (x p.1) (w p.1) (ν p.1) p.2) := by
  have hsites := (jointly_measurable_sampledAtomicSites d a n x hx ν hν).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd) :
      Measurable (fun p : X × RandomRepairedMarks n => (p.1, p.2.1)))
  have hstate := jointly_measurable_randomRepairedInputState d a n k r hr x hx w hw ν hν
  simpa only [randomRepairedInputBranch, sampledRoundedMeasure, randomRepairedInputState,
    Function.comp_def] using
    ((measurable_weightedAtomicMeasure d (a + n)).comp
      (hsites.prodMk (measurable_snd.comp hstate)))

theorem measurable_randomRepairedInputState (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d)) :
    Measurable (randomRepairedInputState d a n k r x w ν) := by
  exact (jointly_measurable_randomRepairedInputState d a n k
    (fun _ : Unit => r) measurable_const (fun _ : Unit => x) measurable_const
    (fun _ : Unit => w) measurable_const (fun _ : Unit => ν) measurable_const).comp
      (measurable_const.prodMk measurable_id :
        Measurable (fun p : RandomRepairedMarks n => ((), p)))

theorem measurable_randomRepairedInputBranch (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d)) :
    Measurable (randomRepairedInputBranch d a n k r x w ν) := by
  exact (measurable_sampledRoundedMeasure d a n x ν).comp
    (measurable_randomRepairedInputState d a n k r x w ν)

/-- The fixed marks realize the same joint sampling/rounding law as the kernels. -/
theorem randomRepairedInputState_map (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d)) :
    Measure.map (randomRepairedInputState d a n k r x w ν) (randomRepairedInputMarks n) =
      sampledRoundingMarks d a n k r x w ν := by
  refine map_product_sampler_eq_compProd (uniformCellMarks n)
    (sampledDyadicRoundingKernel d a n k r x w ν)
    (fun u t => sampleMultiscaleRounding (k + 1)
      (partitionRoundingMasks (dyadicCubeLabels d (a + n) r
        (sampledAtomicSites d a n x ν u)), sampledAtomicWeights d a n w ν) t) ?_ ?_
  · exact measurable_snd.comp (measurable_randomRepairedInputState d a n k r x w ν)
  · exact fun u => (sampleMultiscaleRounding_spec (n := a + n) (k + 1)).2
      (partitionRoundingMasks (dyadicCubeLabels d (a + n) r (sampledAtomicSites d a n x ν u)),
        sampledAtomicWeights d a n w ν)

/-- The actual branch realizes the previously verified rounded configuration law. -/
theorem randomRepairedInputBranch_map (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : Fin n → FiniteMeasure (Rd d)) :
    Measure.map (randomRepairedInputBranch d a n k r x w ν) (randomRepairedInputMarks n) =
      sampledRoundedLaw d a n k r x w ν := by
  rw [sampledRoundedLaw, ← randomRepairedInputState_map d a n k r x w ν,
    Measure.map_map (measurable_sampledRoundedMeasure d a n x ν)
      (measurable_randomRepairedInputState d a n k r x w ν)]
  rfl

instance randomRepairedInputMarks_probability (n : ℕ) :
    IsProbabilityMeasure (randomRepairedInputMarks n) :=
  inferInstanceAs (IsProbabilityMeasure ((uniformCellMarks n).prod (volume : Measure unitInterval)))

/-- Full input mean, transferred through the exact branch law. -/
theorem randomRepairedInputBranch_full_mean (d a n k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (ν : Fin n → FiniteMeasure (Rd d)) (hmass : ∀ i, (ν i).mass ≤ 1)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ p, randomRepairedInputBranch d a n k r x w ν p D ∂randomRepairedInputMarks n) =
      samplingRoundingInput d a n x w ν D := by
  rw [← lintegral_map (Measure.measurable_coe hD)
    (measurable_randomRepairedInputBranch d a n k r x w ν),
    randomRepairedInputBranch_map]
  exact sampledRoundedLaw_full_mean d a n k r x w hw ν hmass D hD

/-- Exact count, simplicity and support on the fixed common mark space. -/
theorem randomRepairedInputBranch_spec (d a n k : ℕ) (r : ℝ) (hr : 0 < r)
    (x : Fin a → Rd d) (hinj : Function.Injective x)
    (hx : ∀ i, x i ∈ cube d ((2 : ℝ) ^ k * r)) (w : Fin a → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (ν : Fin n → FiniteMeasure (Rd d))
    (hν : ∀ i, ν i ≠ 0) (hmass : ∀ i, (ν i).mass ≤ 1) (hatom : ∀ i y, ν i {y} = 0)
    (B : Fin n → Set (Rd d)) (hsupport : ∀ i, ν i (B i)ᶜ = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hB : ∀ i, B i ⊆ cube d ((2 : ℝ) ^ k * r))
    (M : ℕ) (hM : (∑ i, w i) + ∑ i, ((ν i).mass : ℝ) = M) :
    ∀ᵐ p ∂randomRepairedInputMarks n,
      (IsSimpleConfiguration d (randomRepairedInputBranch d a n k r x w ν p) ∧
        randomRepairedInputBranch d a n k r x w ν p Set.univ = (M : ℝ≥0∞)) ∧
      randomRepairedInputBranch d a n k r x w ν p (cube d ((2 : ℝ) ^ k * r))ᶜ = 0 := by
  have hspec := sampledRoundingMarks_spec d a n k r hr x hinj hx w hw ν hν hmass hatom
    B hsupport hdisjoint hB M hM
  rw [← randomRepairedInputState_map d a n k r x w ν] at hspec
  exact ae_of_ae_map (measurable_randomRepairedInputState d a n k r x w ν).aemeasurable hspec

/-- The repaired diffuse input is sampled on the fixed half-unit partition. -/
def randomRepairedHalfUnitBranch (d a m k : ℕ) (r : ℝ) (x : Fin a → Rd d)
    (w : Fin a → ℝ) (ν : FiniteMeasure (Rd d))
    (p : RandomRepairedMarks (halfUnitDiffuseCount d m)) : Measure (Rd d) :=
  randomRepairedInputBranch d a (halfUnitDiffuseCount d m) k r x w
    (halfUnitDiffuseMeasures d m ν) p

theorem jointly_measurable_randomRepairedHalfUnitBranch {X : Type*} [MeasurableSpace X]
    (d a m k : ℕ) (r : X → ℝ) (hr : Measurable r)
    (x : X → Fin a → Rd d) (hx : Measurable x)
    (w : X → Fin a → ℝ) (hw : Measurable w)
    (ν : X → FiniteMeasure (Rd d)) (hν : Measurable ν) :
    Measurable (fun p : X × RandomRepairedMarks (halfUnitDiffuseCount d m) =>
      randomRepairedHalfUnitBranch d a m k (r p.1) (x p.1) (w p.1) (ν p.1) p.2) := by
  exact jointly_measurable_randomRepairedInputBranch d a (halfUnitDiffuseCount d m) k
    r hr x hx w hw (fun z => halfUnitDiffuseMeasures d m (ν z))
    ((measurable_halfUnitDiffuseMeasures d m).comp hν)

theorem randomRepairedHalfUnitBranch_map (d a m k : ℕ) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (ν : FiniteMeasure (Rd d)) :
    Measure.map (randomRepairedHalfUnitBranch d a m k r x w ν)
      (randomRepairedInputMarks (halfUnitDiffuseCount d m)) =
      sampledRoundedLaw d a (halfUnitDiffuseCount d m) k r x w
        (halfUnitDiffuseMeasures d m ν) := by
  exact randomRepairedInputBranch_map d a (halfUnitDiffuseCount d m) k r x w
    (halfUnitDiffuseMeasures d m ν)

theorem randomRepairedHalfUnitBranch_full_mean (d a m k : ℕ) (hd : 2 ≤ d) (r : ℝ)
    (x : Fin a → Rd d) (w : Fin a → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (ν : FiniteMeasure (Rd d))
    (hup : (ν : Measure (Rd d)) ≤ (2 : ℝ≥0∞) • volume.restrict (cube d (m : ℝ)))
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ p, randomRepairedHalfUnitBranch d a m k r x w ν p D
      ∂randomRepairedInputMarks (halfUnitDiffuseCount d m)) =
      (weightedAtomicMeasure d a x w + (ν : Measure (Rd d))) D := by
  have hmass : ∀ i, (halfUnitDiffuseMeasures d m ν i).mass ≤ 1 :=
    fun i => halfUnitDiffusePieces_mass_le_one d m hd ν hup _
  unfold randomRepairedHalfUnitBranch
  rw [randomRepairedInputBranch_full_mean d a (halfUnitDiffuseCount d m) k r x w hw
    (halfUnitDiffuseMeasures d m ν) hmass D hD,
    samplingRoundingInput, halfUnitDiffuseMeasures_sum d m ν hup]

/-- Half-unit sampling produces a simple exact-size configuration in the repaired cube. -/
theorem randomRepairedHalfUnitBranch_spec (d a m k : ℕ) (hd : 2 ≤ d)
    (r : ℝ) (hr : 0 < r) (hsize : (m : ℝ) = (2 : ℝ) ^ k * r)
    (x : Fin a → Rd d) (hinj : Function.Injective x)
    (hx : ∀ i, x i ∈ cube d (m : ℝ)) (w : Fin a → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (ν : FiniteMeasure (Rd d))
    (c : ℝ≥0∞) (hc : 0 < c)
    (hlo : c • volume.restrict (cube d (m : ℝ)) ≤ (ν : Measure (Rd d)))
    (hup : (ν : Measure (Rd d)) ≤ (2 : ℝ≥0∞) • volume.restrict (cube d (m : ℝ)))
    (M : ℕ) (hM : (∑ i, w i) + (ν.mass : ℝ) = M) :
    ∀ᵐ p ∂randomRepairedInputMarks (halfUnitDiffuseCount d m),
      (IsSimpleConfiguration d (randomRepairedHalfUnitBranch d a m k r x w ν p) ∧
        randomRepairedHalfUnitBranch d a m k r x w ν p Set.univ = (M : ℝ≥0∞)) ∧
      randomRepairedHalfUnitBranch d a m k r x w ν p (cube d (m : ℝ))ᶜ = 0 := by
  have hinputs := halfUnitDiffuseMeasures_sampling_inputs d m hd ν c hc hlo hup
  have hmass : (∑ i, w i) + ∑ i, ((halfUnitDiffuseMeasures d m ν i).mass : ℝ) = M := by
    simpa only [halfUnitDiffuseMeasures_mass_sum d m ν hup] using hM
  have hx' : ∀ i, x i ∈ cube d ((2 : ℝ) ^ k * r) := by simpa only [← hsize] using hx
  have hB : ∀ i, halfUnitDiffuseRegions d m i ⊆ cube d ((2 : ℝ) ^ k * r) := by
    simpa only [← hsize] using hinputs.2.2.2.2.2.1
  simpa only [randomRepairedHalfUnitBranch, ← hsize] using
    (randomRepairedInputBranch_spec d a (halfUnitDiffuseCount d m) k r hr x hinj hx' w hw
      (halfUnitDiffuseMeasures d m ν) hinputs.1 hinputs.2.1 hinputs.2.2.1
      (halfUnitDiffuseRegions d m) hinputs.2.2.2.1 hinputs.2.2.2.2.1 hB M hmass)

end Riesz.Negative
