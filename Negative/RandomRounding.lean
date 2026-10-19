import Riesz.Negative.FiniteRounding

/-!
The finite random iteration of the two-weight replacement.  We use an explicit
binary law at each node, so the choice of the next fractional pair does not
require a measurable Markov kernel on the full weight space.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

private def quadraticRaw {n : ℕ} (K : Fin n → Fin n → ℝ)
    (u : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * u j * K i j

private theorem quadraticRaw_two_branch {n : ℕ} (K : Fin n → Fin n → ℝ)
    (u δ : Fin n → ℝ) (a b p r : ℝ)
    (hprob : p + r = 1) (hmean : p * a - r * b = 0) :
    p * quadraticRaw K (fun i => u i + a * δ i) +
      r * quadraticRaw K (fun i => u i - b * δ i) =
        quadraticRaw K u + (p * a ^ 2 + r * b ^ 2) * quadraticRaw K δ := by
  have hterm (i j : Fin n) :
      p * ((u i + a * δ i) * (u j + a * δ j) * K i j) +
        r * ((u i - b * δ i) * (u j - b * δ j) * K i j) =
          u i * u j * K i j +
            (p * a ^ 2 + r * b ^ 2) * (δ i * δ j * K i j) := by
    linear_combination (u i * u j * K i j) * hprob +
      ((u i * δ j + δ i * u j) * K i j) * hmean
  unfold quadraticRaw
  simp only [Finset.mul_sum]
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (p * ((u i + a * δ i) * (u j + a * δ j) * K i j) +
          r * ((u i - b * δ i) * (u j - b * δ j) * K i j)) := by
            simp only [Finset.sum_add_distrib]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (u i * u j * K i j +
          (p * a ^ 2 + r * b ^ 2) * (δ i * δ j * K i j)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact hterm i j
    _ = _ := by simp only [Finset.sum_add_distrib]

private def transferDirection {n : ℕ} (i j : Fin n) : Fin n → ℝ :=
  fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)

private theorem transferWeights_affine {n : ℕ} (w : Fin n → ℝ)
    (i j k : Fin n) (t : ℝ) :
    transferWeights w i j t k = w k + t * transferDirection i j k := by
  unfold transferWeights transferDirection
  split_ifs <;> ring

private theorem weightQuadratic_two_branch {n d : ℕ} (q : ℝ)
    (x : Fin n → Rd d) (w z : Fin n → ℝ) (i j : Fin n)
    (a b p r : ℝ) (hprob : p + r = 1) (hmean : p * a - r * b = 0) :
    p * weightQuadratic d n q x
        (fun k => transferWeights w i j a k - z k) +
      r * weightQuadratic d n q x
        (fun k => transferWeights w i j (-b) k - z k) =
        weightQuadratic d n q x (fun k => w k - z k) +
          (p * a ^ 2 + r * b ^ 2) *
            weightQuadratic d n q x (transferDirection i j) := by
  let K : Fin n → Fin n → ℝ := fun k l => -1 / q * ‖x k - x l‖ ^ q
  have hraw (u : Fin n → ℝ) :
      weightQuadratic d n q x u = quadraticRaw K u := by
    simp only [weightQuadratic, quadraticRaw, K, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hraw, transferWeights_affine]
  have hup : (fun k => w k + a * transferDirection i j k - z k) =
      (fun k => (w k - z k) + a * transferDirection i j k) := by
    funext k
    ring
  have hdown : (fun k => w k + -b * transferDirection i j k - z k) =
      (fun k => (w k - z k) - b * transferDirection i j k) := by
    funext k
    ring
  rw [hup, hdown]
  exact quadraticRaw_two_branch K (fun k => w k - z k)
    (transferDirection i j) a b p r hprob hmean

/-- The energy of a two-point transfer relative to an earlier baseline includes
exactly the fresh increment's mean energy; all mixed terms cancel. -/
theorem transferWeightsLaw_expected_shifted_energy (d n : ℕ) (q : ℝ)
    (x : Fin n → Rd d) (hx : Function.Injective x)
    (w z : Fin n → ℝ) (i j : Fin n) (_hij : i ≠ j)
    (hi : 0 < w i) (hi_one : w i < 1)
    (hj : 0 < w j) (hj_one : w j < 1) :
    (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
        (weightedSignedMeasure d n x (fun k => v k - z k))
        ∂transferWeightsLaw w i j) =
      Riesz.Analysis.signedDiscrepancyEnergy q
        (weightedSignedMeasure d n x (fun k => w k - z k)) +
      (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
        (weightedSignedMeasure d n x (fun k => v k - w k))
        ∂transferWeightsLaw w i j) := by
  let a := roundingUp (w i) (w j)
  let b := roundingDown (w i) (w j)
  let p := b / (a + b)
  let r := a / (a + b)
  have hab : a + b ≠ 0 :=
    (add_pos (roundingSteps_pos (w i) (w j) hi hi_one hj hj_one).1
      (roundingSteps_pos (w i) (w j) hi hi_one hj hj_one).2).ne'
  have hprob : p + r = 1 := by
    dsimp [p, r]
    field_simp [hab]
    ring
  have hmean : p * a - r * b = 0 := by
    dsimp [p, r]
    ring
  simp_rw [weightedSignedMeasure_energy d n q x hx]
  rw [transferWeightsLaw]
  rw [integral_map (measurable_transferWeights w i j).aemeasurable
    (measurable_weightQuadratic_diff d n q x z).aestronglyMeasurable]
  rw [integral_twoWeightTransferLaw (w i) (w j) hi hi_one hj hj_one]
  rw [integral_map (measurable_transferWeights w i j).aemeasurable
    (measurable_weightQuadratic_diff d n q x w).aestronglyMeasurable]
  rw [integral_twoWeightTransferLaw (w i) (w j) hi hi_one hj hj_one]
  change p * weightQuadratic d n q x
      (fun k => transferWeights w i j a k - z k) +
      r * weightQuadratic d n q x
        (fun k => transferWeights w i j (-b) k - z k) =
        weightQuadratic d n q x (fun k => w k - z k) +
          (p * weightQuadratic d n q x
              (fun k => transferWeights w i j a k - w k) +
            r * weightQuadratic d n q x
              (fun k => transferWeights w i j (-b) k - w k))
  rw [weightQuadratic_two_branch q x w z i j a b p r hprob hmean,
    weightQuadratic_two_branch q x w w i j a b p r hprob hmean]
  have hzero : weightQuadratic d n q x (fun k => w k - w k) = 0 := by
    simp [weightQuadratic]
  rw [hzero]
  ring

private theorem exists_fractional_pair {n : ℕ} (w : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card) :
    ∃ pair : Fin n × Fin n,
      pair.1 ≠ pair.2 ∧ 0 < w pair.1 ∧ w pair.1 < 1 ∧
        0 < w pair.2 ∧ w pair.2 < 1 := by
  obtain ⟨i, j, hij, hi, hi_one, hj, hj_one⟩ := exists_two_fractional w h
  exact ⟨(i, j), hij, hi, hi_one, hj, hj_one⟩

private def chosenPair {n : ℕ} (w : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card) : Fin n × Fin n :=
  Classical.choose (exists_fractional_pair w h)

private theorem chosenPair_spec {n : ℕ} (w : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card) :
    (chosenPair w h).1 ≠ (chosenPair w h).2 ∧
      0 < w (chosenPair w h).1 ∧ w (chosenPair w h).1 < 1 ∧
      0 < w (chosenPair w h).2 ∧ w (chosenPair w h).2 < 1 :=
  Classical.choose_spec (exists_fractional_pair w h)

private def chosenUp {n : ℕ} (w : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card) : Fin n → ℝ :=
  let pair := chosenPair w h
  transferWeights w pair.1 pair.2 (roundingUp (w pair.1) (w pair.2))

private def chosenDown {n : ℕ} (w : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card) : Fin n → ℝ :=
  let pair := chosenPair w h
  transferWeights w pair.1 pair.2 (-roundingDown (w pair.1) (w pair.2))

private def chosenProbUp {n : ℕ} (w : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card) : ℝ :=
  let pair := chosenPair w h
  roundingDown (w pair.1) (w pair.2) /
    (roundingUp (w pair.1) (w pair.2) + roundingDown (w pair.1) (w pair.2))

private def chosenProbDown {n : ℕ} (w : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card) : ℝ :=
  let pair := chosenPair w h
  roundingUp (w pair.1) (w pair.2) /
    (roundingUp (w pair.1) (w pair.2) + roundingDown (w pair.1) (w pair.2))

private theorem chosenProb_nonneg_sum {n : ℕ} (w : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card) :
    0 ≤ chosenProbUp w h ∧ 0 ≤ chosenProbDown w h ∧
      chosenProbUp w h + chosenProbDown w h = 1 := by
  obtain ⟨_, hi, hi_one, hj, hj_one⟩ := chosenPair_spec w h
  have ha := (roundingSteps_pos (w (chosenPair w h).1)
    (w (chosenPair w h).2) hi hi_one hj hj_one).1
  have hb := (roundingSteps_pos (w (chosenPair w h).1)
    (w (chosenPair w h).2) hi hi_one hj hj_one).2
  dsimp [chosenProbUp, chosenProbDown]
  constructor
  · positivity
  constructor
  · positivity
  · field_simp [(add_pos ha hb).ne']
    ring

/-- A finite binary tree of mean-preserving rounding choices, truncated after
`fuel` replacements.  At each node the next pair is chosen from the current
fractional sites. -/
def randomRoundingLaw {n : ℕ} : ℕ → (Fin n → ℝ) → Measure (Fin n → ℝ)
  | 0, w => Measure.dirac w
  | fuel + 1, w =>
      if h : 1 < (fractionalSites w).card then
        ENNReal.ofReal (chosenProbUp w h) • randomRoundingLaw fuel (chosenUp w h) +
          ENNReal.ofReal (chosenProbDown w h) • randomRoundingLaw fuel (chosenDown w h)
      else Measure.dirac w

theorem integrable_randomRoundingLaw {n : ℕ} (fuel : ℕ)
    (w : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) :
    Integrable f (randomRoundingLaw fuel w) := by
  induction fuel generalizing w with
  | zero => simpa [randomRoundingLaw] using (integrable_dirac (by simp) :
      Integrable f (Measure.dirac w))
  | succ fuel ih =>
      rw [randomRoundingLaw]
      split_ifs with h
      · exact integrable_add_measure.mpr
          ⟨(ih (chosenUp w h)).smul_measure ENNReal.ofReal_ne_top,
            (ih (chosenDown w h)).smul_measure ENNReal.ofReal_ne_top⟩
      · simpa using (integrable_dirac (by simp) : Integrable f (Measure.dirac w))

theorem randomRoundingLaw_isProbability {n : ℕ} (fuel : ℕ)
    (w : Fin n → ℝ) : IsProbabilityMeasure (randomRoundingLaw fuel w) := by
  induction fuel generalizing w with
  | zero =>
      simp only [randomRoundingLaw]
      infer_instance
  | succ fuel ih =>
      rw [randomRoundingLaw]
      split_ifs with h
      · have hp := chosenProb_nonneg_sum w h
        refine ⟨?_⟩
        simp only [Measure.add_apply, Measure.smul_apply, measure_univ,
          smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_add hp.1 hp.2.1, hp.2.2, ENNReal.ofReal_one]
      · infer_instance

private theorem integral_randomRoundingLaw_succ {n : ℕ} (fuel : ℕ)
    (w : Fin n → ℝ) (h : 1 < (fractionalSites w).card)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ v, f v ∂randomRoundingLaw (fuel + 1) w) =
      chosenProbUp w h * (∫ v, f v ∂randomRoundingLaw fuel (chosenUp w h)) +
        chosenProbDown w h * (∫ v, f v ∂randomRoundingLaw fuel (chosenDown w h)) := by
  rw [randomRoundingLaw, dif_pos h]
  rw [integral_add_measure
      ((integrable_randomRoundingLaw fuel (chosenUp w h) f).smul_measure
        ENNReal.ofReal_ne_top)
      ((integrable_randomRoundingLaw fuel (chosenDown w h) f).smul_measure
        ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (chosenProb_nonneg_sum w h).1,
    ENNReal.toReal_ofReal (chosenProb_nonneg_sum w h).2.1]
  simp only [smul_eq_mul]

private theorem chosen_weight_mean {n : ℕ} (w : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card) (k : Fin n) :
    chosenProbUp w h * chosenUp w h k +
      chosenProbDown w h * chosenDown w h k = w k := by
  have hprob := (chosenProb_nonneg_sum w h).2.2
  let pair := chosenPair w h
  let a := roundingUp (w pair.1) (w pair.2)
  let b := roundingDown (w pair.1) (w pair.2)
  have hmean : chosenProbUp w h * a - chosenProbDown w h * b = 0 := by
    dsimp [chosenProbUp, chosenProbDown, a, b, pair]
    ring
  change chosenProbUp w h * transferWeights w pair.1 pair.2 a k +
    chosenProbDown w h * transferWeights w pair.1 pair.2 (-b) k = w k
  rw [transferWeights_affine, transferWeights_affine]
  linear_combination (w k) * hprob + (transferDirection pair.1 pair.2 k) * hmean

/-- Every coordinate has the exact initial mean after any finite number of
adapted rounding decisions. -/
theorem randomRoundingLaw_coordinate_mean {n : ℕ} (fuel : ℕ)
    (w : Fin n → ℝ) (k : Fin n) :
    (∫ v, v k ∂randomRoundingLaw fuel w) = w k := by
  induction fuel generalizing w with
  | zero => simp [randomRoundingLaw]
  | succ fuel ih =>
      by_cases h : 1 < (fractionalSites w).card
      · rw [integral_randomRoundingLaw_succ fuel w h, ih, ih]
        exact chosen_weight_mean w h k
      · simp [randomRoundingLaw, h]

/-- The binary tree terminates when its fuel bounds the number of fractional
coordinates. Every supported leaf preserves the original sum and integral
coordinates. -/
theorem randomRoundingLaw_final {n : ℕ} (fuel : ℕ)
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (hcard : (fractionalSites w).card ≤ fuel + 1) :
    ∀ᵐ v ∂randomRoundingLaw fuel w,
      (∀ k, 0 ≤ v k ∧ v k ≤ 1) ∧
        (∑ k, v k = ∑ k, w k) ∧
        (fractionalSites v).card ≤ 1 ∧
        (∀ k, w k = 0 ∨ w k = 1 → v k = w k) := by
  induction fuel generalizing w with
  | zero =>
      simp only [randomRoundingLaw, ae_dirac_eq, Filter.eventually_pure]
      exact ⟨hw, trivial, by simpa using hcard, fun _ _ => trivial⟩
  | succ fuel ih =>
      by_cases h : 1 < (fractionalSites w).card
      · let pair := chosenPair w h
        obtain ⟨hij, hi, hi_one, hj, hj_one⟩ := chosenPair_spec w h
        have hup := transferWeights_outcome w pair.1 pair.2 hij hw
          hi hi_one hj hj_one (roundingUp (w pair.1) (w pair.2)) (Or.inl rfl)
        have hdown := transferWeights_outcome w pair.1 pair.2 hij hw
          hi hi_one hj hj_one (-roundingDown (w pair.1) (w pair.2)) (Or.inr rfl)
        change (∀ k, 0 ≤ chosenUp w h k ∧ chosenUp w h k ≤ 1) ∧
            (∑ k, chosenUp w h k = ∑ k, w k) ∧
            (fractionalSites (chosenUp w h)).card < (fractionalSites w).card ∧
            (∀ k, w k = 0 ∨ w k = 1 → chosenUp w h k = w k) at hup
        change (∀ k, 0 ≤ chosenDown w h k ∧ chosenDown w h k ≤ 1) ∧
            (∑ k, chosenDown w h k = ∑ k, w k) ∧
            (fractionalSites (chosenDown w h)).card < (fractionalSites w).card ∧
            (∀ k, w k = 0 ∨ w k = 1 → chosenDown w h k = w k) at hdown
        have hbranch (u : Fin n → ℝ)
            (hu : (∀ k, 0 ≤ u k ∧ u k ≤ 1) ∧
              (∑ k, u k = ∑ k, w k) ∧
              (fractionalSites u).card < (fractionalSites w).card ∧
              (∀ k, w k = 0 ∨ w k = 1 → u k = w k)) :
            ∀ᵐ v ∂randomRoundingLaw fuel u,
              (∀ k, 0 ≤ v k ∧ v k ≤ 1) ∧
                (∑ k, v k = ∑ k, w k) ∧
                (fractionalSites v).card ≤ 1 ∧
                (∀ k, w k = 0 ∨ w k = 1 → v k = w k) := by
          have hcard_u : (fractionalSites u).card ≤ fuel + 1 := by omega
          apply (ih u hu.1 hcard_u).mono
          intro v hv
          refine ⟨hv.1, hv.2.1.trans hu.2.1, hv.2.2.1, ?_⟩
          intro k hk
          have huk : u k = w k := hu.2.2.2 k hk
          have hk_u : u k = 0 ∨ u k = 1 := by rw [huk]; exact hk
          rw [hv.2.2.2 k hk_u, huk]
        rw [randomRoundingLaw, dif_pos h]
        exact ae_add_measure_iff.mpr
          ⟨Measure.ae_smul_measure (hbranch (chosenUp w h) hup) _,
            Measure.ae_smul_measure (hbranch (chosenDown w h) hdown) _⟩
      · simp only [randomRoundingLaw, dif_neg h, ae_dirac_eq, Filter.eventually_pure]
        exact ⟨hw, trivial, le_of_not_gt h, fun _ _ => trivial⟩

private theorem integral_chosenTransfer {n : ℕ} (w : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    (∫ v, f v ∂transferWeightsLaw w (chosenPair w h).1 (chosenPair w h).2) =
      chosenProbUp w h * f (chosenUp w h) +
        chosenProbDown w h * f (chosenDown w h) := by
  obtain ⟨_, hi, hi_one, hj, hj_one⟩ := chosenPair_spec w h
  rw [transferWeightsLaw,
    integral_map (measurable_transferWeights w (chosenPair w h).1
      (chosenPair w h).2).aemeasurable hf.aestronglyMeasurable]
  rw [integral_twoWeightTransferLaw (w (chosenPair w h).1)
    (w (chosenPair w h).2) hi hi_one hj hj_one]
  rfl

private theorem chosen_step_energy_budget {n d : ℕ} (q D : ℝ)
    (hq : 0 < q) (x : Fin n → Rd d) (hx : Function.Injective x)
    (hdiam : ∀ i j, ‖x i - x j‖ ≤ D) (w z : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card) :
    chosenProbUp w h * weightQuadratic d n q x
        (fun k => chosenUp w h k - z k) +
      chosenProbDown w h * weightQuadratic d n q x
        (fun k => chosenDown w h k - z k) ≤
      weightQuadratic d n q x (fun k => w k - z k) +
        D ^ q / q * (totalFractionalBudget w -
          (chosenProbUp w h * totalFractionalBudget (chosenUp w h) +
            chosenProbDown w h * totalFractionalBudget (chosenDown w h))) := by
  let pair := chosenPair w h
  obtain ⟨hij, hi, hi_one, hj, hj_one⟩ := chosenPair_spec w h
  have hshift := transferWeightsLaw_expected_shifted_energy d n q x hx w z
    pair.1 pair.2 hij hi hi_one hj hj_one
  simp_rw [weightedSignedMeasure_energy d n q x hx] at hshift
  rw [integral_chosenTransfer w h
      (fun v => weightQuadratic d n q x (fun k => v k - z k))
      (measurable_weightQuadratic_diff d n q x z),
    integral_chosenTransfer w h
      (fun v => weightQuadratic d n q x (fun k => v k - w k))
      (measurable_weightQuadratic_diff d n q x w)] at hshift
  have hcost := transferWeightsLaw_energy_budget_bound d n q D hq x hx w
    pair.1 pair.2 hij hi hi_one hj hj_one (hdiam pair.1 pair.2)
  simp_rw [weightedSignedMeasure_energy d n q x hx] at hcost
  rw [integral_chosenTransfer w h
      (fun v => weightQuadratic d n q x (fun k => v k - w k))
      (measurable_weightQuadratic_diff d n q x w),
    integral_chosenTransfer w h totalFractionalBudget measurable_totalFractionalBudget]
    at hcost
  linarith

/-- Telescoping the finite binary tree controls energy relative to *any*
earlier baseline. This stronger form carries the cross-term cancellation
through each recursive branch. -/
theorem randomRoundingLaw_shifted_energy_budget {n d : ℕ} (fuel : ℕ)
    (q D : ℝ) (hq : 0 < q)
    (x : Fin n → Rd d) (hx : Function.Injective x)
    (hdiam : ∀ i j, ‖x i - x j‖ ≤ D)
    (w z : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) :
    (∫ v, weightQuadratic d n q x (fun k => v k - z k)
      ∂randomRoundingLaw fuel w) ≤
        weightQuadratic d n q x (fun k => w k - z k) +
          D ^ q / q * (totalFractionalBudget w -
            ∫ v, totalFractionalBudget v ∂randomRoundingLaw fuel w) := by
  induction fuel generalizing w with
  | zero => simp [randomRoundingLaw]
  | succ fuel ih =>
      by_cases h : 1 < (fractionalSites w).card
      · let pair := chosenPair w h
        obtain ⟨hij, hi, hi_one, hj, hj_one⟩ := chosenPair_spec w h
        have hup : ∀ k, 0 ≤ chosenUp w h k ∧ chosenUp w h k ≤ 1 := by
          exact (transferWeights_valid w pair.1 pair.2 hij hw
            (roundingUp (w pair.1) (w pair.2)) (Or.inl rfl)).1
        have hdown : ∀ k, 0 ≤ chosenDown w h k ∧ chosenDown w h k ≤ 1 := by
          exact (transferWeights_valid w pair.1 pair.2 hij hw
            (-roundingDown (w pair.1) (w pair.2)) (Or.inr rfl)).1
        have hih_up := ih (chosenUp w h) hup
        have hih_down := ih (chosenDown w h) hdown
        have hstep := chosen_step_energy_budget q D hq x hx hdiam w z h
        have hp := (chosenProb_nonneg_sum w h).1
        have hr := (chosenProb_nonneg_sum w h).2.1
        rw [integral_randomRoundingLaw_succ fuel w h
          (fun v => weightQuadratic d n q x (fun k => v k - z k)),
          integral_randomRoundingLaw_succ fuel w h totalFractionalBudget]
        calc
          chosenProbUp w h *
              (∫ v, weightQuadratic d n q x (fun k => v k - z k)
                ∂randomRoundingLaw fuel (chosenUp w h)) +
              chosenProbDown w h *
                (∫ v, weightQuadratic d n q x (fun k => v k - z k)
                  ∂randomRoundingLaw fuel (chosenDown w h))
              ≤ chosenProbUp w h *
                  (weightQuadratic d n q x (fun k => chosenUp w h k - z k) +
                    D ^ q / q * (totalFractionalBudget (chosenUp w h) -
                      ∫ v, totalFractionalBudget v
                        ∂randomRoundingLaw fuel (chosenUp w h))) +
                  chosenProbDown w h *
                    (weightQuadratic d n q x (fun k => chosenDown w h k - z k) +
                      D ^ q / q * (totalFractionalBudget (chosenDown w h) -
                        ∫ v, totalFractionalBudget v
                          ∂randomRoundingLaw fuel (chosenDown w h))) := by
                    exact add_le_add (mul_le_mul_of_nonneg_left hih_up hp)
                      (mul_le_mul_of_nonneg_left hih_down hr)
          _ ≤ _ := by nlinarith [hstep]
      · simp [randomRoundingLaw, h]

private theorem totalFractionalBudget_nonneg {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) : 0 ≤ totalFractionalBudget w := by
  unfold totalFractionalBudget
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hw k).1 (sub_nonneg.mpr (hw k).2)

/-- The full finite rounding budget from the paper, for a list of distinct
sites. Taking `fuel = n` leaves at most one fractional coordinate almost surely.
The bound is on the actual signed discrepancy energy of the final weights. -/
theorem randomRoundingLaw_expected_energy_le {n d : ℕ}
    (q D : ℝ) (hq : 0 < q) (hD : 0 ≤ D)
    (x : Fin n → Rd d) (hx : Function.Injective x)
    (hdiam : ∀ i j, ‖x i - x j‖ ≤ D)
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) :
    (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun k => v k - w k))
      ∂randomRoundingLaw n w) ≤
        D ^ q / q * totalFractionalBudget w := by
  have hcard : (fractionalSites w).card ≤ n + 1 := by
    have hle := (fractionalSites w).card_le_univ
    simp only [Fintype.card_fin] at hle
    omega
  have hfinal := randomRoundingLaw_final n w hw hcard
  have hbudget : 0 ≤ ∫ v, totalFractionalBudget v ∂randomRoundingLaw n w := by
    apply integral_nonneg_of_ae
    apply hfinal.mono
    intro v hv
    exact totalFractionalBudget_nonneg v hv.1
  have hcore := randomRoundingLaw_shifted_energy_budget n q D hq x hx hdiam w w hw
  simp_rw [weightedSignedMeasure_energy d n q x hx]
  have hzero : weightQuadratic d n q x (fun k => w k - w k) = 0 := by
    simp [weightQuadratic]
  rw [hzero] at hcore
  have hcoeff : 0 ≤ D ^ q / q := by
    exact div_nonneg (Real.rpow_nonneg hD q) hq.le
  nlinarith

/-- The finite rounding law preserves the mean of every scalar test sum on
the original sites. This is the finite-atomic mean identity used when the
rounding law is applied to a random measure. -/
theorem randomRoundingLaw_test_mean {n d : ℕ} (fuel : ℕ)
    (w : Fin n → ℝ) (x : Fin n → Rd d) (f : Rd d → ℝ) :
    (∫ v, (∑ k : Fin n, v k * f (x k)) ∂randomRoundingLaw fuel w) =
      ∑ k : Fin n, w k * f (x k) := by
  calc
    _ = ∑ k : Fin n, ∫ v, v k * f (x k) ∂randomRoundingLaw fuel w := by
      rw [integral_finsetSum]
      intro k _
      exact integrable_randomRoundingLaw fuel w _
    _ = _ := by
      simp_rw [integral_mul_const, randomRoundingLaw_coordinate_mean]

end Riesz.Negative
