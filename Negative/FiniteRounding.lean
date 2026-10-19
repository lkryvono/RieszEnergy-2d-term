import Riesz.Negative.WeightedAtoms

/-! A deterministic transfer of two coordinates in a finite weight list.
The probabilistic finite iteration will use the checked two-site transfer law. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

def transferWeights {n : ℕ} (w : Fin n → ℝ) (i j : Fin n) (t : ℝ) : Fin n → ℝ :=
  fun k => w k + (if k = i then t else 0) - (if k = j then t else 0)

def fractionalSites {n : ℕ} (w : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun k => 0 < w k ∧ w k < 1)

theorem exists_two_fractional {n : ℕ} (w : Fin n → ℝ)
    (h : 1 < (fractionalSites w).card) :
    ∃ i j : Fin n, i ≠ j ∧ 0 < w i ∧ w i < 1 ∧ 0 < w j ∧ w j < 1 := by
  rcases Finset.one_lt_card.mp h with ⟨i, hi, j, hj, hij⟩
  simp only [fractionalSites, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact ⟨i, j, hij, hi.1, hi.2, hj.1, hj.2⟩

def totalFractionalBudget {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  ∑ k, fractionalBudget (w k)

theorem measurable_totalFractionalBudget {n : ℕ} :
    Measurable (totalFractionalBudget : (Fin n → ℝ) → ℝ) := by
  unfold totalFractionalBudget fractionalBudget
  fun_prop

theorem measurable_weightQuadratic_diff (d n : ℕ) (q : ℝ)
    (x : Fin n → Rd d) (w : Fin n → ℝ) :
    Measurable (fun v : Fin n → ℝ => weightQuadratic d n q x (fun k => v k - w k)) := by
  unfold weightQuadratic
  fun_prop

def transferWeightsLaw {n : ℕ} (w : Fin n → ℝ) (i j : Fin n) : Measure (Fin n → ℝ) :=
  (twoWeightTransferLaw (w i) (w j)).map (transferWeights w i j)

theorem measurable_transferWeights {n : ℕ} (w : Fin n → ℝ) (i j : Fin n) :
    Measurable (transferWeights w i j) := by
  apply measurable_pi_iff.mpr
  intro k
  unfold transferWeights
  split_ifs <;> fun_prop

theorem transferWeightsLaw_isProbability {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hi : 0 < w i) (hi_one : w i < 1) (hj : 0 < w j) (hj_one : w j < 1) :
    IsProbabilityMeasure (transferWeightsLaw w i j) := by
  unfold transferWeightsLaw
  letI := twoWeightTransferLaw_isProbability (w i) (w j) hi hi_one hj hj_one
  exact Measure.isProbabilityMeasure_map (measurable_transferWeights w i j).aemeasurable

theorem transferWeightsLaw_two_point {n : ℕ} (w : Fin n → ℝ) (i j : Fin n) :
    ∀ᵐ v ∂transferWeightsLaw w i j,
      v = transferWeights w i j (roundingUp (w i) (w j)) ∨
        v = transferWeights w i j (-roundingDown (w i) (w j)) := by
  unfold transferWeightsLaw twoWeightTransferLaw
  rw [Measure.map_add _ _ (measurable_transferWeights w i j), Measure.map_smul,
    Measure.map_smul]
  simp only [Measure.map_dirac]
  exact ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure (by simpa only [ae_dirac_eq, Filter.eventually_pure] using
        (Or.inl rfl : transferWeights w i j (roundingUp (w i) (w j)) = _ ∨ _)) _,
     Measure.ae_smul_measure (by simpa only [ae_dirac_eq, Filter.eventually_pure] using
        (Or.inr rfl : _ ∨ transferWeights w i j (-roundingDown (w i) (w j)) = _)) _⟩

theorem transferWeights_at_left {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) (t : ℝ) : transferWeights w i j t i = w i + t := by
  simp [transferWeights, hij]

theorem transferWeights_at_right {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) (t : ℝ) : transferWeights w i j t j = w j - t := by
  simp [transferWeights, Ne.symm hij]

theorem transferWeights_at_other {n : ℕ} (w : Fin n → ℝ) (i j k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ j) (t : ℝ) : transferWeights w i j t k = w k := by
  simp [transferWeights, hki, hkj]

theorem transferWeights_total {n : ℕ} (w : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    ∑ k, transferWeights w i j t k = ∑ k, w k := by
  unfold transferWeights
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

theorem transferWeights_budget {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) (t : ℝ) :
    totalFractionalBudget (transferWeights w i j t) =
      totalFractionalBudget w - fractionalBudget (w i) - fractionalBudget (w j) +
        fractionalBudget (w i + t) + fractionalBudget (w j - t) := by
  unfold totalFractionalBudget
  calc
    _ = ∑ k, (fractionalBudget (w k) +
        (if k = i then fractionalBudget (w i + t) - fractionalBudget (w i) else 0) +
        (if k = j then fractionalBudget (w j - t) - fractionalBudget (w j) else 0)) := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hki : k = i
          · subst k
            simp [transferWeights_at_left w i j hij t, hij]
          · by_cases hkj : k = j
            · subst k
              simp [transferWeights_at_right w i j hij t, Ne.symm hij]
            · simp [transferWeights_at_other w i j k hki hkj t, hki, hkj]
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      simp
      ring

theorem transferWeights_valid {n : ℕ} (w : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) (t : ℝ)
    (ht : t = roundingUp (w i) (w j) ∨ t = -roundingDown (w i) (w j)) :
    (∀ k, 0 ≤ transferWeights w i j t k ∧ transferWeights w i j t k ≤ 1) ∧
      (transferWeights w i j t i = 0 ∨ transferWeights w i j t i = 1 ∨
        transferWeights w i j t j = 0 ∨ transferWeights w i j t j = 1) := by
  have hpair := roundingOutcome_valid (w i) (w j) (hw i).1 (hw i).2
    (hw j).1 (hw j).2 t ht
  constructor
  · intro k
    by_cases hki : k = i
    · subst k
      rw [transferWeights_at_left w i j hij t]
      exact ⟨hpair.1, hpair.2.1⟩
    · by_cases hkj : k = j
      · subst k
        rw [transferWeights_at_right w i j hij t]
        exact ⟨hpair.2.2.1, hpair.2.2.2.1⟩
      · rw [transferWeights_at_other w i j k hki hkj t]
        exact hw k
  · simpa only [transferWeights_at_left w i j hij t,
      transferWeights_at_right w i j hij t] using hpair.2.2.2.2.1

theorem transferWeights_integral_fixed {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hi : 0 < w i) (hi_one : w i < 1) (hj : 0 < w j) (hj_one : w j < 1)
    (t : ℝ) (k : Fin n) (hk : w k = 0 ∨ w k = 1) :
    transferWeights w i j t k = w k := by
  have hki : k ≠ i := by
    intro h
    subst k
    rcases hk with h | h <;> linarith
  have hkj : k ≠ j := by
    intro h
    subst k
    rcases hk with h | h <;> linarith
  exact transferWeights_at_other w i j k hki hkj t

theorem fractionalSites_transfer_subset {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hi : 0 < w i) (hi_one : w i < 1) (hj : 0 < w j) (hj_one : w j < 1)
    (t : ℝ) :
    fractionalSites (transferWeights w i j t) ⊆ fractionalSites w := by
  intro k hk
  simp only [fractionalSites, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  by_cases hki : k = i
  · subst k
    exact ⟨hi, hi_one⟩
  · by_cases hkj : k = j
    · subst k
      exact ⟨hj, hj_one⟩
    · rwa [transferWeights_at_other w i j k hki hkj t] at hk

theorem fractionalSites_transfer_card_lt {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (hi : 0 < w i) (hi_one : w i < 1) (hj : 0 < w j) (hj_one : w j < 1)
    (t : ℝ) (ht : t = roundingUp (w i) (w j) ∨ t = -roundingDown (w i) (w j)) :
    (fractionalSites (transferWeights w i j t)).card < (fractionalSites w).card := by
  have hsub := fractionalSites_transfer_subset w i j hi hi_one hj hj_one t
  have hend := (transferWeights_valid w i j hij hw t ht).2
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ?_)
  rcases hend with hi0 | hi1 | hj0 | hj1
  · exact ⟨i, by simp [fractionalSites, hi, hi_one], by simp [fractionalSites, hi0]⟩
  · exact ⟨i, by simp [fractionalSites, hi, hi_one], by simp [fractionalSites, hi1]⟩
  · exact ⟨j, by simp [fractionalSites, hj, hj_one], by simp [fractionalSites, hj0]⟩
  · exact ⟨j, by simp [fractionalSites, hj, hj_one], by simp [fractionalSites, hj1]⟩

theorem transferWeights_outcome {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (hi : 0 < w i) (hi_one : w i < 1) (hj : 0 < w j) (hj_one : w j < 1)
    (t : ℝ) (ht : t = roundingUp (w i) (w j) ∨ t = -roundingDown (w i) (w j)) :
    (∀ k, 0 ≤ transferWeights w i j t k ∧ transferWeights w i j t k ≤ 1) ∧
      (∑ k, transferWeights w i j t k = ∑ k, w k) ∧
      (fractionalSites (transferWeights w i j t)).card < (fractionalSites w).card ∧
      (∀ k, w k = 0 ∨ w k = 1 → transferWeights w i j t k = w k) := by
  exact ⟨(transferWeights_valid w i j hij hw t ht).1,
    transferWeights_total w i j t,
    fractionalSites_transfer_card_lt w i j hij hw hi hi_one hj hj_one t ht,
    fun k hk => transferWeights_integral_fixed w i j hi hi_one hj hj_one t k hk⟩

theorem transferWeightsLaw_step {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (hi : 0 < w i) (hi_one : w i < 1) (hj : 0 < w j) (hj_one : w j < 1) :
    IsProbabilityMeasure (transferWeightsLaw w i j) ∧
      (∀ᵐ v ∂transferWeightsLaw w i j,
        (∀ k, 0 ≤ v k ∧ v k ≤ 1) ∧
          (∑ k, v k = ∑ k, w k) ∧
          (fractionalSites v).card < (fractionalSites w).card ∧
          (∀ k, w k = 0 ∨ w k = 1 → v k = w k)) := by
  refine ⟨transferWeightsLaw_isProbability w i j hi hi_one hj hj_one, ?_⟩
  apply (transferWeightsLaw_two_point w i j).mono
  intro v hv
  rcases hv with rfl | rfl
  · exact transferWeights_outcome w i j hij hw hi hi_one hj hj_one _ (Or.inl rfl)
  · exact transferWeights_outcome w i j hij hw hi hi_one hj hj_one _ (Or.inr rfl)

theorem transferWeightsLaw_coordinate_mean {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) (hi : 0 < w i) (hi_one : w i < 1)
    (hj : 0 < w j) (hj_one : w j < 1) (k : Fin n) :
    (∫ v, v k ∂transferWeightsLaw w i j) = w k := by
  rw [transferWeightsLaw, integral_map (measurable_transferWeights w i j).aemeasurable
    (measurable_pi_apply k).aestronglyMeasurable]
  by_cases hki : k = i
  · subst k
    simp_rw [transferWeights_at_left w i j hij]
    exact (twoWeightTransferLaw_weight_means (w i) (w j) hi hi_one hj hj_one).1
  · by_cases hkj : k = j
    · subst k
      simp_rw [transferWeights_at_right w i j hij]
      exact (twoWeightTransferLaw_weight_means (w i) (w j) hi hi_one hj hj_one).2
    · simp_rw [transferWeights_at_other w i j k hki hkj]
      letI := twoWeightTransferLaw_isProbability (w i) (w j) hi hi_one hj hj_one
      simp

theorem transferWeightsLaw_expected_budget {n : ℕ} (w : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) (hi : 0 < w i) (hi_one : w i < 1)
    (hj : 0 < w j) (hj_one : w j < 1) :
    (∫ v, totalFractionalBudget v ∂transferWeightsLaw w i j) =
      totalFractionalBudget w - 2 * roundingUp (w i) (w j) * roundingDown (w i) (w j) := by
  rw [transferWeightsLaw, integral_map (measurable_transferWeights w i j).aemeasurable
    (measurable_totalFractionalBudget).aestronglyMeasurable]
  rw [integral_twoWeightTransferLaw (w i) (w j) hi hi_one hj hj_one]
  rw [transferWeights_budget w i j hij, transferWeights_budget w i j hij]
  have hbudget := twoWeightTransferLaw_budget (w i) (w j) hi hi_one hj hj_one
  rw [integral_twoWeightTransferLaw (w i) (w j) hi hi_one hj hj_one] at hbudget
  have hmass : roundingDown (w i) (w j) /
      (roundingUp (w i) (w j) + roundingDown (w i) (w j)) +
      roundingUp (w i) (w j) /
      (roundingUp (w i) (w j) + roundingDown (w i) (w j)) = 1 := by
    field_simp [(add_pos (roundingSteps_pos (w i) (w j) hi hi_one hj hj_one).1
      (roundingSteps_pos (w i) (w j) hi hi_one hj hj_one).2).ne']
    ring
  linear_combination hbudget +
    (totalFractionalBudget w - fractionalBudget (w i) - fractionalBudget (w j)) * hmass

theorem weightedSignedMeasure_transfer_increment (d n : ℕ) (x : Fin n → Rd d)
    (w : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    weightedSignedMeasure d n x (fun k => transferWeights w i j t k - w k) =
      t • unitDipole d (x i) (x j) := by
  have hcoeff : (fun k => transferWeights w i j t k - w k) =
      (fun k => (if k = i then t else 0) - (if k = j then t else 0)) := by
    funext k
    dsimp [transferWeights]
    ring
  rw [hcoeff]
  simp only [weightedSignedMeasure, unitDipole]
  have hsplit (k : Fin n) :
      ((if k = i then t else 0) - (if k = j then t else 0)) •
        (Measure.dirac (x k)).toSignedMeasure =
        (if k = i then t else 0) • (Measure.dirac (x k)).toSignedMeasure -
          (if k = j then t else 0) • (Measure.dirac (x k)).toSignedMeasure := by
    rw [sub_smul (if k = i then t else 0) (if k = j then t else 0)
      (Measure.dirac (x k)).toSignedMeasure]
  simp_rw [hsplit, Finset.sum_sub_distrib]
  simp [smul_sub]

theorem transferWeights_increment_energy (d n : ℕ) (q : ℝ) (hq : 0 < q)
    (x : Fin n → Rd d) (hx : Function.Injective x) (w : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) :
    Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun k => transferWeights w i j t k - w k)) =
        2 * t ^ 2 * ‖x i - x j‖ ^ q / q := by
  rw [weightedSignedMeasure_transfer_increment,
    twoSiteIncrement_energy d q hq t (x i) (x j) (hx.ne hij)]

theorem measurable_weightedSignedMeasure_diff_energy (d n : ℕ) (q : ℝ)
    (x : Fin n → Rd d) (hx : Function.Injective x) (w : Fin n → ℝ) :
    Measurable (fun v : Fin n → ℝ => Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun k => v k - w k))) := by
  simpa only [weightedSignedMeasure_energy d n q x hx] using
    measurable_weightQuadratic_diff d n q x w

theorem transferWeightsLaw_expected_energy (d n : ℕ) (q : ℝ) (hq : 0 < q)
    (x : Fin n → Rd d) (hx : Function.Injective x) (w : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j)
    (hi : 0 < w i) (hi_one : w i < 1) (hj : 0 < w j) (hj_one : w j < 1) :
    (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun k => v k - w k)) ∂transferWeightsLaw w i j) =
        2 * roundingUp (w i) (w j) * roundingDown (w i) (w j) * ‖x i - x j‖ ^ q / q := by
  rw [transferWeightsLaw, integral_map (measurable_transferWeights w i j).aemeasurable
    (measurable_weightedSignedMeasure_diff_energy d n q x hx w).aestronglyMeasurable]
  simp_rw [weightedSignedMeasure_transfer_increment]
  exact twoWeightTransferLaw_expected_energy d q hq (w i) (w j)
    hi hi_one hj hj_one (x i) (x j) (hx.ne hij)

theorem transferWeightsLaw_energy_budget_bound (d n : ℕ) (q D : ℝ) (hq : 0 < q)
    (x : Fin n → Rd d) (hx : Function.Injective x) (w : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j)
    (hi : 0 < w i) (hi_one : w i < 1) (hj : 0 < w j) (hj_one : w j < 1)
    (hdiam : ‖x i - x j‖ ≤ D) :
    (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun k => v k - w k)) ∂transferWeightsLaw w i j) ≤
        D ^ q / q * (totalFractionalBudget w -
          ∫ v, totalFractionalBudget v ∂transferWeightsLaw w i j) := by
  rw [transferWeightsLaw_expected_energy d n q hq x hx w i j hij hi hi_one hj hj_one,
    transferWeightsLaw_expected_budget w i j hij hi hi_one hj hj_one]
  have hpower := Real.rpow_le_rpow (norm_nonneg (x i - x j)) hdiam hq.le
  convert mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hq).mpr hpower)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (roundingSteps_pos (w i) (w j) hi hi_one hj hj_one).1.le)
      (roundingSteps_pos (w i) (w j) hi hi_one hj hj_one).2.le) using 1
  all_goals first | rfl | ring

theorem exists_rounded_weights {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) :
    ∃ v : Fin n → ℝ, (∀ k, 0 ≤ v k ∧ v k ≤ 1) ∧
      (∑ k, v k = ∑ k, w k) ∧ (fractionalSites v).card ≤ 1 ∧
      (∀ k, w k = 0 ∨ w k = 1 → v k = w k) := by
  by_cases hstop : (fractionalSites w).card ≤ 1
  · exact ⟨w, hw, rfl, hstop, fun _ _ => rfl⟩
  · obtain ⟨i, j, hij, hi, hi_one, hj, hj_one⟩ :=
      exists_two_fractional w (lt_of_not_ge hstop)
    let v := transferWeights w i j (roundingUp (w i) (w j))
    have hstep := transferWeights_outcome w i j hij hw hi hi_one hj hj_one
      (roundingUp (w i) (w j)) (Or.inl rfl)
    obtain ⟨u, hu, hsum, hcard, hfixed⟩ := exists_rounded_weights v hstep.1
    refine ⟨u, hu, hsum.trans hstep.2.1, hcard, ?_⟩
    intro k hk
    have hvk : v k = w k := hstep.2.2.2 k hk
    have hk' : v k = 0 ∨ v k = 1 := by rw [hvk]; exact hk
    rw [hfixed k hk', hvk]
termination_by (fractionalSites w).card
decreasing_by
  simpa [v] using hstep.2.2.1

end Riesz.Negative
