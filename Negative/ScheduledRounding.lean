import Riesz.Negative.ExactCount
import Mathlib.Probability.Kernel.Representation

/-!
A finite schedule of measurable two-weight replacements. The Boolean mask
allows a schedule to round only within specified cells. Unlike an arbitrary
choice of a fractional pair, this construction is measurable in its inputs.
The existing `randomRoundingLaw` and its verified proofs are unchanged.
-/

noncomputable section

open MeasureTheory RieszShowcase ProbabilityTheory
open scoped ENNReal Classical

namespace Riesz.Negative

def pairTransferUp {n : ℕ} (p : Fin n × Fin n) (w : Fin n → ℝ) : Fin n → ℝ :=
  transferWeights w p.1 p.2 (roundingUp (w p.1) (w p.2))

def pairTransferDown {n : ℕ} (p : Fin n × Fin n) (w : Fin n → ℝ) : Fin n → ℝ :=
  transferWeights w p.1 p.2 (-roundingDown (w p.1) (w p.2))

def pairTransferProbUp {n : ℕ} (p : Fin n × Fin n) (w : Fin n → ℝ) : ℝ :=
  roundingDown (w p.1) (w p.2) /
    (roundingUp (w p.1) (w p.2) + roundingDown (w p.1) (w p.2))

def pairTransferProbDown {n : ℕ} (p : Fin n × Fin n) (w : Fin n → ℝ) : ℝ :=
  roundingUp (w p.1) (w p.2) /
    (roundingUp (w p.1) (w p.2) + roundingDown (w p.1) (w p.2))

def pairCanRound {n : ℕ} (enabled : Fin n × Fin n → Bool)
    (p : Fin n × Fin n) (w : Fin n → ℝ) : Prop :=
  enabled p = true ∧ p.1 ≠ p.2 ∧
    0 < w p.1 ∧ w p.1 < 1 ∧ 0 < w p.2 ∧ w p.2 < 1

/-- The finite binary law follows the supplied pair schedule and skips disabled
or nonfractional pairs. No selection of pairs depends on an unproved choice. -/
def scheduledRoundingLaw {n : ℕ} (enabled : Fin n × Fin n → Bool) :
    List (Fin n × Fin n) → (Fin n → ℝ) → Measure (Fin n → ℝ)
  | [], w => Measure.dirac w
  | p :: ps, w =>
      if pairCanRound enabled p w then
        ENNReal.ofReal (pairTransferProbUp p w) •
            scheduledRoundingLaw enabled ps (pairTransferUp p w) +
          ENNReal.ofReal (pairTransferProbDown p w) •
            scheduledRoundingLaw enabled ps (pairTransferDown p w)
      else scheduledRoundingLaw enabled ps w

@[fun_prop] theorem measurable_pairTransferUp {n : ℕ} (p : Fin n × Fin n) :
    Measurable (pairTransferUp p : (Fin n → ℝ) → (Fin n → ℝ)) := by
  unfold pairTransferUp transferWeights roundingUp
  refine measurable_pi_iff.mpr (fun k => ?_)
  split_ifs <;> fun_prop

@[fun_prop] theorem measurable_pairTransferDown {n : ℕ} (p : Fin n × Fin n) :
    Measurable (pairTransferDown p : (Fin n → ℝ) → (Fin n → ℝ)) := by
  unfold pairTransferDown transferWeights roundingDown
  refine measurable_pi_iff.mpr (fun k => ?_)
  split_ifs <;> fun_prop

theorem measurableSet_pairCanRound {n : ℕ} (p : Fin n × Fin n) :
    MeasurableSet {a : (Fin n × Fin n → Bool) × (Fin n → ℝ) |
      pairCanRound a.1 p a.2} := by
  unfold pairCanRound
  measurability

/-- The full finite law is jointly measurable in the cell mask and weights. -/
theorem measurable_scheduledRoundingLaw {n : ℕ} (ps : List (Fin n × Fin n)) :
    Measurable (fun a : (Fin n × Fin n → Bool) × (Fin n → ℝ) =>
      scheduledRoundingLaw a.1 ps a.2) := by
  induction ps with
  | nil =>
      exact Measure.measurable_dirac.comp measurable_snd
  | cons p ps ih =>
      simp only [scheduledRoundingLaw]
      refine Measurable.ite (measurableSet_pairCanRound p) ?_ ih
      refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      have hup := (Measure.measurable_coe hs).comp
        (ih.comp (measurable_fst.prodMk ((measurable_pairTransferUp p).comp measurable_snd)))
      have hdown := (Measure.measurable_coe hs).comp
        (ih.comp (measurable_fst.prodMk ((measurable_pairTransferDown p).comp measurable_snd)))
      unfold pairTransferProbUp pairTransferProbDown roundingUp roundingDown
      fun_prop

theorem pairTransferProb_nonneg_sum {n : ℕ} (p : Fin n × Fin n) (w : Fin n → ℝ)
    (h : 0 < w p.1 ∧ w p.1 < 1 ∧ 0 < w p.2 ∧ w p.2 < 1) :
    0 ≤ pairTransferProbUp p w ∧ 0 ≤ pairTransferProbDown p w ∧
      pairTransferProbUp p w + pairTransferProbDown p w = 1 := by
  have hsteps := roundingSteps_pos (w p.1) (w p.2) h.1 h.2.1 h.2.2.1 h.2.2.2
  unfold pairTransferProbUp pairTransferProbDown
  refine ⟨div_nonneg hsteps.2.le (add_pos hsteps.1 hsteps.2).le,
    div_nonneg hsteps.1.le (add_pos hsteps.1 hsteps.2).le, ?_⟩
  rw [← add_div, add_comm (roundingDown (w p.1) (w p.2)) (roundingUp (w p.1) (w p.2)),
    div_self (add_pos hsteps.1 hsteps.2).ne']

theorem integrable_scheduledRoundingLaw {n : ℕ} (enabled : Fin n × Fin n → Bool)
    (ps : List (Fin n × Fin n)) (w : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) :
    Integrable f (scheduledRoundingLaw enabled ps w) := by
  induction ps generalizing w with
  | nil =>
      simpa only [scheduledRoundingLaw] using
        (integrable_dirac (by simp) : Integrable f (Measure.dirac w))
  | cons p ps ih =>
      rw [scheduledRoundingLaw]
      split_ifs
      · exact integrable_add_measure.mpr
          ⟨(ih (pairTransferUp p w)).smul_measure ENNReal.ofReal_ne_top,
            (ih (pairTransferDown p w)).smul_measure ENNReal.ofReal_ne_top⟩
      · exact ih w

theorem scheduledRoundingLaw_isProbability {n : ℕ}
    (enabled : Fin n × Fin n → Bool) (ps : List (Fin n × Fin n)) (w : Fin n → ℝ) :
    IsProbabilityMeasure (scheduledRoundingLaw enabled ps w) := by
  induction ps generalizing w with
  | nil =>
      exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac w))
  | cons p ps ih =>
      rw [scheduledRoundingLaw]
      split_ifs with h
      · have hp := pairTransferProb_nonneg_sum p w h.2.2
        refine ⟨?_⟩
        simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_add hp.1 hp.2.1, hp.2.2, ENNReal.ofReal_one]
      · exact ih w

theorem integral_pairTransferLaw {n : ℕ} (p : Fin n × Fin n) (w : Fin n → ℝ)
    (h : 0 < w p.1 ∧ w p.1 < 1 ∧ 0 < w p.2 ∧ w p.2 < 1)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    (∫ v, f v ∂transferWeightsLaw w p.1 p.2) =
      pairTransferProbUp p w * f (pairTransferUp p w) +
        pairTransferProbDown p w * f (pairTransferDown p w) := by
  rw [transferWeightsLaw,
    integral_map (measurable_transferWeights w p.1 p.2).aemeasurable hf.aestronglyMeasurable]
  rw [integral_twoWeightTransferLaw (w p.1) (w p.2) h.1 h.2.1 h.2.2.1 h.2.2.2]
  rfl

theorem integral_scheduledRoundingLaw_cons {n : ℕ}
    (enabled : Fin n × Fin n → Bool) (p : Fin n × Fin n)
    (ps : List (Fin n × Fin n)) (w : Fin n → ℝ)
    (h : pairCanRound enabled p w) (f : (Fin n → ℝ) → ℝ) :
    (∫ v, f v ∂scheduledRoundingLaw enabled (p :: ps) w) =
      pairTransferProbUp p w * (∫ v, f v ∂scheduledRoundingLaw enabled ps (pairTransferUp p w)) +
        pairTransferProbDown p w * (∫ v, f v ∂scheduledRoundingLaw enabled ps (pairTransferDown p w)) := by
  rw [scheduledRoundingLaw, if_pos h]
  rw [integral_add_measure
    ((integrable_scheduledRoundingLaw enabled ps (pairTransferUp p w) f).smul_measure
      ENNReal.ofReal_ne_top)
    ((integrable_scheduledRoundingLaw enabled ps (pairTransferDown p w) f).smul_measure
      ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (pairTransferProb_nonneg_sum p w h.2.2).1,
    ENNReal.toReal_ofReal (pairTransferProb_nonneg_sum p w h.2.2).2.1, smul_eq_mul]

theorem pairTransfer_coordinate_mean {n : ℕ} (p : Fin n × Fin n) (w : Fin n → ℝ)
    (hij : p.1 ≠ p.2)
    (h : 0 < w p.1 ∧ w p.1 < 1 ∧ 0 < w p.2 ∧ w p.2 < 1) (k : Fin n) :
    pairTransferProbUp p w * pairTransferUp p w k +
      pairTransferProbDown p w * pairTransferDown p w k = w k := by
  have hm := transferWeightsLaw_coordinate_mean w p.1 p.2 hij
    h.1 h.2.1 h.2.2.1 h.2.2.2 k
  simpa only [integral_pairTransferLaw p w h (fun v => v k) (measurable_pi_apply k)] using hm

/-- A measurable schedule preserves every input coordinate in expectation. -/
theorem scheduledRoundingLaw_coordinate_mean {n : ℕ}
    (enabled : Fin n × Fin n → Bool) (ps : List (Fin n × Fin n))
    (w : Fin n → ℝ) (k : Fin n) :
    (∫ v, v k ∂scheduledRoundingLaw enabled ps w) = w k := by
  induction ps generalizing w with
  | nil =>
      simp [scheduledRoundingLaw]
  | cons p ps ih =>
      by_cases h : pairCanRound enabled p w
      · rw [integral_scheduledRoundingLaw_cons enabled p ps w h, ih, ih]
        exact pairTransfer_coordinate_mean p w h.2.1 h.2.2 k
      · simpa only [scheduledRoundingLaw, if_neg h] using ih w

/-- Every scheduled leaf preserves the total weight and all initially integral
coordinates, and remains in the unit weight cube. -/
theorem scheduledRoundingLaw_preserves {n : ℕ}
    (enabled : Fin n × Fin n → Bool) (ps : List (Fin n × Fin n))
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) :
    ∀ᵐ v ∂scheduledRoundingLaw enabled ps w,
      (∀ k, 0 ≤ v k ∧ v k ≤ 1) ∧ (∑ k, v k = ∑ k, w k) ∧
        (∀ k, w k = 0 ∨ w k = 1 → v k = w k) := by
  induction ps generalizing w with
  | nil =>
      simpa [scheduledRoundingLaw] using hw
  | cons p ps ih =>
      by_cases h : pairCanRound enabled p w
      · have hbranch (u : Fin n → ℝ) (hu : ∀ k, 0 ≤ u k ∧ u k ≤ 1)
            (hsum : (∑ k, u k) = ∑ k, w k)
            (hfixed : ∀ k, w k = 0 ∨ w k = 1 → u k = w k) :
            ∀ᵐ v ∂scheduledRoundingLaw enabled ps u,
              (∀ k, 0 ≤ v k ∧ v k ≤ 1) ∧ (∑ k, v k = ∑ k, w k) ∧
                (∀ k, w k = 0 ∨ w k = 1 → v k = w k) := by
          exact (ih u hu).mono fun v hv =>
            ⟨hv.1, hv.2.1.trans hsum,
              fun k hk => (hv.2.2 k ((hfixed k hk).symm ▸ hk)).trans (hfixed k hk)⟩
        have hup := transferWeights_outcome w p.1 p.2 h.2.1 hw
          h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
          (roundingUp (w p.1) (w p.2)) (Or.inl rfl)
        have hdown := transferWeights_outcome w p.1 p.2 h.2.1 hw
          h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
          (-roundingDown (w p.1) (w p.2)) (Or.inr rfl)
        rw [scheduledRoundingLaw, if_pos h]
        exact ae_add_measure_iff.mpr
          ⟨Measure.ae_smul_measure
              (hbranch (pairTransferUp p w) hup.1 hup.2.1 hup.2.2.2) _,
            Measure.ae_smul_measure
              (hbranch (pairTransferDown p w) hdown.1 hdown.2.1 hdown.2.2.2) _⟩
      · simpa only [scheduledRoundingLaw, if_neg h] using ih w hw

private theorem integral_pair_of_not_pairCanRound {n : ℕ}
    (enabled : Fin n × Fin n → Bool) (p : Fin n × Fin n) (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) (he : enabled p = true) (hij : p.1 ≠ p.2)
    (h : ¬pairCanRound enabled p w) :
    w p.1 = 0 ∨ w p.1 = 1 ∨ w p.2 = 0 ∨ w p.2 = 1 := by
  grind [pairCanRound]

private theorem scheduledRoundingLaw_preserves_integral_pair {n : ℕ}
    (enabled : Fin n × Fin n → Bool) (ps : List (Fin n × Fin n))
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) (p : Fin n × Fin n)
    (hp : w p.1 = 0 ∨ w p.1 = 1 ∨ w p.2 = 0 ∨ w p.2 = 1) :
    ∀ᵐ v ∂scheduledRoundingLaw enabled ps w,
      v p.1 = 0 ∨ v p.1 = 1 ∨ v p.2 = 0 ∨ v p.2 = 1 := by
  exact (scheduledRoundingLaw_preserves enabled ps w hw).mono fun v hv => by
    grind

/-- Every enabled distinct pair occurring in the schedule has an integral
endpoint at the end; later steps cannot make that endpoint fractional again. -/
theorem scheduledRoundingLaw_pair_settled {n : ℕ}
    (enabled : Fin n × Fin n → Bool) (ps : List (Fin n × Fin n))
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) (p : Fin n × Fin n)
    (hmem : p ∈ ps) (he : enabled p = true) (hij : p.1 ≠ p.2) :
    ∀ᵐ v ∂scheduledRoundingLaw enabled ps w,
      v p.1 = 0 ∨ v p.1 = 1 ∨ v p.2 = 0 ∨ v p.2 = 1 := by
  induction ps generalizing w with
  | nil =>
      simp at hmem
  | cons r ps ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst r
        by_cases h : pairCanRound enabled p w
        · have hup := transferWeights_valid w p.1 p.2 hij hw
            (roundingUp (w p.1) (w p.2)) (Or.inl rfl)
          have hdown := transferWeights_valid w p.1 p.2 hij hw
            (-roundingDown (w p.1) (w p.2)) (Or.inr rfl)
          rw [scheduledRoundingLaw, if_pos h]
          exact ae_add_measure_iff.mpr
            ⟨Measure.ae_smul_measure
                (scheduledRoundingLaw_preserves_integral_pair enabled ps
                  (pairTransferUp p w) hup.1 p hup.2) _,
              Measure.ae_smul_measure
                (scheduledRoundingLaw_preserves_integral_pair enabled ps
                  (pairTransferDown p w) hdown.1 p hdown.2) _⟩
        · simpa only [scheduledRoundingLaw, if_neg h] using
            scheduledRoundingLaw_preserves_integral_pair enabled ps w hw p
              (integral_pair_of_not_pairCanRound enabled p w hw he hij h)
      · by_cases h : pairCanRound enabled r w
        · have hup := transferWeights_valid w r.1 r.2 h.2.1 hw
            (roundingUp (w r.1) (w r.2)) (Or.inl rfl)
          have hdown := transferWeights_valid w r.1 r.2 h.2.1 hw
            (-roundingDown (w r.1) (w r.2)) (Or.inr rfl)
          rw [scheduledRoundingLaw, if_pos h]
          exact ae_add_measure_iff.mpr
            ⟨Measure.ae_smul_measure (ih (pairTransferUp r w) hup.1 htail) _,
              Measure.ae_smul_measure (ih (pairTransferDown r w) hdown.1 htail) _⟩
        · simpa only [scheduledRoundingLaw, if_neg h] using ih w hw htail

/-- A fixed schedule containing every pair, independent of the input weights. -/
def allPairsSchedule (n : ℕ) : List (Fin n × Fin n) := Finset.univ.toList

theorem mem_allPairsSchedule {n : ℕ} (p : Fin n × Fin n) : p ∈ allPairsSchedule n := by
  simp [allPairsSchedule]

/-- One pass through the fixed schedule settles every enabled distinct pair. -/
theorem scheduledRoundingLaw_all_pairs_settled {n : ℕ}
    (enabled : Fin n × Fin n → Bool) (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) :
    ∀ᵐ v ∂scheduledRoundingLaw enabled (allPairsSchedule n) w,
      ∀ i j, enabled (i, j) = true → i ≠ j →
        v i = 0 ∨ v i = 1 ∨ v j = 0 ∨ v j = 1 := by
  refine ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ?_))
  refine ae_all_iff.mpr (fun he => ae_all_iff.mpr (fun hij => ?_))
  exact scheduledRoundingLaw_pair_settled enabled (allPairsSchedule n) w hw (i, j)
    (mem_allPairsSchedule (i, j)) he hij

/-- A mask enabling all pairs inside a cell leaves at most one fractional site there. -/
theorem scheduledRoundingLaw_cell_fractional_card {n : ℕ}
    (enabled : Fin n × Fin n → Bool) (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) (A : Finset (Fin n))
    (he : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → enabled (i, j) = true) :
    ∀ᵐ v ∂scheduledRoundingLaw enabled (allPairsSchedule n) w,
      ((fractionalSites v) ∩ A).card ≤ 1 := by
  apply (scheduledRoundingLaw_all_pairs_settled enabled w hw).mono
  intro v hv
  refine Finset.card_le_one.mpr (fun i hi j hj => ?_)
  grind [fractionalSites]

/-- Integer mass eliminates the last fractional site after a full enabled pass. -/
theorem scheduledRoundingLaw_integral_final {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) (m : ℕ) (hsum : ∑ k, w k = (m : ℝ)) :
    ∀ᵐ v ∂scheduledRoundingLaw (fun _ => true) (allPairsSchedule n) w,
      ∀ k, v k = 0 ∨ v k = 1 := by
  filter_upwards [scheduledRoundingLaw_preserves (fun _ => true) (allPairsSchedule n) w hw,
    scheduledRoundingLaw_cell_fractional_card (fun _ => true) w hw Finset.univ
      (by simp)] with v hv hcard k
  exact integral_weights_of_integer_sum v hv.1 (by simpa using hcard) m
    (hv.2.1.trans hsum) k

/-- The previously verified transfer energy identity supplies a scheduled step's budget. -/
theorem pairTransfer_energy_budget {n d : ℕ} (q D : ℝ) (hq : 0 < q)
    (x : Fin n → Rd d) (hx : Function.Injective x)
    (w z : Fin n → ℝ) (p : Fin n × Fin n) (hij : p.1 ≠ p.2)
    (h : 0 < w p.1 ∧ w p.1 < 1 ∧ 0 < w p.2 ∧ w p.2 < 1)
    (hdiam : ‖x p.1 - x p.2‖ ≤ D) :
    pairTransferProbUp p w * weightQuadratic d n q x
        (fun k => pairTransferUp p w k - z k) +
      pairTransferProbDown p w * weightQuadratic d n q x
        (fun k => pairTransferDown p w k - z k) ≤
      weightQuadratic d n q x (fun k => w k - z k) +
        D ^ q / q * (totalFractionalBudget w -
          (pairTransferProbUp p w * totalFractionalBudget (pairTransferUp p w) +
            pairTransferProbDown p w * totalFractionalBudget (pairTransferDown p w))) := by
  have hshift := transferWeightsLaw_expected_shifted_energy d n q x hx w z
    p.1 p.2 hij h.1 h.2.1 h.2.2.1 h.2.2.2
  simp_rw [weightedSignedMeasure_energy d n q x hx] at hshift
  rw [integral_pairTransferLaw p w h
      (fun v => weightQuadratic d n q x (fun k => v k - z k))
      (measurable_weightQuadratic_diff d n q x z),
    integral_pairTransferLaw p w h
      (fun v => weightQuadratic d n q x (fun k => v k - w k))
      (measurable_weightQuadratic_diff d n q x w)] at hshift
  have hcost := transferWeightsLaw_energy_budget_bound d n q D hq x hx w
    p.1 p.2 hij h.1 h.2.1 h.2.2.1 h.2.2.2 hdiam
  simp_rw [weightedSignedMeasure_energy d n q x hx] at hcost
  rw [integral_pairTransferLaw p w h
      (fun v => weightQuadratic d n q x (fun k => v k - w k))
      (measurable_weightQuadratic_diff d n q x w),
    integral_pairTransferLaw p w h totalFractionalBudget measurable_totalFractionalBudget] at hcost
  linarith

/-- Scheduled transfers telescope relative to any earlier baseline. Only enabled
pairs need the diameter bound, so this theorem applies separately at each scale. -/
theorem scheduledRoundingLaw_shifted_energy_budget {n d : ℕ}
    (enabled : Fin n × Fin n → Bool) (ps : List (Fin n × Fin n))
    (q D : ℝ) (hq : 0 < q) (x : Fin n → Rd d) (hx : Function.Injective x)
    (hdiam : ∀ i j, enabled (i, j) = true → ‖x i - x j‖ ≤ D)
    (w z : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) :
    (∫ v, weightQuadratic d n q x (fun k => v k - z k)
      ∂scheduledRoundingLaw enabled ps w) ≤
      weightQuadratic d n q x (fun k => w k - z k) +
        D ^ q / q * (totalFractionalBudget w -
          ∫ v, totalFractionalBudget v ∂scheduledRoundingLaw enabled ps w) := by
  induction ps generalizing w with
  | nil => simp [scheduledRoundingLaw]
  | cons p ps ih =>
      by_cases h : pairCanRound enabled p w
      · have hup := transferWeights_valid w p.1 p.2 h.2.1 hw
          (roundingUp (w p.1) (w p.2)) (Or.inl rfl)
        have hdown := transferWeights_valid w p.1 p.2 h.2.1 hw
          (-roundingDown (w p.1) (w p.2)) (Or.inr rfl)
        have hih_up := ih (pairTransferUp p w) hup.1
        have hih_down := ih (pairTransferDown p w) hdown.1
        have hstep := pairTransfer_energy_budget q D hq x hx w z p h.2.1 h.2.2
          (hdiam p.1 p.2 h.1)
        have hp := pairTransferProb_nonneg_sum p w h.2.2
        rw [integral_scheduledRoundingLaw_cons enabled p ps w h
          (fun v => weightQuadratic d n q x (fun k => v k - z k)),
          integral_scheduledRoundingLaw_cons enabled p ps w h totalFractionalBudget]
        nlinarith [mul_le_mul_of_nonneg_left hih_up hp.1,
          mul_le_mul_of_nonneg_left hih_down hp.2.1]
      · simpa only [scheduledRoundingLaw, if_neg h] using ih w hw

/-- The measurable cell schedule obeys the same actual signed-energy budget as
the original fixed-input rounding law. -/
theorem scheduledRoundingLaw_expected_energy_le {n d : ℕ}
    (enabled : Fin n × Fin n → Bool) (ps : List (Fin n × Fin n))
    (q D : ℝ) (hq : 0 < q) (hD : 0 ≤ D)
    (x : Fin n → Rd d) (hx : Function.Injective x)
    (hdiam : ∀ i j, enabled (i, j) = true → ‖x i - x j‖ ≤ D)
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) :
    (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun k => v k - w k))
      ∂scheduledRoundingLaw enabled ps w) ≤ D ^ q / q * totalFractionalBudget w := by
  have hbudget : 0 ≤ ∫ v, totalFractionalBudget v ∂scheduledRoundingLaw enabled ps w :=
    integral_nonneg_of_ae ((scheduledRoundingLaw_preserves enabled ps w hw).mono
      (fun v hv => Finset.sum_nonneg
        (fun k _ => mul_nonneg (hv.1 k).1 (sub_nonneg.mpr (hv.1 k).2))))
  have hcore := scheduledRoundingLaw_shifted_energy_budget enabled ps q D hq x hx hdiam w w hw
  simp_rw [weightedSignedMeasure_energy d n q x hx]
  have hzero : weightQuadratic d n q x (fun k => w k - w k) = 0 := by
    simp [weightQuadratic]
  rw [hzero] at hcore
  have hcoeff : 0 ≤ D ^ q / q := div_nonneg (Real.rpow_nonneg hD q) hq.le
  nlinarith

/-- A measurable kernel on the full mask-and-weight input space. -/
def scheduledRoundingKernel {n : ℕ} (ps : List (Fin n × Fin n)) :
    Kernel ((Fin n × Fin n → Bool) × (Fin n → ℝ)) (Fin n → ℝ) where
  toFun a := scheduledRoundingLaw a.1 ps a.2
  measurable' := measurable_scheduledRoundingLaw ps

instance scheduledRoundingKernel_isMarkov {n : ℕ} (ps : List (Fin n × Fin n)) :
    IsMarkovKernel (scheduledRoundingKernel ps) where
  isProbabilityMeasure a := scheduledRoundingLaw_isProbability a.1 ps a.2

/-- One uniform mark samples the law jointly measurably in mask and weights. -/
theorem exists_scheduledRounding_sampler {n : ℕ} (ps : List (Fin n × Fin n)) :
    ∃ f : ((Fin n × Fin n → Bool) × (Fin n → ℝ)) → unitInterval → (Fin n → ℝ),
      Measurable (Function.uncurry f) ∧
        ∀ a, Measure.map (f a) volume = scheduledRoundingLaw a.1 ps a.2 := by
  exact (scheduledRoundingKernel ps).exists_measurable_map_eq_unitInterval

/-- A fixed uniform-space realization usable at successive rounding scales. -/
def sampleScheduledRounding {n : ℕ} (ps : List (Fin n × Fin n))
    (a : (Fin n × Fin n → Bool) × (Fin n → ℝ)) (u : unitInterval) : Fin n → ℝ :=
  Classical.choose (exists_scheduledRounding_sampler ps) a u

theorem measurable_sampleScheduledRounding {n : ℕ} (ps : List (Fin n × Fin n)) :
    Measurable (Function.uncurry (sampleScheduledRounding ps)) := by
  exact (Classical.choose_spec (exists_scheduledRounding_sampler ps)).1

theorem sampleScheduledRounding_map {n : ℕ} (ps : List (Fin n × Fin n))
    (a : (Fin n × Fin n → Bool) × (Fin n → ℝ)) :
    Measure.map (sampleScheduledRounding ps a) volume = scheduledRoundingLaw a.1 ps a.2 := by
  exact (Classical.choose_spec (exists_scheduledRounding_sampler ps)).2 a

theorem scheduledRoundingLaw_coordinate_lintegral {n : ℕ}
    (enabled : Fin n × Fin n → Bool) (ps : List (Fin n × Fin n))
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) (i : Fin n) :
    (∫⁻ v, ENNReal.ofReal (v i) ∂scheduledRoundingLaw enabled ps w) = ENNReal.ofReal (w i) := by
  have hnonneg : 0 ≤ᵐ[scheduledRoundingLaw enabled ps w] (fun v => v i) :=
    (scheduledRoundingLaw_preserves enabled ps w hw).mono (fun v hv => (hv.1 i).1)
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_scheduledRoundingLaw enabled ps w (fun v => v i)) hnonneg).symm.trans
      (congrArg ENNReal.ofReal (scheduledRoundingLaw_coordinate_mean enabled ps w i))

/-- The kernel preserves the entire atomic measure mean, not only total mass. -/
theorem scheduledRoundingLaw_weightedAtomic_mean {d n : ℕ}
    (enabled : Fin n × Fin n → Bool) (ps : List (Fin n × Fin n))
    (x : Fin n → Rd d) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (D : Set (Rd d)) :
    (∫⁻ v, weightedAtomicMeasure d n x v D ∂scheduledRoundingLaw enabled ps w) =
      weightedAtomicMeasure d n x w D := by
  simp_rw [weightedAtomicMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_finsetSum (f := fun (i : Fin n) (v : Fin n → ℝ) =>
    ENNReal.ofReal (v i) * Measure.dirac (x i) D) Finset.univ (fun i _ =>
      (ENNReal.measurable_ofReal.comp (measurable_pi_apply i)).mul measurable_const)]
  exact Finset.sum_congr rfl (fun i _ =>
    (lintegral_mul_const (Measure.dirac (x i) D)
      (ENNReal.measurable_ofReal.comp (measurable_pi_apply i))).trans
      (congrArg (fun a => a * Measure.dirac (x i) D)
        (scheduledRoundingLaw_coordinate_lintegral enabled ps w hw i)))

/-- At the root scale the measurable law produces an exact-size point set. -/
theorem scheduledRoundingLaw_occupiedSites_spec {n d : ℕ}
    (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (m : ℕ) (hsum : ∑ k, w k = (m : ℝ))
    (x : Fin n → Rd d) (hx : Function.Injective x) :
    ∀ᵐ v ∂scheduledRoundingLaw (fun _ => true) (allPairsSchedule n) w,
      (occupiedSites x v).card = m ∧
        weightedAtomicMeasure d n x v = ∑ y ∈ occupiedSites x v, Measure.dirac y := by
  filter_upwards [scheduledRoundingLaw_preserves (fun _ => true) (allPairsSchedule n) w hw,
    scheduledRoundingLaw_integral_final w hw m hsum] with v hv h01
  have hcard := occupied_card_eq_of_integral_weights v h01 m (hv.2.1.trans hsum)
  exact ⟨by simpa [occupiedSites, Finset.card_image_of_injective _ hx] using hcard,
    weightedAtomicMeasure_eq_occupiedSites x hx v h01⟩

/-- Each fractional site contributes at most one quarter of rounding budget. -/
theorem totalFractionalBudget_le_fractional_card {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) :
    totalFractionalBudget w ≤ (fractionalSites w).card / (4 : ℝ) := by
  have hsum : totalFractionalBudget w = ∑ k ∈ fractionalSites w, w k * (1 - w k) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ (fractionalSites w))
    grind [fractionalSites]
  rw [hsum]
  have hbound : (∑ k ∈ fractionalSites w, w k * (1 - w k)) ≤
      ∑ _k ∈ fractionalSites w, (1 / 4 : ℝ) :=
    Finset.sum_le_sum (fun k _ => by nlinarith [sq_nonneg (w k - 1 / 2)])
  simpa [div_eq_mul_inv] using hbound

/-- After rounding a partition, its residual budget is controlled by occupied
cells rather than by the potentially unbounded number of original atom sites. -/
theorem scheduledRoundingLaw_partition_budget {n : ℕ} {ι : Type*} [DecidableEq ι]
    (enabled : Fin n × Fin n → Bool) (label : Fin n → ι) (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (he : ∀ i j, label i = label j → i ≠ j → enabled (i, j) = true) :
    ∀ᵐ v ∂scheduledRoundingLaw enabled (allPairsSchedule n) w,
      totalFractionalBudget v ≤ (Finset.univ.image label).card / (4 : ℝ) := by
  filter_upwards [scheduledRoundingLaw_preserves enabled (allPairsSchedule n) w hw,
    scheduledRoundingLaw_all_pairs_settled enabled w hw] with v hv hsettled
  have hinj : Set.InjOn label (fractionalSites v) := by
    intro i hi j hj hlabel
    grind [fractionalSites]
  have hcard : ((fractionalSites v).image label).card ≤ (Finset.univ.image label).card :=
    Finset.card_le_card (Finset.image_subset_image (Finset.subset_univ (fractionalSites v)))
  rw [Finset.card_image_of_injOn hinj] at hcard
  exact (totalFractionalBudget_le_fractional_card v hv.1).trans
    (div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by norm_num))

end Riesz.Negative
