import Riesz.Negative.MultiscaleRounding
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Field.GeomSum

/-!
Geometric cell labels for the multiscale rounding law. The bounds depend
on the number of occupied cells rather than the number of original atoms.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

def cubeCellLabel (d : ℕ) (h : ℝ) (x : Rd d) : Fin d → ℕ :=
  fun i => ⌊x i / h⌋₊

theorem cubeCellLabel_lt (d K : ℕ) (h : ℝ) (hh : 0 < h) (x : Rd d)
    (hx : x ∈ cube d ((K : ℝ) * h)) (i : Fin d) : cubeCellLabel d h x i < K := by
  apply (Nat.floor_lt (div_nonneg (hx i).1 hh.le)).2
  exact (div_lt_iff₀ hh).2 (hx i).2

theorem cellLabel_image_card_le {n d K : ℕ} (label : Fin n → Fin d → ℕ)
    (hlabel : ∀ i j, label i j < K) :
    (Finset.univ.image label).card ≤ K ^ d := by
  let boundedLabel : Fin n → (Fin d → Fin K) := fun i j => ⟨label i j, hlabel i j⟩
  calc
    _ = ((Finset.univ.image boundedLabel).image
        (fun z : Fin d → Fin K => fun j => (z j : ℕ))).card :=
      congrArg Finset.card Finset.image_image.symm
    _ ≤ (Finset.univ.image boundedLabel).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin d → Fin K)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = K ^ d := by simp

theorem cubeCellLabel_dist_le (d : ℕ) (h : ℝ) (hh : 0 < h) (x y : Rd d)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (he : cubeCellLabel d h x = cubeCellLabel d h y) :
    ‖x - y‖ ≤ Real.sqrt d * h := by
  have hc (i : Fin d) : |x i - y i| ≤ h := by
    have hf : (⌊x i / h⌋₊ : ℝ) = (⌊y i / h⌋₊ : ℝ) :=
      congrArg (fun a : ℕ => (a : ℝ)) (congrFun he i)
    have hxlo := (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg (hx i) hh.le))
    have hxhi := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (x i / h))
    have hylo := (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg (hy i) hh.le))
    have hyhi := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (y i / h))
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hsquare : ‖x - y‖ ^ 2 ≤ (d : ℝ) * h ^ 2 := by
    calc
      _ = ∑ i : Fin d, (x i - y i) ^ 2 := EuclideanSpace.real_norm_sq_eq (x - y)
      _ ≤ ∑ _i : Fin d, h ^ 2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hh.le).2 (hc i))
      _ = _ := by simp
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hh.le)).mp
    (by simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] using hsquare)

theorem cubeCellLabel_image_card_le (d n K : ℕ) (h : ℝ) (hh : 0 < h)
    (x : Fin n → Rd d) (hx : ∀ i, x i ∈ cube d ((K : ℝ) * h)) :
    (Finset.univ.image (fun i => cubeCellLabel d h (x i))).card ≤ K ^ d := by
  exact cellLabel_image_card_le _ (fun i j => cubeCellLabel_lt d K h hh (x i) (hx i) j)

theorem measurable_cubeCellLabel (d : ℕ) :
    Measurable (fun a : ℝ × Rd d => cubeCellLabel d a.1 a.2) := by
  unfold cubeCellLabel
  fun_prop

theorem cubeCellLabel_eq_zero (d : ℕ) (h : ℝ) (hh : 0 < h) (x : Rd d)
    (hx : x ∈ cube d h) : cubeCellLabel d h x = fun _ => 0 := by
  exact funext (fun i => Nat.lt_one_iff.mp
    (cubeCellLabel_lt d 1 h hh x (by simpa using hx) i))

theorem dyadicCubeLabel_image_card_le (d n k j : ℕ) (hj : j ≤ k)
    (r : ℝ) (hr : 0 < r) (x : Fin n → Rd d)
    (hx : ∀ i, x i ∈ cube d ((2 : ℝ) ^ k * r)) :
    (Finset.univ.image (fun i => cubeCellLabel d ((2 : ℝ) ^ j * r) (x i))).card ≤
      (2 ^ (k - j)) ^ d := by
  have hside : (2 : ℝ) ^ (k - j) * ((2 : ℝ) ^ j * r) = (2 : ℝ) ^ k * r := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
  exact cubeCellLabel_image_card_le d n (2 ^ (k - j)) _ (by positivity) x
    (fun i => by simpa only [Nat.cast_pow, Nat.cast_ofNat, hside] using hx i)

def dyadicCubeLabels (d n : ℕ) (r : ℝ) (x : Fin n → Rd d) : ℕ → Fin n → (Fin d → ℕ) :=
  fun j i => cubeCellLabel d ((2 : ℝ) ^ j * r) (x i)

theorem dyadicCubeRounding_energy_le (d n k : ℕ) (r q : ℝ) (hr : 0 < r) (hq : 0 < q)
    (x : Fin n → Rd d) (hinj : Function.Injective x)
    (hx : ∀ i, x i ∈ cube d ((2 : ℝ) ^ k * r))
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) :
    (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun i => v i - w i))
      ∂multiscaleRoundingLaw (k + 1) (partitionRoundingMasks (dyadicCubeLabels d n r x)) w) ≤
        (Real.sqrt d * r) ^ q / q * totalFractionalBudget w +
          ∑ j ∈ Finset.range k, (Real.sqrt d * ((2 : ℝ) ^ (j + 1) * r)) ^ q / q *
            (((2 ^ (k - j)) ^ d : ℕ) / (4 : ℝ)) := by
  have hbase := partitionRoundingLaw_expected_energy_le k (dyadicCubeLabels d n r x) q hq
    (fun j => Real.sqrt d * ((2 : ℝ) ^ j * r))
    (fun j _ => mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) hr.le))
    x hinj (fun j _ i l he => cubeCellLabel_dist_le d _ (by positivity) (x i) (x l)
      (fun a => (hx i a).1) (fun a => (hx l a).1) he) w hw
  have hsum :
      (∑ j ∈ Finset.range k, (Real.sqrt d * ((2 : ℝ) ^ (j + 1) * r)) ^ q / q *
        ((Finset.univ.image (dyadicCubeLabels d n r x j)).card / (4 : ℝ))) ≤
      ∑ j ∈ Finset.range k, (Real.sqrt d * ((2 : ℝ) ^ (j + 1) * r)) ^ q / q *
        (((2 ^ (k - j)) ^ d : ℕ) / (4 : ℝ)) :=
    Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (show
          ((Finset.univ.image (dyadicCubeLabels d n r x j)).card : ℝ) ≤
            (((2 ^ (k - j)) ^ d : ℕ) : ℝ) from by
        exact Nat.cast_le.mpr (dyadicCubeLabel_image_card_le d n k j
          (Nat.le_of_lt (Finset.mem_range.mp hj)) r hr x hx)) (by norm_num))
      (div_nonneg (Real.rpow_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) hr.le)) q) hq.le))
  simp only [pow_zero, one_mul] at hbase
  exact hbase.trans (add_le_add le_rfl hsum)

theorem dyadicCubeRounding_occupiedSites_spec (d n k : ℕ) (r : ℝ) (hr : 0 < r)
    (x : Fin n → Rd d) (hinj : Function.Injective x)
    (hx : ∀ i, x i ∈ cube d ((2 : ℝ) ^ k * r))
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (M : ℕ) (hM : ∑ i, w i = M) :
    ∀ᵐ v ∂multiscaleRoundingLaw (k + 1) (partitionRoundingMasks (dyadicCubeLabels d n r x)) w,
      (occupiedSites x v).card = M ∧
        weightedAtomicMeasure d n x v = ∑ y ∈ occupiedSites x v, Measure.dirac y := by
  have hroot (i l : Fin n) : dyadicCubeLabels d n r x k i = dyadicCubeLabels d n r x k l :=
    (cubeCellLabel_eq_zero d _ (by positivity) (x i) (hx i)).trans
      (cubeCellLabel_eq_zero d _ (by positivity) (x l) (hx l)).symm
  exact multiscaleRoundingLaw_occupiedSites_spec k _
    (fun i l => by simp [partitionRoundingMasks, hroot i l]) w hw M hM x hinj

theorem measurable_dyadicCubeLabels (d n : ℕ) :
    Measurable (fun a : ℝ × (Fin n → Rd d) => dyadicCubeLabels d n a.1 a.2) := by
  unfold dyadicCubeLabels
  exact measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun i =>
    (measurable_cubeCellLabel d).comp
      ((measurable_const.mul measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd))))

theorem measurable_partitionRoundingMasks {n : ℕ} {ι : Type*} [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableEq ι] :
    Measurable (partitionRoundingMasks : (ℕ → Fin n → ι) → RoundingMasks n) := by
  refine measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun p => ?_))
  apply measurable_to_bool
  simpa only [partitionRoundingMasks, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using measurableSet_eq_fun
    (f := fun c : ℕ → Fin n → ι => c j p.1) (g := fun c : ℕ → Fin n → ι => c j p.2)
    ((measurable_pi_apply p.1).comp (measurable_pi_apply j))
    ((measurable_pi_apply p.2).comp (measurable_pi_apply j))

theorem measurable_dyadicCubeRoundingLaw (d n k : ℕ) :
    Measurable (fun a : (ℝ × (Fin n → Rd d)) × (Fin n → ℝ) =>
      multiscaleRoundingLaw (k + 1)
        (partitionRoundingMasks (dyadicCubeLabels d n a.1.1 a.1.2)) a.2) := by
  have hm : Measurable (fun a : (ℝ × (Fin n → Rd d)) × (Fin n → ℝ) =>
      partitionRoundingMasks (dyadicCubeLabels d n a.1.1 a.1.2)) :=
    (measurable_partitionRoundingMasks (n := n) (ι := Fin d → ℕ)).comp
      ((measurable_dyadicCubeLabels d n).comp measurable_fst)
  exact (multiscaleRoundingLaw_measurable_probability (n := n) (k + 1)).1.comp
    (f := fun a : (ℝ × (Fin n → Rd d)) × (Fin n → ℝ) =>
      (partitionRoundingMasks (dyadicCubeLabels d n a.1.1 a.1.2), a.2))
    (hm.prodMk measurable_snd)

theorem finite_geometric_sum_le (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ_one : ρ < 1) (k : ℕ) :
    (∑ j ∈ Finset.range k, ρ ^ j) ≤ 1 / (1 - ρ) := by
  apply (le_div_iff₀ (sub_pos.mpr hρ_one)).2
  rw [geom_sum_mul_neg]
  exact sub_le_self 1 (pow_nonneg hρ k)

private theorem dyadicCubeScaleCost_eq (d k j : ℕ) (hj : j ≤ k) (r q : ℝ)
    (hr : 0 ≤ r) :
    (Real.sqrt d * ((2 : ℝ) ^ (j + 1) * r)) ^ q / q *
        (((2 ^ (k - j)) ^ d : ℕ) / (4 : ℝ)) =
      ((Real.sqrt d * r) ^ q / q *
        ((2 : ℝ) ^ q * ((2 : ℝ) ^ k) ^ d / 4)) *
          ((2 : ℝ) ^ q / (2 : ℝ) ^ d) ^ j := by
  have hscale : Real.sqrt d * ((2 : ℝ) ^ (j + 1) * r) =
      (Real.sqrt d * r) * (2 : ℝ) ^ (j + 1) := by ring
  rw [hscale, Real.mul_rpow (mul_nonneg (Real.sqrt_nonneg _) hr) (by positivity),
    Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
  have hpower : ((2 : ℝ) ^ (j + 1)) ^ q = ((2 : ℝ) ^ q) ^ (j + 1) := by
    rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)) (j + 1) q,
      mul_comm ((j + 1 : ℕ) : ℝ) q,
      Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ)) q (j + 1)]
  rw [hpower, pow_succ, pow_sub₀ (2 : ℝ) (by norm_num) hj, mul_pow, inv_pow]
  have hflip : ((2 : ℝ) ^ j) ^ d = ((2 : ℝ) ^ d) ^ j := by
    rw [← pow_mul, Nat.mul_comm j d, pow_mul]
  rw [hflip, div_pow]
  ring

private theorem dyadicCubeScaleSum_le (d k : ℕ) (r q : ℝ) (hr : 0 ≤ r)
    (hq : 0 < q) (hqd : q < (d : ℝ)) :
    (∑ j ∈ Finset.range k, (Real.sqrt d * ((2 : ℝ) ^ (j + 1) * r)) ^ q / q *
      (((2 ^ (k - j)) ^ d : ℕ) / (4 : ℝ))) ≤
        ((Real.sqrt d * r) ^ q / q * ((2 : ℝ) ^ q * ((2 : ℝ) ^ k) ^ d / 4)) /
          (1 - (2 : ℝ) ^ q / (2 : ℝ) ^ d) := by
  have hρ : 0 ≤ (2 : ℝ) ^ q / (2 : ℝ) ^ d :=
    div_nonneg (Real.rpow_nonneg (by norm_num) q) (by positivity)
  have hρ_one : (2 : ℝ) ^ q / (2 : ℝ) ^ d < 1 := by
    apply (div_lt_one (by positivity : 0 < (2 : ℝ) ^ d)).2
    simpa only [Real.rpow_natCast] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) hqd
  have hsum :
      (∑ j ∈ Finset.range k, (Real.sqrt d * ((2 : ℝ) ^ (j + 1) * r)) ^ q / q *
        (((2 ^ (k - j)) ^ d : ℕ) / (4 : ℝ))) =
      ((Real.sqrt d * r) ^ q / q * ((2 : ℝ) ^ q * ((2 : ℝ) ^ k) ^ d / 4)) *
        ∑ j ∈ Finset.range k, ((2 : ℝ) ^ q / (2 : ℝ) ^ d) ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j hj =>
      dyadicCubeScaleCost_eq d k j (Nat.le_of_lt (Finset.mem_range.mp hj)) r q hr)
  rw [hsum]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
    (finite_geometric_sum_le _ hρ hρ_one k)
    (by positivity : 0 ≤ (Real.sqrt d * r) ^ q / q *
      ((2 : ℝ) ^ q * ((2 : ℝ) ^ k) ^ d / 4))

/-- An explicit constant for the cube rounding bound, independent of the
number of sites, number of scales, and initial weights. -/
def cubeRoundingConstant (d : ℕ) (q : ℝ) : ℝ :=
  (Real.sqrt d) ^ q / q *
    (1 + (2 : ℝ) ^ q / (4 * (1 - (2 : ℝ) ^ q / (2 : ℝ) ^ d)))

theorem cubeRoundingConstant_pos (d : ℕ) (q : ℝ) (hq : 0 < q) (hqd : q < (d : ℝ)) :
    0 < cubeRoundingConstant d q := by
  have hρ_one : (2 : ℝ) ^ q / (2 : ℝ) ^ d < 1 :=
    (div_lt_one (by positivity : 0 < (2 : ℝ) ^ d)).2
      (by simpa only [Real.rpow_natCast] using
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) hqd)
  unfold cubeRoundingConstant
  exact mul_pos (div_pos (Real.rpow_pos_of_pos (Real.sqrt_pos.2 (hq.trans hqd)) q) hq)
    (add_pos_of_pos_of_nonneg (by norm_num)
      (div_nonneg (Real.rpow_nonneg (by norm_num) q)
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hρ_one.le))))

/-- The atomic part of the paper's dyadic discretization estimate, with an
explicit uniform constant and the actual multiscale rounding law. -/
theorem dyadicCubeRounding_uniform_energy_le (d n k : ℕ) (r q : ℝ)
    (hr : 0 < r) (hq : 0 < q) (hqd : q < (d : ℝ))
    (x : Fin n → Rd d) (hinj : Function.Injective x)
    (hx : ∀ i, x i ∈ cube d ((2 : ℝ) ^ k * r))
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) :
    (∫ v, Riesz.Analysis.signedDiscrepancyEnergy q
      (weightedSignedMeasure d n x (fun i => v i - w i))
      ∂multiscaleRoundingLaw (k + 1) (partitionRoundingMasks (dyadicCubeLabels d n r x)) w) ≤
        cubeRoundingConstant d q *
          (r ^ q * totalFractionalBudget w + ((2 : ℝ) ^ k * r) ^ d * r ^ (q - (d : ℝ))) := by
  have hbound := (dyadicCubeRounding_energy_le d n k r q hr hq x hinj hx w hw).trans
    (add_le_add le_rfl (dyadicCubeScaleSum_le d k r q hr.le hq hqd))
  have hvolume : ((2 : ℝ) ^ k * r) ^ d * r ^ (q - (d : ℝ)) =
      ((2 : ℝ) ^ k) ^ d * r ^ q := by
    rw [mul_pow, Real.rpow_sub hr, Real.rpow_natCast]
    field_simp [(pow_pos hr d).ne']
  have hbudget : 0 ≤ totalFractionalBudget w :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).1 (sub_nonneg.mpr (hw i).2))
  have hρ_one : (2 : ℝ) ^ q / (2 : ℝ) ^ d < 1 :=
    (div_lt_one (by positivity : 0 < (2 : ℝ) ^ d)).2
      (by simpa only [Real.rpow_natCast] using
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) hqd)
  have ha : 0 ≤ (Real.sqrt d) ^ q / q :=
    div_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) q) hq.le
  have hG : 0 ≤ (2 : ℝ) ^ q / (4 * (1 - (2 : ℝ) ^ q / (2 : ℝ) ^ d)) :=
    div_nonneg (Real.rpow_nonneg (by norm_num) q)
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hρ_one.le))
  apply hbound.trans
  simp only [cubeRoundingConstant, hvolume,
    Real.mul_rpow (Real.sqrt_nonneg (d : ℝ)) hr.le,
    div_mul_eq_div_div] at hG ⊢
  simp only [div_eq_mul_inv] at ha hG ⊢
  nlinarith only [mul_nonneg ha (mul_nonneg (by positivity : 0 ≤ ((2 : ℝ) ^ k) ^ d)
      (Real.rpow_nonneg hr.le q)),
    mul_nonneg (mul_nonneg ha hG) (mul_nonneg (Real.rpow_nonneg hr.le q) hbudget)]

end Riesz.Negative
