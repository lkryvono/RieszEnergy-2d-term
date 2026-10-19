import Riesz.Negative.DiscrepancyBridge

/-! Independent finite cells and cancellation of their centered cross energies.
This supplies finite-volume inputs to the cube tiling argument; it does not
assert the cube limit or the stationary comparison. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

/-- The mean counting measure of a tuple law, as a sum of its coordinate marginals. -/
def tupleMeanMeasure (d n : ℕ) (Q : Measure (Fin n → Rd d)) : Measure (Rd d) :=
  ∑ i, Measure.map (fun x => x i) Q

instance tupleMeanMeasure_isFinite (d n : ℕ) (Q : Measure (Fin n → Rd d))
    [IsFiniteMeasure Q] : IsFiniteMeasure (tupleMeanMeasure d n Q) :=
  inferInstanceAs (IsFiniteMeasure (∑ i : Fin n, Measure.map (fun x => x i) Q))

/-- The mean cross-pair measure of two independent tuple laws. -/
def independentTuplePairMean (d n r : ℕ) (Q : Measure (Fin n → Rd d))
    (R : Measure (Fin r → Rd d)) : Measure (Rd d × Rd d) :=
  ∑ ij : Fin n × Fin r, Measure.map (fun z => (z.1 ij.1, z.2 ij.2)) (Q.prod R)

/-- Independence makes every cross-cell pair equal to the product of the mean measures. -/
theorem independentTuplePairMean_eq_prod (d n r : ℕ)
    (Q : Measure (Fin n → Rd d)) (R : Measure (Fin r → Rd d))
    [IsFiniteMeasure Q] [IsFiniteMeasure R] :
    independentTuplePairMean d n r Q R =
      (tupleMeanMeasure d n Q).prod (tupleMeanMeasure d r R) := by
  simp only [tupleMeanMeasure, independentTuplePairMean, ← Measure.sum_fintype,
    Measure.prod_sum, Measure.map_prod_map Q R (measurable_pi_apply _) (measurable_pi_apply _)]
  rfl

theorem tupleMeanMeasure_coordinate_integrable (d n : ℕ) (Q : Measure (Fin n → Rd d))
    (f : Rd d → ℝ) (hf : Integrable f (tupleMeanMeasure d n Q)) (i : Fin n) :
    Integrable (fun x => f (x i)) Q := by
  have hi : Integrable f (Measure.map (fun x : Fin n → Rd d => x i) Q) :=
    hf.mono_measure (Finset.single_le_sum
      (fun j _ => Measure.zero_le (Measure.map (fun x : Fin n → Rd d => x j) Q))
      (Finset.mem_univ i))
  exact hi.comp_measurable (measurable_pi_apply i)

theorem tupleMeanMeasure_integrable_sum (d n : ℕ) (Q : Measure (Fin n → Rd d))
    (f : Rd d → ℝ) (hf : Integrable f (tupleMeanMeasure d n Q)) :
    Integrable (fun x => ∑ i, f (x i)) Q := by
  exact integrable_finsetSum _ (fun i _ => tupleMeanMeasure_coordinate_integrable d n Q f hf i)

theorem tupleMeanMeasure_integral_sum (d n : ℕ) (Q : Measure (Fin n → Rd d))
    (f : Rd d → ℝ) (hf : Integrable f (tupleMeanMeasure d n Q)) :
    (∫ x, ∑ i, f (x i) ∂Q) = ∫ a, f a ∂tupleMeanMeasure d n Q := by
  have hmap (i : Fin n) : Integrable f (Measure.map (fun x : Fin n → Rd d => x i) Q) :=
    hf.mono_measure (Finset.single_le_sum
      (fun j _ => Measure.zero_le (Measure.map (fun x : Fin n → Rd d => x j) Q))
      (Finset.mem_univ i))
  rw [integral_finsetSum _ (fun i _ => tupleMeanMeasure_coordinate_integrable d n Q f hf i),
    tupleMeanMeasure, integral_finsetSum_measure (fun i _ => hmap i)]
  exact Finset.sum_congr rfl (fun i _ =>
    (integral_map (measurable_pi_apply i).aemeasurable (hmap i).aestronglyMeasurable).symm)

theorem independentTuplePair_map_integrable (d n r : ℕ)
    (Q : Measure (Fin n → Rd d)) (R : Measure (Fin r → Rd d))
    [IsFiniteMeasure Q] [IsFiniteMeasure R] (k : Rd d → Rd d → ℝ)
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleMeanMeasure d n Q).prod (tupleMeanMeasure d r R))) (ij : Fin n × Fin r) :
    Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      (Measure.map (fun z => (z.1 ij.1, z.2 ij.2)) (Q.prod R)) := by
  have hmean : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      (independentTuplePairMean d n r Q R) :=
    (independentTuplePairMean_eq_prod d n r Q R).symm ▸ hk
  exact hmean.mono_measure (Finset.single_le_sum
    (fun uv _ => Measure.zero_le (Measure.map
      (fun z : (Fin n → Rd d) × (Fin r → Rd d) => (z.1 uv.1, z.2 uv.2)) (Q.prod R)))
    (Finset.mem_univ ij))

theorem independentTuplePair_integrable_sum (d n r : ℕ)
    (Q : Measure (Fin n → Rd d)) (R : Measure (Fin r → Rd d))
    [IsFiniteMeasure Q] [IsFiniteMeasure R] (k : Rd d → Rd d → ℝ)
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleMeanMeasure d n Q).prod (tupleMeanMeasure d r R))) :
    Integrable (fun z => ∑ ij : Fin n × Fin r, k (z.1 ij.1) (z.2 ij.2)) (Q.prod R) := by
  exact integrable_finsetSum _ (fun ij _ =>
    (independentTuplePair_map_integrable d n r Q R k hk ij).comp_measurable
      (((measurable_pi_apply ij.1).comp measurable_fst).prodMk
        ((measurable_pi_apply ij.2).comp measurable_snd)))

theorem independentTuplePair_integral_sum (d n r : ℕ)
    (Q : Measure (Fin n → Rd d)) (R : Measure (Fin r → Rd d))
    [IsFiniteMeasure Q] [IsFiniteMeasure R] (k : Rd d → Rd d → ℝ)
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleMeanMeasure d n Q).prod (tupleMeanMeasure d r R))) :
    (∫ z, ∑ ij : Fin n × Fin r, k (z.1 ij.1) (z.2 ij.2) ∂Q.prod R) =
      ∫ p : Rd d × Rd d, k p.1 p.2 ∂(tupleMeanMeasure d n Q).prod
        (tupleMeanMeasure d r R) := by
  have hmap := independentTuplePair_map_integrable d n r Q R k hk
  have hcomp (ij : Fin n × Fin r) :
      Integrable (fun z => k (z.1 ij.1) (z.2 ij.2)) (Q.prod R) :=
    (hmap ij).comp_measurable
      (((measurable_pi_apply ij.1).comp measurable_fst).prodMk
        ((measurable_pi_apply ij.2).comp measurable_snd))
  rw [integral_finsetSum _ (fun ij _ => hcomp ij),
    ← independentTuplePairMean_eq_prod d n r Q R, independentTuplePairMean,
    integral_finsetSum_measure (fun ij _ => hmap ij)]
  exact Finset.sum_congr rfl (fun ij _ => (integral_map
    (φ := fun z : (Fin n → Rd d) × (Fin r → Rd d) => (z.1 ij.1, z.2 ij.2))
    (((measurable_pi_apply ij.1).comp measurable_fst).prodMk
      ((measurable_pi_apply ij.2).comp measurable_snd)).aemeasurable
    (hmap ij).aestronglyMeasurable).symm)

/-- The cross quadratic form of two tuple discrepancies, centered by their true means. -/
def centeredTupleCross (d n r : ℕ) (Q : Measure (Fin n → Rd d))
    (R : Measure (Fin r → Rd d)) (k : Rd d → Rd d → ℝ)
    (z : (Fin n → Rd d) × (Fin r → Rd d)) : ℝ :=
  (∑ ij : Fin n × Fin r, k (z.1 ij.1) (z.2 ij.2)) -
    (∑ i, ∫ b, k (z.1 i) b ∂tupleMeanMeasure d r R) -
    (∑ j, ∫ a, k a (z.2 j) ∂tupleMeanMeasure d n Q) +
    ∫ p : Rd d × Rd d, k p.1 p.2 ∂(tupleMeanMeasure d n Q).prod (tupleMeanMeasure d r R)

/-- Integrability of the centered cross form follows from integrability under the mean measures. -/
theorem centeredTupleCross_integrable (d n r : ℕ)
    (Q : Measure (Fin n → Rd d)) (R : Measure (Fin r → Rd d))
    [IsFiniteMeasure Q] [IsFiniteMeasure R] (k : Rd d → Rd d → ℝ)
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleMeanMeasure d n Q).prod (tupleMeanMeasure d r R))) :
    Integrable (centeredTupleCross d n r Q R k) (Q.prod R) := by
  exact (((independentTuplePair_integrable_sum d n r Q R k hk).sub
    ((tupleMeanMeasure_integrable_sum d n Q
      (fun a => ∫ b, k a b ∂tupleMeanMeasure d r R) hk.integral_prod_left).comp_fst R)).sub
    ((tupleMeanMeasure_integrable_sum d r R
      (fun b => ∫ a, k a b ∂tupleMeanMeasure d n Q) hk.integral_prod_right).comp_snd Q)).add
    (integrable_const (∫ p : Rd d × Rd d, k p.1 p.2 ∂(tupleMeanMeasure d n Q).prod
      (tupleMeanMeasure d r R)))

/-- Independent mean-zero cell discrepancies have exactly zero expected cross energy. -/
theorem expected_centeredTupleCross_eq_zero (d n r : ℕ)
    (Q : Measure (Fin n → Rd d)) (R : Measure (Fin r → Rd d))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] (k : Rd d → Rd d → ℝ)
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleMeanMeasure d n Q).prod (tupleMeanMeasure d r R))) :
    (∫ z, centeredTupleCross d n r Q R k z ∂Q.prod R) = 0 := by
  have hA := independentTuplePair_integrable_sum d n r Q R k hk
  have hB := (tupleMeanMeasure_integrable_sum d n Q
    (fun a => ∫ b, k a b ∂tupleMeanMeasure d r R) hk.integral_prod_left).comp_fst R
  have hC := (tupleMeanMeasure_integrable_sum d r R
    (fun b => ∫ a, k a b ∂tupleMeanMeasure d n Q) hk.integral_prod_right).comp_snd Q
  have hD : Integrable (fun _ : (Fin n → Rd d) × (Fin r → Rd d) =>
      ∫ p : Rd d × Rd d, k p.1 p.2 ∂(tupleMeanMeasure d n Q).prod
        (tupleMeanMeasure d r R)) (Q.prod R) := integrable_const _
  unfold centeredTupleCross
  have hAB : Integrable (fun z => (∑ ij : Fin n × Fin r, k (z.1 ij.1) (z.2 ij.2)) -
      (∑ i, ∫ b, k (z.1 i) b ∂tupleMeanMeasure d r R)) (Q.prod R) := hA.sub hB
  have hABC : Integrable (fun z => (∑ ij : Fin n × Fin r, k (z.1 ij.1) (z.2 ij.2)) -
      (∑ i, ∫ b, k (z.1 i) b ∂tupleMeanMeasure d r R) -
      (∑ j, ∫ a, k a (z.2 j) ∂tupleMeanMeasure d n Q)) (Q.prod R) := hAB.sub hC
  rw [integral_add hABC hD, integral_sub hAB hC, integral_sub hA hB]
  rw [independentTuplePair_integral_sum d n r Q R k hk,
    integral_fun_fst (fun x : Fin n → Rd d => ∑ i, ∫ b, k (x i) b ∂tupleMeanMeasure d r R),
    integral_fun_snd (fun y : Fin r → Rd d => ∑ j, ∫ a, k a (y j) ∂tupleMeanMeasure d n Q),
    integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [tupleMeanMeasure_integral_sum d n Q
      (fun a => ∫ b, k a b ∂tupleMeanMeasure d r R) hk.integral_prod_left,
    tupleMeanMeasure_integral_sum d r R
      (fun b => ∫ a, k a b ∂tupleMeanMeasure d n Q) hk.integral_prod_right]
  rw [← integral_prod _ hk, ← integral_prod_symm _ hk]
  ring

/-- Evaluation of the mean measure equals the expected count on every measurable set. -/
theorem tupleMeanMeasure_apply (d n : ℕ) (Q : Measure (Fin n → Rd d))
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    tupleMeanMeasure d n Q D = ∫⁻ x, tupleCounting d n x D ∂Q := by
  have heval (i : Fin n) : (∫⁻ x, Measure.dirac (x i) D ∂Q) =
      (Measure.map (fun x : Fin n → Rd d => x i) Q) D := by
    simpa only [Measure.dirac_apply' _ hD, Set.indicator_apply, Pi.one_apply,
      Measure.map_apply (f := fun x : Fin n → Rd d => x i)
        (measurable_pi_apply i) hD, one_mul] using
      lintegral_indicator_const_comp (μ := Q) (measurable_pi_apply i) hD (1 : ℝ≥0∞)
  simp_rw [tupleMeanMeasure, tupleCounting, Measure.finsetSum_apply]
  rw [lintegral_finsetSum (f := fun (i : Fin n) (x : Fin n → Rd d) => Measure.dirac (x i) D)
    Finset.univ (fun i _ => (Measure.measurable_coe hD).comp
      (Measure.measurable_dirac.comp (measurable_pi_apply i)))]
  simp only [heval]

/-- The showcase's balance condition identifies the actual tuple mean with cube volume. -/
theorem tupleBalanced_tupleMeanMeasure (d m : ℕ)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    tupleMeanMeasure d (m ^ d) Q = volume.restrict (cube d (m : ℝ)) := by
  exact Measure.ext (fun D hD =>
    (tupleMeanMeasure_apply d (m ^ d) Q D hD).trans (hQ.2.2 D hD))

/-- Almost-sure support of the tuples is inherited by their mean counting measure. -/
theorem tupleMeanMeasure_concentrated (d n : ℕ) (Q : Measure (Fin n → Rd d))
    (S : Set (Rd d)) (hS : MeasurableSet S) (hQ : ∀ᵐ x ∂Q, ∀ i, x i ∈ S) :
    tupleMeanMeasure d n Q Sᶜ = 0 := by
  rw [tupleMeanMeasure_apply d n Q Sᶜ hS.compl]
  exact lintegral_eq_zero_of_ae_eq_zero (hQ.mono (fun x hx =>
    (tupleCounting_compl_eq_zero_iff d n x S hS).mpr hx))

/-- Bounded tuple supports justify all distance-power cross integrals. -/
theorem independentTuple_rpow_kernel_integrable (d n r : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (Q : Measure (Fin n → Rd d)) (R : Measure (Fin r → Rd d))
    [IsFiniteMeasure Q] [IsFiniteMeasure R] (S : Set (Rd d))
    (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hQ : ∀ᵐ x ∂Q, ∀ i, x i ∈ S) (hR : ∀ᵐ y ∂R, ∀ j, y j ∈ S) :
    Integrable (fun p : Rd d × Rd d => ‖p.1 - p.2‖ ^ q)
      ((tupleMeanMeasure d n Q).prod (tupleMeanMeasure d r R)) := by
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp hbounded
  exact Riesz.Analysis.integrable_rpow_distance q L hq _ _
    (Riesz.Analysis.ae_distance_le_of_concentrated _ _ S L
      (tupleMeanMeasure_concentrated d n Q S hS hQ)
      (tupleMeanMeasure_concentrated d r R S hS hR)
      (fun a ha b hb => dist_eq_norm a b ▸ hL ha hb))

/-- Independent bounded point cells have zero expected centered distance-power cross term. -/
theorem expected_rpow_centeredTupleCross_eq_zero (d n r : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (Q : Measure (Fin n → Rd d)) (R : Measure (Fin r → Rd d))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] (S : Set (Rd d))
    (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hQ : ∀ᵐ x ∂Q, ∀ i, x i ∈ S) (hR : ∀ᵐ y ∂R, ∀ j, y j ∈ S) :
    (∫ z, centeredTupleCross d n r Q R (fun a b => ‖a - b‖ ^ q) z ∂Q.prod R) = 0 := by
  exact expected_centeredTupleCross_eq_zero d n r Q R _
    (independentTuple_rpow_kernel_integrable d n r q hq Q R S hS hbounded hQ hR)

/-- Integrating against a finite counting measure is exactly a sum over point indices. -/
theorem integral_tupleCounting (d n : ℕ) (x : Fin n → Rd d) (f : Rd d → ℝ) :
    (∫ a, f a ∂tupleCounting d n x) = ∑ i, f (x i) := by
  rw [tupleCounting, integral_finsetSum_measure (fun _ _ => integrable_dirac enorm_lt_top)]
  simp only [integral_dirac]

theorem iterated_integral_tupleCounting (d n r : ℕ) (x : Fin n → Rd d) (y : Fin r → Rd d)
    (k : Rd d → Rd d → ℝ) :
    (∫ a, ∫ b, k a b ∂tupleCounting d r y ∂tupleCounting d n x) =
      ∑ ij : Fin n × Fin r, k (x ij.1) (y ij.2) := by
  simp only [integral_tupleCounting, Fintype.sum_prod_type]

/-- The finite discrepancy cross form, with mixed terms integrated point-first. -/
def tupleDiscrepancyCross (d n r : ℕ) (ν ρ : Measure (Rd d))
    (k : Rd d → Rd d → ℝ) (z : (Fin n → Rd d) × (Fin r → Rd d)) : ℝ :=
  (∫ a, ∫ b, k a b ∂tupleCounting d r z.2 ∂tupleCounting d n z.1) -
    (∫ a, ∫ b, k a b ∂ρ ∂tupleCounting d n z.1) -
    (∫ b, ∫ a, k a b ∂ν ∂tupleCounting d r z.2) +
    ∫ p : Rd d × Rd d, k p.1 p.2 ∂ν.prod ρ

theorem tupleDiscrepancyCross_eq_centered (d n r : ℕ)
    (Q : Measure (Fin n → Rd d)) (R : Measure (Fin r → Rd d))
    (k : Rd d → Rd d → ℝ) (z : (Fin n → Rd d) × (Fin r → Rd d)) :
    tupleDiscrepancyCross d n r (tupleMeanMeasure d n Q) (tupleMeanMeasure d r R) k z =
      centeredTupleCross d n r Q R k z := by
  simp only [tupleDiscrepancyCross, centeredTupleCross, integral_tupleCounting,
    Fintype.sum_prod_type]

theorem expected_tupleDiscrepancyCross_eq_zero (d n r : ℕ)
    (Q : Measure (Fin n → Rd d)) (R : Measure (Fin r → Rd d))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] (k : Rd d → Rd d → ℝ)
    (hk : Integrable (fun p : Rd d × Rd d => k p.1 p.2)
      ((tupleMeanMeasure d n Q).prod (tupleMeanMeasure d r R))) :
    (∫ z, tupleDiscrepancyCross d n r (tupleMeanMeasure d n Q)
      (tupleMeanMeasure d r R) k z ∂Q.prod R) = 0 := by
  simpa only [tupleDiscrepancyCross_eq_centered] using
    expected_centeredTupleCross_eq_zero d n r Q R k hk

/-- The actual balanced cube backgrounds cancel the expected distance-power cross term.
This identity is the finite independent-cell component of the paper's increment argument. -/
theorem balanced_cube_cross_expectation (d m ℓ : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (Q : Measure (Fin (m ^ d) → Rd d)) (R : Measure (Fin (ℓ ^ d) → Rd d))
    (hQ : TupleBalancedAdmissible d m Q) (hR : TupleBalancedAdmissible d ℓ R) :
    (∫ z, tupleDiscrepancyCross d (m ^ d) (ℓ ^ d)
      (volume.restrict (cube d (m : ℝ))) (volume.restrict (cube d (ℓ : ℝ)))
      (fun a b => ‖a - b‖ ^ q) z ∂Q.prod R) = 0 := by
  letI : IsProbabilityMeasure Q := hQ.1
  letI : IsProbabilityMeasure R := hR.1
  have hk := independentTuple_rpow_kernel_integrable d (m ^ d) (ℓ ^ d) q hq Q R
    (cube d (m : ℝ) ∪ cube d (ℓ : ℝ))
    ((measurableSet_cube d (m : ℝ)).union (measurableSet_cube d (ℓ : ℝ)))
    ((cube_isBounded d (m : ℝ)).union (cube_isBounded d (ℓ : ℝ)))
    (hQ.2.1.mono (fun x hx i => Set.mem_union_left _ (hx.2 i)))
    (hR.2.1.mono (fun y hy j => Set.mem_union_right _ (hy.2 j)))
  rw [← tupleBalanced_tupleMeanMeasure d m Q hQ, ← tupleBalanced_tupleMeanMeasure d ℓ R hR]
  exact expected_tupleDiscrepancyCross_eq_zero d (m ^ d) (ℓ ^ d) Q R _ hk

/-- Deterministic translations preserve integrability of bounded-support distance-power kernels. -/
theorem shifted_rpow_kernel_integrable (d : ℕ) (q L : ℝ) (hq : 0 ≤ q)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (u v : Rd d)
    (hbound : ∀ᵐ p : Rd d × Rd d ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L) :
    Integrable (fun p : Rd d × Rd d => ‖(u + p.1) - (v + p.2)‖ ^ q) (μ.prod ν) := by
  refine (integrable_const ((‖u - v‖ + L) ^ q)).mono'
    ((((continuous_const.add continuous_fst).sub
      (continuous_const.add continuous_snd)).norm.measurable.pow_const q).aestronglyMeasurable) ?_
  filter_upwards [hbound] with p hp
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  refine Real.rpow_le_rpow (norm_nonneg _) ?_ hq
  have hshift : ‖(u + p.1) - (v + p.2)‖ ≤ ‖u - v‖ + ‖p.1 - p.2‖ := by
    simpa only [dist_eq_norm] using dist_add_add_le u p.1 v p.2
  exact hshift.trans (add_le_add le_rfl hp)

/-- Cross energies between independent balanced cells cancel after arbitrary deterministic shifts. -/
theorem shifted_balanced_cube_cross_expectation (d m ℓ : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (Q : Measure (Fin (m ^ d) → Rd d)) (R : Measure (Fin (ℓ ^ d) → Rd d))
    (hQ : TupleBalancedAdmissible d m Q) (hR : TupleBalancedAdmissible d ℓ R)
    (u v : Rd d) :
    (∫ z, tupleDiscrepancyCross d (m ^ d) (ℓ ^ d)
      (volume.restrict (cube d (m : ℝ))) (volume.restrict (cube d (ℓ : ℝ)))
      (fun a b => ‖(u + a) - (v + b)‖ ^ q) z ∂Q.prod R) = 0 := by
  letI : IsProbabilityMeasure Q := hQ.1
  letI : IsProbabilityMeasure R := hR.1
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp
    ((cube_isBounded d (m : ℝ)).union (cube_isBounded d (ℓ : ℝ)))
  have hb := Riesz.Analysis.ae_distance_le_of_concentrated
    (tupleMeanMeasure d (m ^ d) Q) (tupleMeanMeasure d (ℓ ^ d) R)
    (cube d (m : ℝ) ∪ cube d (ℓ : ℝ)) L
    (tupleMeanMeasure_concentrated d (m ^ d) Q _
      ((measurableSet_cube d (m : ℝ)).union (measurableSet_cube d (ℓ : ℝ)))
      (hQ.2.1.mono (fun x hx i => Set.mem_union_left _ (hx.2 i))))
    (tupleMeanMeasure_concentrated d (ℓ ^ d) R _
      ((measurableSet_cube d (m : ℝ)).union (measurableSet_cube d (ℓ : ℝ)))
      (hR.2.1.mono (fun y hy j => Set.mem_union_right _ (hy.2 j))))
    (fun a ha b hb => dist_eq_norm a b ▸ hL ha hb)
  rw [← tupleBalanced_tupleMeanMeasure d m Q hQ, ← tupleBalanced_tupleMeanMeasure d ℓ R hR]
  exact expected_tupleDiscrepancyCross_eq_zero d (m ^ d) (ℓ ^ d) Q R _
    (shifted_rpow_kernel_integrable d q L hq _ _ u v hb)

end Riesz.Negative
