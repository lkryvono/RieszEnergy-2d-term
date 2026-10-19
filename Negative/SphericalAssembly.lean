import Riesz.Negative.SphericalResidual
import Riesz.Negative.SphericalEnergyComparison
import Riesz.Negative.FiniteCells
import Riesz.Negative.CubeTiling
import Riesz.Asymptotics.PositiveSphericalAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Negative spherical upper assembly from actual transported cube laws and
actual residual filling. The upper target uses the independent balanced
density infimum. Its identification with the stationary Euclidean constant
is a separate reverse comparison.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry Riesz.Stationary Riesz.Asymptotics
open scoped ENNReal Topology Classical

namespace Riesz.Negative

instance negativeCellFamilyCounting_finite (a J : ℕ) (n : Fin J → ℕ)
    (x : (j : Fin J) → Fin (n j) → Rd a) :
    IsFiniteMeasure (cellFamilyCounting a J n x) := by
  letI : ∀ j : Fin J, IsFiniteMeasure (tupleCounting a (n j) (x j)) :=
    fun j => tupleCounting_isFiniteMeasure a (n j) (x j)
  exact inferInstanceAs (IsFiniteMeasure (∑ j, tupleCounting a (n j) (x j)))

def negativeTupleLawMean (a n : ℕ) (Q : Measure (Fin n → Rd a))
    [IsFiniteMeasure Q] : FiniteMeasure (Rd a) := ⟨tupleMeanMeasure a n Q, by infer_instance⟩

def negativeCellFamilyMean (a J : ℕ) (n : Fin J → ℕ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd a)) [∀ j, IsFiniteMeasure (Q j)] :
    FiniteMeasure (Rd a) := ⟨∑ j, tupleMeanMeasure a (n j) (Q j), by infer_instance⟩

def negativeCellFamilyEnergy (a J : ℕ) (n : Fin J → ℕ) (q : ℝ)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd a)) [∀ j, IsFiniteMeasure (Q j)]
    (x : (j : Fin J) → Fin (n j) → Rd a) : ℝ :=
  Riesz.Analysis.signedDiscrepancyEnergy q
    ((cellFamilyCounting a J n x).toSignedMeasure -
      (negativeCellFamilyMean a J n Q : Measure (Rd a)).toSignedMeasure)

theorem tupleMeanMeasure_univ_eq_count (a n : ℕ) (Q : Measure (Fin n → Rd a))
    [IsProbabilityMeasure Q] : tupleMeanMeasure a n Q Set.univ = n := by
  rw [tupleMeanMeasure_apply a n Q Set.univ MeasurableSet.univ]
  simp only [tupleCounting_univ, lintegral_const, measure_univ, mul_one]

theorem negativeSignedDifference_eq_rpow_cross (a : ℕ) (q L : ℝ)
    (hq : 0 < q) (hq2 : q < 2) (μ ν : Measure (Rd a))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real Set.univ = ν.real Set.univ)
    (S : Set (Rd a)) (hS : MeasurableSet S) (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L) :
    Riesz.Analysis.signedDiscrepancyEnergy q (μ.toSignedMeasure - ν.toSignedMeasure) =
      -(1 / q) * finiteDiscrepancyCross a (fun x y => ‖x - y‖ ^ q) μ ν μ ν := by
  rw [Riesz.Analysis.signedDiscrepancyEnergy_sub_toSignedMeasure q L hq hq2 μ ν
    hmass S hS hμ hν hdiam]
  unfold Riesz.Analysis.differenceKernelQuadratic finiteDiscrepancyCross
  rw [Riesz.Analysis.integral_symmetric_kernel (fun x y : Rd a => ‖x - y‖ ^ q)
    (fun x y => congrArg (fun r : ℝ => r ^ q) (norm_sub_rev x y)) ν μ]
  simp only [K_s, neg_neg, div_neg, integral_neg, integral_div]
  ring

/-- Actual signed-energy additivity on the product sample space. The means
are the actual tuple means; every off-diagonal ordered cell pair cancels. -/
theorem negativeCellFamily_expected_energy (a J : ℕ) (n : Fin J → ℕ) (q : ℝ)
    (hq : 0 < q) (hq2 : q < 2)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd a)) [∀ j, IsProbabilityMeasure (Q j)]
    (S : Set (Rd a)) (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hQ : ∀ j, ∀ᵐ x ∂Q j, ∀ i, x i ∈ S) :
    Integrable (negativeCellFamilyEnergy a J n q Q) (Measure.pi Q) ∧
      (∫ x, negativeCellFamilyEnergy a J n q Q x ∂Measure.pi Q) =
        ∑ j, ∫ x, negativeTupleSignedEnergy a (n j) q (negativeTupleLawMean a (n j) (Q j)) x ∂Q j := by
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp hbounded
  have hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L :=
    fun x hx y hy => dist_eq_norm x y ▸ hL hx hy
  have hν (j : Fin J) : tupleMeanMeasure a (n j) (Q j) Sᶜ = 0 :=
    tupleMeanMeasure_concentrated a (n j) (Q j) S hS (hQ j)
  have hνsum : (negativeCellFamilyMean a J n Q : Measure (Rd a)) Sᶜ = 0 := by
    simp only [negativeCellFamilyMean, FiniteMeasure.toMeasure_mk, Measure.finsetSum_apply, hν, Finset.sum_const_zero]
  have hmassν : (negativeCellFamilyMean a J n Q : Measure (Rd a)) Set.univ =
      (∑ j, n j : ℕ) := by
    simp only [negativeCellFamilyMean, FiniteMeasure.toMeasure_mk, Measure.finsetSum_apply, tupleMeanMeasure_univ_eq_count,
      Nat.cast_sum]
  have hInt (μ ν : Measure (Rd a)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0) :
      Integrable (fun p : Rd a × Rd a => ‖p.1 - p.2‖ ^ q) (μ.prod ν) :=
    Riesz.Analysis.integrable_rpow_distance q L hq.le μ ν
      (Riesz.Analysis.ae_distance_le_of_concentrated μ ν S L hμ hν hdiam)
  have hk := fun i j : Fin J => independentTuple_rpow_kernel_integrable a (n i) (n j)
    q hq.le (Q i) (Q j) S hS hbounded (hQ i) (hQ j)
  have hself := fun i : Fin J => tupleSelf_rpow_cross_integrable a (n i) q hq.le
    (Q i) S hS hbounded (hQ i)
  have hgood : ∀ᵐ x ∂Measure.pi Q, ∀ j i, x j i ∈ S :=
    ae_all_iff.mpr (fun j => ae_of_ae_map (measurable_pi_apply j).aemeasurable
      ((measurePreserving_eval Q j).map_eq.symm ▸ hQ j))
  have heq : ∀ᵐ x ∂Measure.pi Q, negativeCellFamilyEnergy a J n q Q x =
      -(1 / q) * cellFamilyCrossSum a J n Q (fun x y => ‖x - y‖ ^ q) x := by
    filter_upwards [hgood] with x hx
    have hμ := cellFamilyCounting_concentrated a J n x S hS hx
    rw [negativeCellFamilyEnergy,
      negativeSignedDifference_eq_rpow_cross a q L hq hq2 _ _
        (congrArg ENNReal.toReal ((cellFamilyCounting_univ a J n x).trans hmassν.symm))
        S hS hμ hνsum hdiam]
    exact congrArg (fun r : ℝ => -(1 / q) * r)
      (cellFamily_rpow_crossSum_eq a J n q hq.le Q S hS hbounded hQ x hx)
  have hselfeq (j : Fin J) : ∀ᵐ x ∂Q j,
      negativeTupleSignedEnergy a (n j) q (negativeTupleLawMean a (n j) (Q j)) x =
        -(1 / q) * tupleDiscrepancyCross a (n j) (n j)
          (tupleMeanMeasure a (n j) (Q j)) (tupleMeanMeasure a (n j) (Q j))
          (fun x y => ‖x - y‖ ^ q) (x, x) := by
    filter_upwards [hQ j] with x hx
    letI := tupleCounting_isFiniteMeasure a (n j) x
    have hμ := (tupleCounting_compl_eq_zero_iff a (n j) x S hS).mpr hx
    change Riesz.Analysis.signedDiscrepancyEnergy q
      ((tupleCounting a (n j) x).toSignedMeasure - (tupleMeanMeasure a (n j) (Q j)).toSignedMeasure) = _
    rw [negativeSignedDifference_eq_rpow_cross a q L hq hq2 _ _
        (congrArg ENNReal.toReal ((tupleCounting_univ a (n j) x).trans
          (tupleMeanMeasure_univ_eq_count a (n j) (Q j)).symm)) S hS hμ (hν j) hdiam,
      finiteDiscrepancyCross_eq_tuple a (n j) (n j) _ x x _ _
        (hInt _ _ hμ hμ) (hInt _ _ hμ (hν j)) (hInt _ _ (hν j) hμ)]
  have hcross : Integrable (cellFamilyCrossSum a J n Q (fun x y => ‖x - y‖ ^ q))
      (Measure.pi Q) :=
    integrable_finsetSum _ (fun ij _ => cellFamily_cross_term_integrable a J n Q _ hk hself ij)
  refine ⟨(hcross.const_mul (-(1 / q))).congr (Filter.EventuallyEq.symm heq), ?_⟩
  rw [integral_congr_ae heq, integral_const_mul,
    cellFamilyCrossSum_expectation a J n Q _ hk hself, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.EventuallyEq.symm (hselfeq j)))

/-- Reindex an actual independent family as an exact-N tuple. There are no
energy hypotheses: the expected energy is derived by independent cross cancellation. -/
theorem exists_negativeIndependentTuple (a J N : ℕ) (n : Fin J → ℕ) (q L : ℝ)
    (hq : 0 < q) (hq2 : q < 2)
    (Q : (j : Fin J) → Measure (Fin (n j) → Rd a)) (hprob : ∀ j, IsProbabilityMeasure (Q j))
    (ν : Fin J → FiniteMeasure (Rd a)) (νfull : FiniteMeasure (Rd a))
    (hmean : ∀ j, tupleMeanMeasure a (n j) (Q j) = (ν j : Measure (Rd a)))
    (hmeansum : (∑ j, (ν j : Measure (Rd a))) = (νfull : Measure (Rd a)))
    (B : Fin J → Set (Rd a)) (hdisjoint : Pairwise (fun i j => Disjoint (B i) (B j)))
    (S : Set (Rd a)) (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hsub : ∀ j, B j ⊆ S) (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L)
    (hQ : ∀ j, ∀ᵐ x ∂Q j, Function.Injective x ∧ ∀ i, x i ∈ B j)
    (hcount : ∑ j, n j = N) (hνmass : (νfull : Measure (Rd a)) Set.univ = N) :
    ∃ QT : Measure (Fin N → Rd a), IsProbabilityMeasure QT ∧
      (∀ᵐ x ∂QT, Function.Injective x ∧ ∀ i, x i ∈ S) ∧
      tupleMeanMeasure a N QT = (νfull : Measure (Rd a)) ∧
      Integrable (negativeTupleSignedEnergy a N q νfull) QT ∧
      (∫ x, negativeTupleSignedEnergy a N q νfull x ∂QT) =
        ∑ j, ∫ x, negativeTupleSignedEnergy a (n j) q (ν j) x ∂Q j := by
  letI : ∀ j, IsProbabilityMeasure (Q j) := hprob
  let P := Measure.pi Q
  let F := cellFamilyCounting a J n
  have hF := measurable_cellFamilyCounting a J n
  have hsource := cellFamily_joint_good a J n Q B hQ
  have hQsupport : ∀ j, ∀ᵐ x ∂Q j, ∀ i, x i ∈ S :=
    fun j => (hQ j).mono (fun x hx i => hsub j (hx.2 i))
  have hgood : ∀ᵐ x ∂P, (IsSimpleConfiguration a (F x) ∧ F x Set.univ = (N : ℝ≥0∞)) ∧
      F x Sᶜ = 0 := by
    filter_upwards [hsource] with x hx
    exact ⟨⟨cellFamilyCounting_simple a J n x (cellFamilySites_injective a J n x B hdisjoint hx),
      (cellFamilyCounting_univ a J n x).trans (congrArg Nat.cast hcount)⟩,
      cellFamilyCounting_concentrated a J n x S hS (fun j i => hsub j ((hx j).2 i))⟩
  have htotalmean : (∑ j, tupleMeanMeasure a (n j) (Q j)) = (νfull : Measure (Rd a)) := by
    simp only [hmean]
    exact hmeansum
  have hmeanF (D : Set (Rd a)) (hD : MeasurableSet D) :
      (∫⁻ x, F x D ∂P) = (νfull : Measure (Rd a)) D := by
    rw [← lintegral_map (Measure.measurable_coe hD) hF]
    exact (cellFamilyCountingLaw_mean a J n Q D hD).trans
      (congrArg (fun μ : Measure (Rd a) => μ D) htotalmean)
  have hνsupport : (νfull : Measure (Rd a)) Sᶜ = 0 := by
    rw [← hmeanF Sᶜ hS.compl]
    simpa only [lintegral_zero] using lintegral_congr_ae (hgood.mono (fun x hx => hx.2))
  obtain ⟨QT, hQT, hQTgood, hQTmean, hQTi, heq⟩ :=
    exists_finiteTupleRealization_of_bounded_marks P a N q L hq hq2 F hF νfull hνmass
      S hS hνsupport hdiam hgood (fun D hD => (hmeanF D hD).trans
        (FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure νfull D).symm)
  have hνeq (j : Fin J) : negativeTupleLawMean a (n j) (Q j) = ν j :=
    FiniteMeasure.toMeasure_injective (hmean j)
  have hνfull : negativeCellFamilyMean a J n Q = νfull :=
    FiniteMeasure.toMeasure_injective htotalmean
  have hadd := (negativeCellFamily_expected_energy a J n q hq hq2 Q S hS hbounded hQsupport).2
  have hadd' : (∫ x, Riesz.Analysis.signedDiscrepancyEnergy q
      ((F x).toSignedMeasure - (νfull : Measure (Rd a)).toSignedMeasure) ∂P) =
      ∑ j, ∫ x, negativeTupleSignedEnergy a (n j) q (ν j) x ∂Q j := by
    simpa only [negativeCellFamilyEnergy, hνfull, hνeq] using hadd
  exact ⟨QT, hQT, hQTgood, hQTmean, hQTi, heq.trans hadd'⟩

def negativeMainCellErrorDensity (d m : ℕ) (q : ℝ) : ℝ :=
  12 * (Real.sqrt d * (m : ℝ)) ^ q * (m : ℝ) ^ d / q

theorem negativeMainCellErrorDensity_nonneg (d m : ℕ) (q : ℝ) (hq : 0 < q) :
    0 ≤ negativeMainCellErrorDensity d m q := by
  unfold negativeMainCellErrorDensity
  positivity

theorem negativePhysicalCellTuple_certificate (d m N : ℕ) (q δ R : ℝ)
    (hm : 0 < m) (hq : 0 < q) (hq2 : q < 2)
    (hδ0 : 0 ≤ δ) (hδh : δ ≤ 1 / 2) (hR : 0 < R) (hRN : R ^ d * omega d = N)
    (D : Set (Rd d)) (F : Rd d → Sphere d) (hD : MeasurableSet D)
    (hF : ContinuousOn F D) (hFi : Set.InjOn F D)
    (harea : ∀ E, MeasurableSet E → E ⊆ D → sphericalMeasure d (F '' E) =
      (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E)
    (z : GridIndex d) (hcell : latticeCell d ((m : ℝ) / R) 0 z ⊆ D)
    (hmetric : ∀ x ∈ D, ∀ y ∈ D,
      (1 - δ) * ‖x - y‖ ≤ chord d (F x) (F y) ∧ chord d (F x) (F y) ≤ (1 + δ) * ‖x - y‖)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    let C := F '' latticeCell d ((m : ℝ) / R) 0 z
    let T := negativePhysicalCellMap d m R D F z
    let QT := Q.map (negativeTransportTuple d (d + 1) (m ^ d) T)
    IsProbabilityMeasure QT ∧
      (∀ᵐ x ∂QT, Function.Injective x ∧ ∀ i, x i ∈ (fun y : Sphere d => R • y.val) '' C) ∧
      tupleMeanMeasure (d + 1) (m ^ d) QT = (residualPhysicalBackground d R C : Measure (Rd (d + 1))) ∧
      Integrable (negativeTupleSignedEnergy (d + 1) (m ^ d) q (residualPhysicalBackground d R C)) QT ∧
      (∫ x, negativeTupleSignedEnergy (d + 1) (m ^ d) q (residualPhysicalBackground d R C) x ∂QT) ≤
        (∫ x, Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x) ∂Q) +
          δ * (m : ℝ) ^ d * negativeMainCellErrorDensity d m q := by
  dsimp only
  let C := F '' latticeCell d ((m : ℝ) / R) 0 z
  let T := negativePhysicalCellMap d m R D F z
  let QT := Q.map (negativeTransportTuple d (d + 1) (m ^ d) T)
  let νT := (negativeCubeBackground d m).map T
  have hTm := measurable_negativePhysicalCellMap d m R D F hD hF z
  have hmT : tupleMeanMeasure (d + 1) (m ^ d) QT = (νT : Measure (Rd (d + 1))) := by
    rw [tupleMeanMeasure_negativeTransportTuple d (d + 1) (m ^ d) T hTm,
      tupleBalanced_tupleMeanMeasure d m Q hQ]
    rfl
  have hmC : tupleMeanMeasure (d + 1) (m ^ d) QT =
      (residualPhysicalBackground d R C : Measure (Rd (d + 1))) := by
    simpa only [residualPhysicalBackground, FiniteMeasure.toMeasure_mk, hRN] using
      negativePhysicalCellTuple_mean d m N R hR hRN D F hD hF hFi harea z hcell Q hQ
  have hνeq : νT = residualPhysicalBackground d R C :=
    FiniteMeasure.toMeasure_injective (hmT.symm.trans hmC)
  dsimp only [νT, T] at hνeq
  have hcost := negativePhysicalCellTuple_expected_energy_le d m q δ R hm hq hq2 hδ0 hδh hR
    D F hD hF z hcell hmetric Q hQ
  have hgood := negativePhysicalCellTuple_good d m R hR D F hD hF hFi z hcell Q hQ
  have hpatch : T '' cube d (m : ℝ) ⊆ (fun y : Sphere d => R • y.val) '' C := by
    rintro x ⟨u, hu, rfl⟩
    refine ⟨F (sphericalCellAffine d (m : ℝ) R z u), ?_, ?_⟩
    · exact ⟨_, (sphericalCellAffine_image_cube d (m : ℝ) R hR z) ▸
        Set.mem_image_of_mem (sphericalCellAffine d (m : ℝ) R z) hu, rfl⟩
    · change R • (F (sphericalCellAffine d (m : ℝ) R z u)).val =
        R • sphericalCellMap d (m : ℝ) R D F z u
      rw [sphericalCellMap_eqOn d (m : ℝ) R hR z D F hcell hu]
  refine ⟨negativePhysicalCellTuple_probability d m R D F hD hF z Q hQ,
    hgood.mono (fun x hx => ⟨hx.1, fun i => hpatch (hx.2 i)⟩), hmC, ?_, ?_⟩
  · simpa only [hνeq] using hcost.1
  · have herr : 12 * δ * (Real.sqrt d * (m : ℝ)) ^ q * ((m ^ d : ℕ) : ℝ) ^ 2 / q =
        δ * (m : ℝ) ^ d * negativeMainCellErrorDensity d m q := by
      simp only [negativeMainCellErrorDensity, Nat.cast_pow]
      ring
    simpa only [hνeq, herr] using hcost.2

theorem residualPhysicalBackground_mass_formula (d N : ℕ) (R : ℝ)
    (hRN : R ^ d * omega d = N) (C : Set (Sphere d)) :
    (residualPhysicalBackground d R C : Measure (Rd (d + 1))) Set.univ =
      ENNReal.ofReal (N : ℝ) * sphericalMeasure d C := by
  change ((ENNReal.ofReal (R ^ d * omega d) • (sphericalMeasure d).restrict C).map
    (fun p : Sphere d => R • p.val)) Set.univ = _
  rw [hRN, Measure.map_apply
    (show Measurable (fun p : Sphere d => R • p.val) from continuous_subtype_val.measurable.const_smul R)
    MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]

theorem residualPhysicalBackground_partition (d J : ℕ) (R : ℝ)
    (C : Fin J → Set (Sphere d)) (hC : ∀ i, MeasurableSet (C i))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j))) :
    (∑ i, (residualPhysicalBackground d R (C i) : Measure (Rd (d + 1)))) +
      (residualPhysicalBackground d R (⋃ i, C i)ᶜ : Measure (Rd (d + 1))) =
        (negativeSphericalBackground d R : Measure (Rd (d + 1))) := by
  have hr : (∑ i, (sphericalMeasure d).restrict (C i)) +
      (sphericalMeasure d).restrict (⋃ i, C i)ᶜ = sphericalMeasure d := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisjoint hC,
      Measure.restrict_add_restrict_compl (MeasurableSet.iUnion hC)]
  have hm : Measurable (fun p : Sphere d => R • p.val) :=
    continuous_subtype_val.measurable.const_smul R
  have ht := congrArg (fun μ : Measure (Sphere d) =>
    (ENNReal.ofReal (R ^ d * omega d) • μ).map (fun p : Sphere d => R • p.val)) hr
  rw [smul_add, Finset.smul_sum, Measure.map_add _ _ hm,
    Measure.map_finset_sum' hm.aemeasurable] at ht
  simpa only [residualPhysicalBackground, negativeSphericalBackground, FiniteMeasure.toMeasure_mk] using ht

theorem complement_cons_pairwise_disjoint {X : Type*} (J : ℕ) (C : Fin J → Set X)
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j))) :
    Pairwise (fun i j : Fin (J + 1) =>
      Disjoint (Fin.cases (motive := fun _ => Set X) (⋃ k, C k)ᶜ C i)
        (Fin.cases (motive := fun _ => Set X) (⋃ k, C k)ᶜ C j)) := by
  intro i
  refine Fin.cases ?_ (fun u => ?_) i
  · intro j
    refine Fin.cases ?_ (fun v => ?_) j
    · intro h
      exact False.elim (h rfl)
    · intro h
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact hx (Set.mem_iUnion.mpr ⟨v, hy⟩)
  · intro j
    refine Fin.cases ?_ (fun v => ?_) j
    · intro h
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact hy (Set.mem_iUnion.mpr ⟨u, hx⟩)
    · intro h
      exact hdisjoint (fun he => h (congrArg Fin.succ he))

theorem physicalSphereMap_injective (d : ℕ) (R : ℝ) (hR : 0 < R) :
    Function.Injective (fun x : Sphere d => R • x.val) := by
  intro x y hxy
  apply Subtype.val_injective
  have he := congrArg (fun z : Rd (d + 1) => R⁻¹ • z) hxy
  simpa only [smul_smul, inv_mul_cancel₀ hR.ne', one_smul] using he

theorem physicalSphereImages_pairwise_disjoint (d J : ℕ) (R : ℝ) (hR : 0 < R)
    (C : Fin J → Set (Sphere d)) (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j))) :
    Pairwise (fun i j => Disjoint ((fun x : Sphere d => R • x.val) '' C i)
      ((fun x : Sphere d => R • x.val) '' C j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
  have hvu := physicalSphereMap_injective d R hR he
  subst v
  exact Set.disjoint_left.mp (hdisjoint hij) hu hv

theorem negativeSphericalPackingScalar (d : ℕ) (q r R ω N J n M c H C δ eta E : ℝ)
    (hN : 0 < N) (hω : 0 < ω) (hRN : R ^ d * ω = N)
    (hpacking : J * n ≤ N) (hcost : 0 ≤ c + δ * H)
    (hC : 0 ≤ C) (hr : 0 < r) (hM : M ≤ eta * N)
    (henergy : E ≤ J * n * (c + δ * H) + C * (r ^ q * M + R ^ d * r ^ (q - (d : ℝ)))) :
    E / N ≤ c + δ * H + C * r ^ q * eta + (C / ω) * r ^ (q - (d : ℝ)) := by
  have hmain := mul_le_mul_of_nonneg_right hpacking hcost
  have hres := mul_le_mul_of_nonneg_left hM
    (mul_nonneg hC (Real.rpow_nonneg hr.le q))
  have hbulk : C * (R ^ d * r ^ (q - (d : ℝ))) =
      N * ((C / ω) * r ^ (q - (d : ℝ))) := by
    rw [← hRN]
    field_simp [hω.ne']
  apply (div_le_iff₀ hN).2
  nlinarith only [henergy, hmain, hres, hbulk]

/-- Actual main-cell transport plus residual filling, on a finite chart
family. The residual law is produced from its Borel mask and integer mass.
Neither an assembled law nor an assembled energy bound is an input. -/
theorem exists_negativeSphericalTuple_of_cells (d m N J : ℕ) (hd : 2 ≤ d)
    (A : ResidualSphericalAtlas d) (q δ r R eta : ℝ) (hm : 0 < m) (hN : 0 < N)
    (hq : 0 < q) (hq2 : q < 2) (hδ0 : 0 ≤ δ) (hδh : δ ≤ 1 / 2)
    (hr : 1 ≤ r) (hrR : r ≤ R) (hR : 0 < R) (hRN : R ^ d * omega d = N)
    (D : Fin J → Set (Rd d)) (F : Fin J → Rd d → Sphere d) (z : Fin J → GridIndex d)
    (hD : ∀ j, MeasurableSet (D j)) (hF : ∀ j, ContinuousOn (F j) (D j))
    (hFi : ∀ j, Set.InjOn (F j) (D j))
    (harea : ∀ j E, MeasurableSet E → E ⊆ D j → sphericalMeasure d (F j '' E) =
      (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E)
    (hcell : ∀ j, latticeCell d ((m : ℝ) / R) 0 (z j) ⊆ D j)
    (hmetric : ∀ j, ∀ x ∈ D j, ∀ y ∈ D j,
      (1 - δ) * ‖x - y‖ ≤ chord d (F j x) (F j y) ∧
        chord d (F j x) (F j y) ≤ (1 + δ) * ‖x - y‖)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (F i '' latticeCell d ((m : ℝ) / R) 0 (z i))
      (F j '' latticeCell d ((m : ℝ) / R) 0 (z j))))
    (hmiss : sphericalMeasure d (⋃ j, F j '' latticeCell d ((m : ℝ) / R) 0 (z j))ᶜ < ENNReal.ofReal eta)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    ∃ QT : Measure (Fin N → Rd (d + 1)), IsProbabilityMeasure QT ∧
      (∀ᵐ x ∂QT, Function.Injective x ∧ ∀ i, ‖x i‖ = R) ∧
      tupleMeanMeasure (d + 1) N QT = (negativeSphericalBackground d R : Measure (Rd (d + 1))) ∧
      Integrable (negativeTupleSignedEnergy (d + 1) N q (negativeSphericalBackground d R)) QT ∧
      (∫ x, negativeTupleSignedEnergy (d + 1) N q (negativeSphericalBackground d R) x ∂QT) / N ≤
        (∫ x, Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x) ∂Q) / (m : ℝ) ^ d +
          δ * negativeMainCellErrorDensity d m q +
          residualSphericalFillingConstant d A q * r ^ q * eta +
          (residualSphericalFillingConstant d A q / omega d) * r ^ (q - (d : ℝ)) := by
  let C : Fin J → Set (Sphere d) := fun j => F j '' latticeCell d ((m : ℝ) / R) 0 (z j)
  let U : Set (Sphere d) := (⋃ j, C j)ᶜ
  let ν : Fin J → FiniteMeasure (Rd (d + 1)) := fun j => residualPhysicalBackground d R (C j)
  let Qmain := fun j : Fin J => Q.map (negativeTransportTuple d (d + 1) (m ^ d)
    (negativePhysicalCellMap d m R (D j) (F j) (z j)))
  have hC (j : Fin J) : MeasurableSet (C j) :=
    (latticeCell_measurable d _ 0 _).image_of_continuousOn_injOn
      ((hF j).mono (hcell j)) ((hFi j).mono (hcell j))
  have hU : MeasurableSet U := (MeasurableSet.iUnion hC).compl
  have hmain (j : Fin J) := negativePhysicalCellTuple_certificate d m N q δ R hm hq hq2
    hδ0 hδh hR hRN (D j) (F j) (hD j) (hF j) (hFi j) (harea j) (z j) (hcell j) (hmetric j) Q hQ
  letI : ∀ j, IsProbabilityMeasure (Qmain j) := fun j => (hmain j).1
  have hνmass (j : Fin J) : (ν j : Measure (Rd (d + 1))) Set.univ = (m ^ d : ℕ) :=
    ((congrArg (fun μ : Measure (Rd (d + 1)) => μ Set.univ) (hmain j).2.2.1).symm).trans
      (tupleMeanMeasure_univ_eq_count (d + 1) (m ^ d) (Qmain j))
  have hpart := residualPhysicalBackground_partition d J R C hC hdisjoint
  have hcountmass : ((J * m ^ d : ℕ) : ℝ≥0∞) +
      (residualPhysicalBackground d R U : Measure (Rd (d + 1))) Set.univ = N := by
    calc
      _ = ((∑ j, (ν j : Measure (Rd (d + 1)))) +
          (residualPhysicalBackground d R U : Measure (Rd (d + 1)))) Set.univ := by
        simp only [Measure.add_apply, Measure.finsetSum_apply, hνmass,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      _ = (negativeSphericalBackground d R : Measure (Rd (d + 1))) Set.univ :=
        congrArg (fun μ : Measure (Rd (d + 1)) => μ Set.univ) hpart
      _ = N := negativeSphericalBackground_mass d N R hRN
  have hreal := congrArg ENNReal.toReal hcountmass
  rw [ENNReal.toReal_add (by finiteness) (measure_ne_top _ _),
    ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hreal
  have hpacking : J * m ^ d ≤ N := by
    exact_mod_cast (show ((J * m ^ d : ℕ) : ℝ) ≤ (N : ℝ) by
      nlinarith only [hreal, ENNReal.toReal_nonneg
        (a := (residualPhysicalBackground d R U : Measure (Rd (d + 1))) Set.univ)])
  let M := N - J * m ^ d
  have hM : (residualPhysicalBackground d R U : Measure (Rd (d + 1))) Set.univ = M := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by finiteness)).mp
    rw [ENNReal.toReal_natCast, Nat.cast_sub hpacking]
    linarith only [hreal]
  have hMarea : (M : ℝ) = (N : ℝ) * (sphericalMeasure d).real U := by
    have hh := congrArg ENNReal.toReal hM
    rw [residualPhysicalBackground_mass_formula d N R hRN U, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Nat.cast_nonneg N), ENNReal.toReal_natCast] at hh
    exact hh.symm
  have hMsmall : (M : ℝ) ≤ eta * (N : ℝ) := by
    have hmσ : (sphericalMeasure d).real U < eta := ENNReal.toReal_lt_of_lt_ofReal hmiss
    rw [hMarea]
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  obtain ⟨Qres, hresprob, hresgood, hresmean, hresi, hrescost⟩ :=
    exists_residualSphericalFilling_tuple d hd A q r R hq hq2 hr hrR hR U hU M hM
  let counts : Fin (J + 1) → ℕ := Fin.cases M (fun _ => m ^ d)
  let laws : (i : Fin (J + 1)) → Measure (Fin (counts i) → Rd (d + 1)) :=
    fun i => Fin.cases (motive := fun i => Measure (Fin (counts i) → Rd (d + 1)))
      Qres (fun j => Qmain j) i
  let means : Fin (J + 1) → FiniteMeasure (Rd (d + 1)) :=
    Fin.cases (residualPhysicalBackground d R U) ν
  let patches : Fin (J + 1) → Set (Sphere d) := Fin.cases U C
  let B : Fin (J + 1) → Set (Rd (d + 1)) :=
    fun i => (fun x : Sphere d => R • x.val) '' patches i
  let Sph : Set (Rd (d + 1)) := {x | ‖x‖ = R}
  have hprob (i : Fin (J + 1)) : IsProbabilityMeasure (laws i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hresprob
    · exact (hmain j).1
  have hgood (i : Fin (J + 1)) : ∀ᵐ x ∂laws i, Function.Injective x ∧ ∀ j, x j ∈ B i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hresgood
    · exact (hmain j).2.1
  have hmean (i : Fin (J + 1)) : tupleMeanMeasure (d + 1) (counts i) (laws i) =
      (means i : Measure (Rd (d + 1))) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [laws, means, counts, Fin.cases_zero] using hresmean
    · simpa only [laws, means, counts, Fin.cases_succ] using (hmain j).2.2.1
  have hmeansum : (∑ i, (means i : Measure (Rd (d + 1)))) =
      (negativeSphericalBackground d R : Measure (Rd (d + 1))) := by
    simpa only [Fin.sum_univ_succ, means, Fin.cases_zero, Fin.cases_succ, add_comm] using hpart
  have hcount : ∑ i, counts i = N := by
    simpa only [Fin.sum_univ_succ, counts, Fin.cases_zero, Fin.cases_succ,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, M] using Nat.sub_add_cancel hpacking
  have hBdisjoint : Pairwise (fun i j => Disjoint (B i) (B j)) :=
    physicalSphereImages_pairwise_disjoint d (J + 1) R hR patches
      (complement_cons_pairwise_disjoint J C hdisjoint)
  have hSph : MeasurableSet Sph := measurableSet_eq_fun continuous_norm.measurable measurable_const
  have hSphbounded : Bornology.IsBounded Sph := by
    simpa only [Metric.sphere, dist_zero_right] using
      (Metric.isBounded_sphere : Bornology.IsBounded (Metric.sphere (0 : Rd (d + 1)) R))
  have hBsub (j : Fin (J + 1)) : B j ⊆ Sph := by
    rintro x ⟨y, hy, rfl⟩
    simp only [Sph, Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hR, y.property, mul_one]
  have hdiam (x : Rd (d + 1)) (hx : x ∈ Sph) (y : Rd (d + 1)) (hy : y ∈ Sph) : ‖x - y‖ ≤ 2 * R := by
    change ‖x‖ = R at hx
    change ‖y‖ = R at hy
    exact (norm_sub_le x y).trans (by rw [hx, hy]; linarith)
  obtain ⟨QT, hQT, hQTgood, hQTmean, hQTi, heq⟩ :=
    exists_negativeIndependentTuple (d + 1) (J + 1) N counts q (2 * R) hq hq2 laws hprob means
      (negativeSphericalBackground d R) hmean hmeansum B hBdisjoint Sph hSph hSphbounded hBsub
      hdiam hgood hcount (negativeSphericalBackground_mass d N R hRN)
  let E0 := ∫ x, Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x) ∂Q
  let c := E0 / (m : ℝ) ^ d
  let H := negativeMainCellErrorDensity d m q
  let Cres := residualSphericalFillingConstant d A q
  have hcostsum : (∑ i, ∫ x, negativeTupleSignedEnergy (d + 1) (counts i) q (means i) x ∂laws i) ≤
      (J : ℝ) * (E0 + δ * (m : ℝ) ^ d * H) + Cres * (r ^ q * M + R ^ d * r ^ (q - (d : ℝ))) := by
    rw [Fin.sum_univ_succ]
    simp only [counts, laws, means, Fin.cases_zero, Fin.cases_succ]
    have hmaincost := Finset.sum_le_sum (s := Finset.univ) (fun j hj => (hmain j).2.2.2.2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hmaincost
    convert add_le_add hrescost hmaincost using 1 <;> first | rfl | ring
  have hE0 : 0 ≤ E0 := integral_nonneg_of_ae ((hQ.2.1).mono (fun x hx =>
    (tuple_signedDiscrepancyEnergy_gaussian d m q (by omega) hq hq2 x hx.2).2))
  have hc : 0 ≤ c := div_nonneg hE0 (by positivity)
  have hH := negativeMainCellErrorDensity_nonneg d m q hq
  have hqd : q < (d : ℝ) := hq2.trans_le (Nat.cast_le.mpr hd)
  have hCres : 0 ≤ Cres := (residualSphericalFillingConstant_pos d A q hq hqd).le
  have hE0eq : E0 = (m : ℝ) ^ d * c := by
    dsimp only [c]
    field_simp [(pow_pos (Nat.cast_pos.mpr hm : (0 : ℝ) < m) d).ne']
  have hcost : (∫ x, negativeTupleSignedEnergy (d + 1) N q (negativeSphericalBackground d R) x ∂QT) ≤
      (J : ℝ) * (m : ℝ) ^ d * (c + δ * H) + Cres * (r ^ q * M + R ^ d * r ^ (q - (d : ℝ))) := by
    rw [heq]
    convert hcostsum using 1
    rw [hE0eq]
    ring
  refine ⟨QT, hQT, hQTgood, hQTmean, hQTi, ?_⟩
  exact negativeSphericalPackingScalar d q r R (omega d) N J ((m : ℝ) ^ d) M c H Cres δ eta _
    (Nat.cast_pos.mpr hN) (omega_pos d) hRN (by exact_mod_cast hpacking)
    (add_nonneg hc (mul_nonneg hδ0 hH)) hCres (lt_of_lt_of_le zero_lt_one hr) hMsmall hcost

theorem negativeSphericalTuple_expected_optimal_le (d N : ℕ) (hd : 2 ≤ d)
    (q R : ℝ) (hq : 0 < q) (hq2 : q < 2) (hR : 0 < R)
    (hRN : R ^ d * omega d = N) (QT : Measure (Fin N → Rd (d + 1)))
    [IsProbabilityMeasure QT]
    (hgood : ∀ᵐ x ∂QT, Function.Injective x ∧ ∀ i, ‖x i‖ = R)
    (hi : Integrable (negativeTupleSignedEnergy (d + 1) N q (negativeSphericalBackground d R)) QT) :
    R ^ q / (N : ℝ) * (E_K d (-q) N - V_K d (-q) * (N : ℝ) ^ 2) ≤
      (∫ x, negativeTupleSignedEnergy (d + 1) N q (negativeSphericalBackground d R) x ∂QT) / N := by
  have hp : ∀ᵐ x ∂QT, R ^ q * (E_K d (-q) N - V_K d (-q) * (N : ℝ) ^ 2) ≤
      negativeTupleSignedEnergy (d + 1) N q (negativeSphericalBackground d R) x := by
    filter_upwards [hgood] with x hx
    exact negativePhysicalSphereTuple_optimal_le d N hd q R hq hq2 hR hRN x hx.1 hx.2
  have hh := integral_mono_ae (integrable_const _) hi hp
  simp only [integral_const, probReal_univ, one_smul] at hh
  simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg N)

/-- All-N upper estimate from a fixed actual balanced tuple law. The finite
retained chart family is chosen separately for each sufficiently large N. -/
theorem eventually_negativeSphericalUpper_of_fixed_tuple (d m : ℕ) (hd : 2 ≤ d)
    (A : ResidualSphericalAtlas d) (q r δ eta : ℝ) (hm : 0 < m)
    (hq : 0 < q) (hq2 : q < 2) (hr : 1 ≤ r)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (heta : 0 < eta)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    ∀ᶠ N : ℕ in atTop, Riesz.Asymptotics.scaledOptimalKernelEnergy d (-q) N ≤
      (∫ x, Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x) ∂Q) / (m : ℝ) ^ d +
        δ * negativeMainCellErrorDensity d m q +
        residualSphericalFillingConstant d A q * r ^ q * eta +
        (residualSphericalFillingConstant d A q / omega d) * r ^ (q - (d : ℝ)) := by
  have hδ1 : δ < 1 := by linarith
  filter_upwards [eventually_exists_positiveSphericalGrid d hd (m : ℝ) δ eta
    (Nat.cast_pos.mpr hm) hδ hδ1 heta,
    (sphericalRadius_tendsto_atTop d (by omega)).eventually (eventually_ge_atTop r),
    eventually_gt_atTop (0 : ℕ)] with N hgrid hRlarge hN
  obtain ⟨k, D, F, I, hD, hdisjoint, harea, hmetric, hcell, hmiss⟩ := hgrid
  let e : Fin (Fintype.card (Σ i, ↥(I i))) ≃ (Σ i, ↥(I i)) :=
    (Fintype.equivFin (Σ i, ↥(I i))).symm
  have hcell' (j : Fin (Fintype.card (Σ i, ↥(I i)))) :
      latticeCell d ((m : ℝ) / sphericalRadius d N) 0 (e j).2.val ⊆ D (e j).1 :=
    subset_closure.trans (hcell (e j).1 (e j).2.val (e j).2.property)
  have hdisjoint' : Pairwise (fun i j => Disjoint
      (F (e i).1 '' latticeCell d ((m : ℝ) / sphericalRadius d N) 0 (e i).2.val)
      (F (e j).1 '' latticeCell d ((m : ℝ) / sphericalRadius d N) 0 (e j).2.val)) :=
    fun i j hij => retained_spherical_cells_pairwise_disjoint d k _
      (div_pos (Nat.cast_pos.mpr hm) (sphericalRadius_pos d N hN)) D F I
      (fun i => (hD i).2.2.2) (fun i z hz => subset_closure.trans (hcell i z hz)) hdisjoint
      (fun h => hij (e.injective h))
  have hunion : (⋃ j, F (e j).1 '' latticeCell d ((m : ℝ) / sphericalRadius d N) 0 (e j).2.val) =
      ⋃ i, ⋃ z ∈ I i, F i '' latticeCell d ((m : ℝ) / sphericalRadius d N) 0 z := by
    rw [e.surjective.iUnion_comp (fun a : Σ i, ↥(I i) =>
      F a.1 '' latticeCell d ((m : ℝ) / sphericalRadius d N) 0 a.2.val), Set.iUnion_sigma]
    simp only [Set.iUnion_subtype]
  obtain ⟨QT, hQT, hQTgood, hQTmean, hQTi, hbound⟩ :=
    exists_negativeSphericalTuple_of_cells d m N (Fintype.card (Σ i, ↥(I i))) hd A q δ r
      (sphericalRadius d N) eta hm hN hq hq2 hδ.le hδh hr hRlarge (sphericalRadius_pos d N hN)
      (sphericalRadius_area_normalization d N (by omega))
      (fun j => D (e j).1) (fun j => F (e j).1) (fun j => (e j).2.val)
      (fun j => (hD (e j).1).1.measurableSet) (fun j => (hD (e j).1).2.2.1)
      (fun j => (hD (e j).1).2.2.2) (fun j => harea (e j).1) hcell'
      (fun j => hmetric (e j).1) hdisjoint' (by simpa only [hunion] using hmiss) Q hQ
  letI : IsProbabilityMeasure QT := hQT
  have hopt := negativeSphericalTuple_expected_optimal_le d N hd q (sphericalRadius d N)
    hq hq2 (sphericalRadius_pos d N hN) (sphericalRadius_area_normalization d N (by omega))
    QT hQTgood hQTi
  have hopt' : Riesz.Asymptotics.scaledOptimalKernelEnergy d (-q) N ≤
      (∫ x, negativeTupleSignedEnergy (d + 1) N q
        (negativeSphericalBackground d (sphericalRadius d N)) x ∂QT) / N := by
    simpa only [Riesz.Asymptotics.scaledOptimalKernelEnergy, neg_neg] using hopt
  exact hopt'.trans hbound

/-- Genuine upper bound in the balanced finite-volume density. Its
identification with e(d,-q) is deliberately a separate reverse comparison. -/
theorem negative_spherical_upper_to_balanced_density (d : ℕ) (hd : 2 ≤ d)
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) :
    ∀ b : ℝ, sInf (balancedDensityValues d q) < b →
      ∀ᶠ N : ℕ in atTop, Riesz.Asymptotics.scaledOptimalKernelEnergy d (-q) N < b := by
  intro b hb
  let c0 := sInf (balancedDensityValues d q)
  let ε := (b - c0) / 8
  have hε : 0 < ε := div_pos (sub_pos.mpr hb) (by norm_num)
  obtain ⟨v, ⟨m, hm, rfl⟩, hmlt⟩ :=
    (csInf_lt_iff (balancedDensityValues_bddBelow d q hq hq2)
      (balancedDensityValues_nonempty d q)).mp (show c0 < c0 + ε by linarith)
  have hm0 : 0 < m := by omega
  have hn : 0 < (m : ℝ) ^ d := pow_pos (Nat.cast_pos.mpr hm0) d
  obtain ⟨Q, hQ, hQi, hQle, hQlt⟩ := exists_near_optimal_signed_tuple_law d m q
    (ε * (m : ℝ) ^ d) (by omega) hm0 hq hq2 (mul_pos hε hn)
  let c := (∫ x, Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x) ∂Q) / (m : ℝ) ^ d
  have hc : c < c0 + 2 * ε := by
    apply (div_lt_iff₀ hn).2
    have hmupper := (div_lt_iff₀ hn).mp hmlt
    nlinarith only [hmupper, hQlt]
  have hA : Nonempty (ResidualSphericalAtlas d) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
    exact exists_residualSphericalAtlas k
  let A := Classical.choice hA
  let Cres := residualSphericalFillingConstant d A q
  have hqd : q < (d : ℝ) := hq2.trans_le (Nat.cast_le.mpr hd)
  have hCres : 0 < Cres := residualSphericalFillingConstant_pos d A q hq hqd
  have hbulkLimit : Tendsto (fun r : ℝ => (Cres / omega d) * r ^ (q - (d : ℝ)))
      atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hqd)).const_mul (Cres / omega d)
  obtain ⟨r, hr, hbulk⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (hbulkLimit.eventually (gt_mem_nhds hε))).exists
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let eta := ε / (Cres * r ^ q + 1)
  have hdeneta : 0 < Cres * r ^ q + 1 := by positivity
  have heta : 0 < eta := div_pos hε hdeneta
  have hetaEq : (Cres * r ^ q + 1) * eta = ε := by
    dsimp only [eta]
    field_simp [hdeneta.ne']
  have hetacost : Cres * r ^ q * eta < ε := by nlinarith only [hetaEq, heta]
  let H := negativeMainCellErrorDensity d m q
  have hH : 0 ≤ H := negativeMainCellErrorDensity_nonneg d m q hq
  have hdenδ : 0 < H + 1 := by linarith
  let δ := min (1 / 4 : ℝ) (ε / (H + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hdenδ)
  have hδh : δ ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hδprod : δ * (H + 1) ≤ ε := (le_div_iff₀ hdenδ).mp (min_le_right _ _)
  have hδcost : δ * H < ε := by nlinarith only [hδprod, hδ]
  filter_upwards [eventually_negativeSphericalUpper_of_fixed_tuple d m hd A q r δ eta hm0
    hq hq2 hr hδ hδh heta Q hQ] with N hN
  apply hN.trans_lt
  change c + δ * H + Cres * r ^ q * eta + (Cres / omega d) * r ^ (q - (d : ℝ)) < b
  dsimp only [ε] at hc hetacost hδcost hbulk hε
  nlinarith only [hc, hetacost, hδcost, hbulk, hε]

end Riesz.Negative
