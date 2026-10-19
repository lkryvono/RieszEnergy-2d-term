import Riesz.Configuration.Compactness
import Riesz.Configuration.FiniteProducts
import Mathlib.MeasureTheory.Integral.Prod

/-! Compact tests for the factorial pair functional of counting configurations.
The diagonal term removes equal labels; distinct labels at the same site remain.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Configuration

/-- Pull a compact pair test back to equal positions. -/
def countingDiagonalTest (d : ℕ) (f : C_c(Rd d × Rd d, ℝ)) : C_c(Rd d, ℝ) :=
  ⟨⟨fun x => f (x, x), f.continuous.comp (continuous_id.prodMk continuous_id)⟩,
    by
      refine HasCompactSupport.intro (f.hasCompactSupport.image continuous_fst) ?_
      exact fun x hx => image_eq_zero_of_notMem_tsupport (f := (f : Rd d × Rd d → ℝ))
        (fun h => hx ⟨(x, x), h, rfl⟩)⟩

theorem continuous_cutoffMeasure (d : ℕ) (χ : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) :
    Continuous (fun μ : CountingConfiguration d => cutoffMeasure d μ.val χ) := by
  exact continuous_iff_continuousAt.mpr (fun μ =>
    tendsto_cutoffMeasure_of_tendsto_integral d id (𝓝 μ) μ.val
      (fun f => (continuous_countingIntegral d f).tendsto μ) χ hχ)

theorem integral_cutoffMeasure_prod (d : ℕ) (μ : Measure (Rd d))
    [IsFiniteMeasureOnCompacts μ] (χ : C_c(Rd d, ℝ))
    (f : C_c(Rd d × Rd d, ℝ))
    (hf : ∀ p ∈ tsupport f, χ p.1 = 1 ∧ χ p.2 = 1) :
    (∫ p, f p ∂((cutoffMeasure d μ χ).prod (cutoffMeasure d μ χ)).toMeasure) =
      ∫ p, f p ∂μ.prod μ := by
  change (∫ p, f p ∂(μ.withDensity (fun x => ENNReal.ofReal (χ x))).prod
    (μ.withDensity (fun x => ENNReal.ofReal (χ x)))) = _
  rw [prod_withDensity (μ := μ) (ν := μ)
    (f := fun x => ENNReal.ofReal (χ x)) (g := fun x => ENNReal.ofReal (χ x))
    χ.continuous.measurable.ennreal_ofReal χ.continuous.measurable.ennreal_ofReal]
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun p : Rd d × Rd d => ENNReal.ofReal (χ p.1) * ENNReal.ofReal (χ p.2))
    ((χ.continuous.measurable.comp measurable_fst).ennreal_ofReal.mul
      (χ.continuous.measurable.comp measurable_snd).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.ofReal_lt_top))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  by_cases hp : p ∈ tsupport f
  · simp [(hf p hp).1, (hf p hp).2]
  · simp [image_eq_zero_of_notMem_tsupport hp]

/-- All-pair compact-test integrals depend continuously on the configuration. -/
theorem continuous_countingPairIntegral (d : ℕ) (f : C_c(Rd d × Rd d, ℝ)) :
    Continuous (fun μ : CountingConfiguration d => ∫ p, f p ∂μ.val.prod μ.val) := by
  let K : Set (Rd d) := (Prod.fst '' tsupport f) ∪ (Prod.snd '' tsupport f)
  have hK : IsCompact K :=
    (f.hasCompactSupport.image continuous_fst).union
      (f.hasCompactSupport.image continuous_snd)
  obtain ⟨χ, hχK, _, hχcompact, hχrange⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (by simp)
  let ψ : C_c(Rd d, ℝ) := ⟨χ, hχcompact⟩
  have hψ : ∀ x, 0 ≤ ψ x := fun x => (hχrange x).1
  have hfψ : ∀ p ∈ tsupport f, ψ p.1 = 1 ∧ ψ p.2 = 1 :=
    fun p hp => ⟨hχK (Or.inl ⟨p, hp, rfl⟩), hχK (Or.inr ⟨p, hp, rfl⟩)⟩
  have hcont :=
    (FiniteMeasure.continuous_integral_boundedContinuousFunction
      f.toBoundedContinuousFunction).comp
      (continuous_finiteMeasure_prod.comp
        ((continuous_cutoffMeasure d ψ hψ).prodMk (continuous_cutoffMeasure d ψ hψ)))
  exact hcont.congr (fun μ => integral_cutoffMeasure_prod d μ.val ψ f hfψ)

/-- The factorial pair functional, allowing multiplicity at each site. -/
def countingFactorialIntegral (d : ℕ) (μ : CountingConfiguration d)
    (f : C_c(Rd d × Rd d, ℝ)) : ℝ :=
  (∫ p, f p ∂μ.val.prod μ.val) - ∫ x, f (x, x) ∂μ.val

/-- Factorial compact-test integrals depend continuously on the configuration. -/
theorem continuous_countingFactorialIntegral (d : ℕ)
    (f : C_c(Rd d × Rd d, ℝ)) :
    Continuous (fun μ : CountingConfiguration d => countingFactorialIntegral d μ f) := by
  exact (continuous_countingPairIntegral d f).sub
    (continuous_countingIntegral d (countingDiagonalTest d f))

/-- Integrating against a finite tuple counts labels, including repeated sites. -/
theorem integral_tupleCounting (d m : ℕ) (x : Fin m → Rd d) (g : Rd d → ℝ) :
    (∫ y, g y ∂Riesz.Negative.tupleCounting d m x) = ∑ i, g (x i) := by
  unfold Riesz.Negative.tupleCounting
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp

theorem integral_tupleCounting_prod (d m : ℕ) (x : Fin m → Rd d)
    (f : C_c(Rd d × Rd d, ℝ)) :
    (∫ p, f p ∂(Riesz.Negative.tupleCounting d m x).prod
      (Riesz.Negative.tupleCounting d m x)) = ∑ i, ∑ j, f (x i, x j) := by
  letI := Riesz.Negative.tupleCounting_isFiniteMeasure d m x
  rw [integral_prod _ f.integrable]
  simp_rw [integral_tupleCounting]

/-- On a finite local tuple, the factorial functional sums over unequal labels.
No injectivity of the tuple is assumed. -/
theorem countingFactorialIntegral_eq_sum_of_restrict_eq_tupleCounting
    (d n m : ℕ) (μ : CountingConfiguration d) (x : Fin m → Rd d)
    (f : C_c(Rd d × Rd d, ℝ))
    (hμ : μ.val.restrict (Metric.closedBall (0 : Rd d) (n : ℝ)) =
      Riesz.Negative.tupleCounting d m x)
    (hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ) ×ˢ
      Metric.closedBall (0 : Rd d) (n : ℝ)) :
    countingFactorialIntegral d μ f =
      ∑ i : Fin m, ∑ j : Fin m, if i = j then 0 else f (x i, x j) := by
  let K := Metric.closedBall (0 : Rd d) (n : ℝ)
  have hp : (∫ p, f p ∂μ.val.prod μ.val) =
      ∫ p, f p ∂(μ.val.restrict K).prod (μ.val.restrict K) := by
    rw [Measure.prod_restrict]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp =>
      image_eq_zero_of_notMem_tsupport (fun h => hp (hf h)))).symm
  have hd : (∫ y, f (y, y) ∂μ.val) = ∫ y, f (y, y) ∂μ.val.restrict K := by
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := μ.val) (s := K) (f := fun y => f (y, y)) (fun y hy =>
      image_eq_zero_of_notMem_tsupport (f := (f : Rd d × Rd d → ℝ))
        (x := (y, y))
        (fun h => hy (hf h).1))).symm
  rw [countingFactorialIntegral, hp, hd, show μ.val.restrict K = _ from hμ,
    integral_tupleCounting_prod, integral_tupleCounting]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hdiag : (∑ j : Fin m, if i = j then f (x i, x j) else 0) = f (x i, x i) := by
    simp
  rw [← hdiag, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp

/-- Nonnegative compact tests have nonnegative factorial integrals, including
configurations with repeated sites. -/
theorem countingFactorialIntegral_nonneg (d : ℕ) (μ : CountingConfiguration d)
    (f : C_c(Rd d × Rd d, ℝ)) (hf : ∀ p, 0 ≤ f p) :
    0 ≤ countingFactorialIntegral d μ f := by
  obtain ⟨R, hR⟩ :=
    ((f.hasCompactSupport.image continuous_fst).union
      (f.hasCompactSupport.image continuous_snd)).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hs : tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ) ×ˢ
      Metric.closedBall (0 : Rd d) (n : ℝ) := by
    exact fun p hp => ⟨by simpa only [Metric.mem_closedBall, dist_zero_right]
      using (hR p.1 (Or.inl ⟨p, hp, rfl⟩)).trans hn,
      by simpa only [Metric.mem_closedBall, dist_zero_right]
        using (hR p.2 (Or.inr ⟨p, hp, rfl⟩)).trans hn⟩
  obtain ⟨m, x, hx⟩ := μ.property n
  rw [countingFactorialIntegral_eq_sum_of_restrict_eq_tupleCounting d n m μ x f hx hs]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    by split_ifs <;> simp_all only [le_refl]))

end Riesz.Configuration
