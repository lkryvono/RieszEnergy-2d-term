import Riesz.Stationary.DisplacedFactorialGaussian
import Riesz.Asymptotics.SphericalOptimalLower
import Riesz.Stationary.GridScaleGaussian

/-!
Finite factorial energy dominates the original simple-law infimum through actual
Gaussian displacement. Weak counting limits and factorial Fatou then give the
unconditional negative spherical optimal-energy lower bound.
-/

noncomputable section
open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal Topology Classical

namespace Riesz.Stationary

/-- Non-strict actual displacement compares the original simple infimum with
the canonical factorial energy of an arbitrary stationary counting law. -/
theorem e_le_factorialW_of_stationary_unitIntensity
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs_lower : -2 < s) (hs_neg : s < 0)
    (P : Measure (CountingConfiguration d)) [IsProbabilityMeasure P]
    (hstationary : IsStationary d (P.map Subtype.val))
    (hmean : (P.map Subtype.val).join = (volume : Measure (Rd d)))
    (hsecond : ∀ K : Set (Rd d), MeasurableSet K → Bornology.IsBounded K →
      (∫⁻ μ, (μ.val K)^2 ∂P) < ∞)
    (hW : factorialW d s P
      (fun n => hsecond (Metric.closedBall (0 : Rd d) (n : ℝ))
        measurableSet_closedBall (isCompact_closedBall (0 : Rd d) (n : ℝ)).isBounded) ≠ ⊤) :
    (e d s : EReal) ≤ factorialW d s P
      (fun n => hsecond (Metric.closedBall (0 : Rd d) (n : ℝ))
        measurableSet_closedBall (isCompact_closedBall (0 : Rd d) (n : ℝ)).isBounded) := by
  let hball : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ)))^2 ∂P) < ∞ :=
    fun n => hsecond (Metric.closedBall (0 : Rd d) (n : ℝ))
      measurableSet_closedBall (isCompact_closedBall (0 : Rd d) (n : ℝ)).isBounded
  have hfinite := (negative_constant_finiteness_and_sign d hd s hs_lower hs_neg).1
  have hbound : (c0 d s : EReal) ≤ factorialW d s P hball := by
    unfold factorialW
    exact le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _)
  have hbot : factorialW d s P hball ≠ ⊥ :=
    ne_of_gt ((EReal.bot_lt_coe (c0 d s)).trans_le hbound)
  let A : ℝ := (factorialW d s P hball).toReal
  have hA : factorialW d s P hball = (A : EReal) :=
    (EReal.coe_toReal hW hbot).symm
  change (e d s : EReal) ≤ factorialW d s P hball
  rw [hA]
  apply EReal.coe_le_coe_iff.mpr
  by_contra h
  have hgap : A < e d s := lt_of_not_ge h
  let ε : ℝ := (e d s-A)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨t,_ht,htAdmissible,htenergy⟩ :=
    exists_admissible_displacedLaw_energy_le_factorialW_add
      d hd s hs_lower hs_neg P hstationary hmean hsecond hW ε hε
  have he : eExtended d s ≤ W d s (displacedLaw d t P) :=
    sInf_le ⟨displacedLaw d t P,htAdmissible,rfl⟩
  have hineq : (e d s : EReal) ≤ ((A+ε : ℝ) : EReal) := by
    rw [EReal.coe_add]
    exact (hfinite ▸ he).trans (hA ▸ htenergy)
  have hreal : e d s ≤ A+ε := EReal.coe_le_coe_iff.mp hineq
  dsimp [ε] at hreal
  linarith

end Riesz.Stationary

namespace Riesz.Asymptotics

/-- The actual bounded-energy weak limit supplies the negative threshold bound,
retaining all multiplicities until the non-strict displacement comparison. -/
theorem negative_e_le_spherical_energy_threshold
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs_lower : -2 < s) (hs_neg : s < 0)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n)) (L : ℝ)
    (henergy : ∀ᶠ n : ℕ in atTop, scaledSphericalKernelEnergy d (N n) s (x n) ≤ L) :
    e d s ≤ L := by
  have hsd : s < (d : ℝ) := hs_neg.trans_le (Nat.cast_nonneg d)
  obtain ⟨Q,φ,hφ,hQ,hsecondAmbient⟩ :=
    exists_sphereLocalCountingProbability_limit_with_second_moments
      d hd s hs_lower hsd hs_neg.ne N hN x ⟨L,henergy⟩
  have hNφ : Tendsto (N ∘ φ) atTop atTop := hN.comp hφ.tendsto_atTop
  have henergyφ : ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N (φ n)) s (x (φ n)) ≤ L :=
    hφ.tendsto_atTop.eventually henergy
  have hQφ : Tendsto (fun n => sphereLocalCountingProbability d (N (φ n))
      (sphericalRadius d (N (φ n))) (x (φ n)).val) atTop (𝓝 Q) := hQ
  have hsecond : ∀ K : Set (Rd d), MeasurableSet K → Bornology.IsBounded K →
      (∫⁻ μ, (μ.val K)^2 ∂Q.toMeasure) < ∞ := by
    intro K hK hKb
    have h := hsecondAmbient K hK hKb
    rw [lintegral_map ((Measure.measurable_coe hK).pow_const 2) measurable_subtype_coe] at h
    exact h
  have hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T))^2
        ∂(sphereLocalCountingProbability d (N (φ n))
          (sphericalRadius d (N (φ n))) (x (φ n)).val).toMeasure) ≤ C :=
    fun T hT => exists_sphereLocalCountingProbability_ball_second_moment_bound_of_energy_bound
      d hd s hs_lower hsd hs_neg.ne (N ∘ φ) hNφ (fun n => x (φ n)) ⟨L,henergyφ⟩ T hT
  have hstationary : IsStationary d (Q.toMeasure.map Subtype.val) :=
    sphereLocalCountingProbability_limit_stationary
      d hd (N ∘ φ) hNφ (fun n => (x (φ n)).val) Q hQφ
  have hmean : (Q.toMeasure.map Subtype.val).join = (volume : Measure (Rd d)) :=
    sphereLocalCountingProbability_limit_mean_eq_volume_unconditional
      d hd (N ∘ φ) hNφ (fun n => (x (φ n)).val) Q hQφ hball
  obtain ⟨hsecondQ,hFatou,hWfinite⟩ :=
    sphereLocalCountingProbability_limit_factorialW_le_liminf_of_negative_energy_bound
      d hd s hs_lower hs_neg (N ∘ φ) hNφ (fun n => x (φ n)) ⟨L,henergyφ⟩ Q hQφ
  have he : (e d s : EReal) ≤ Riesz.Stationary.factorialW d s Q.toMeasure hsecondQ :=
    Riesz.Stationary.e_le_factorialW_of_stationary_unitIntensity
      d hd s hs_lower hs_neg Q.toMeasure hstationary hmean hsecond hWfinite
  have hupper : atTop.liminf (fun n : ℕ =>
      (scaledSphericalKernelEnergy d (N (φ n)) s (x (φ n)) : EReal)) ≤ (L : EReal) :=
    Filter.liminf_le_of_frequently_le'
      (henergyφ.mono (fun n hn => EReal.coe_le_coe_iff.mpr hn)).frequently
  exact EReal.coe_le_coe_iff.mp (he.trans (hFatou.trans hupper))

/-- Unconditional negative optimal lower bound in the paper's enlarged-sphere units. -/
theorem eventually_lt_scaledOptimalKernelEnergy_of_lt_e_neg
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs_lower : -2 < s) (hs_neg : s < 0)
    (a : ℝ) (ha : a < e d s) :
    ∀ᶠ N : ℕ in atTop, a < scaledOptimalKernelEnergy d s N := by
  by_contra h
  have hbad : ∃ᶠ N : ℕ in atTop, scaledOptimalKernelEnergy d s N ≤ a :=
    (Filter.not_eventually.mp h).mono (fun N hN => le_of_not_gt hN)
  have hbadpos : ∃ᶠ N : ℕ in atTop,
      0 < N ∧ scaledOptimalKernelEnergy d s N ≤ a :=
    (hbad.and_eventually (eventually_gt_atTop (0 : ℕ))).mono
      (fun N hN => ⟨hN.2,hN.1⟩)
  obtain ⟨φ,hφ,hφbad⟩ := extraction_of_frequently_atTop hbadpos
  let L : ℝ := (a+e d s)/2
  have hε : 0 < L-a := by dsimp [L]; linarith only [ha]
  have hchoice : ∀ n : ℕ, ∃ x : SphereConfiguration d (φ n),
      scaledSphericalKernelEnergy d (φ n) s x ≤ L := by
    intro n
    obtain ⟨x,hx⟩ := exists_scaled_spherical_near_minimizer
      d hd s (φ n) (hφbad n).1 (L-a) hε
    exact ⟨x,by linarith [(hφbad n).2]⟩
  choose x hx using hchoice
  have he := negative_e_le_spherical_energy_threshold
    d hd s hs_lower hs_neg φ hφ.tendsto_atTop x L (Eventually.of_forall hx)
  dsimp [L] at he
  linarith only [ha,he]

end Riesz.Asymptotics
