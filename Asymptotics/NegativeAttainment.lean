import Riesz.Asymptotics.NegativeOptimalLower
import Riesz.Negative.SphericalAssembly
import Riesz.Negative.ReverseCubeComparison
import Riesz.Stationary.GridEnergyNegative

/-!
The negative spherical energy limit and Euclidean attainment, using actual
spherical competitors, reverse cube comparison, and strict displacement to
prove simplicity of the optimal counting limit.
-/

noncomputable section
open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal Topology Classical

namespace Riesz.Asymptotics

private theorem negative_scaledOptimal_le_scaledSpherical
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hq2 : q < 2)
    (N : ℕ) (hN : 0 < N) (x : SphereConfiguration d N) :
    scaledOptimalKernelEnergy d (-q) N ≤ scaledSphericalKernelEnergy d N (-q) x := by
  have hsd : -q < (d : ℝ) := (neg_lt_zero.mpr hq).trans_le (Nat.cast_nonneg d)
  have hbelow : BddBelow (Set.range (Riesz.Energy.kernelEnergy d (-q) N)) := by
    refine ⟨V_K d (-q)*(N : ℝ)^2+Problem1.part5_energy_constants_negative d (-q)*
      (N : ℝ)^(1+(-q)/(d : ℝ)),?_⟩
    rintro r ⟨z,rfl⟩
    exact negative_sphere_kernelEnergy_lower d hd (-q) (neg_lt_neg hq2)
      (neg_lt_zero.mpr hq) hsd N z
  have hopt : E_K d (-q) N ≤ Riesz.Energy.kernelEnergy d (-q) N x :=
    csInf_le hbelow (Set.mem_range_self x)
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hopt _)
    (div_nonneg (Real.rpow_nonneg (sphericalRadius_pos d N hN).le _) (Nat.cast_nonneg N))

/-- Genuine reverse comparison and sphere filling close the sharp negative limit. -/
theorem tendsto_scaledOptimalKernelEnergy_neg
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hq2 : q < 2) :
    Tendsto (scaledOptimalKernelEnergy d (-q)) atTop (𝓝 (e d (-q))) := by
  have heq := Riesz.Negative.balanced_density_inf_eq_e d hd q hq hq2
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact eventually_lt_scaledOptimalKernelEnergy_of_lt_e_neg
      d hd (-q) (neg_lt_neg hq2) (neg_lt_zero.mpr hq) a ha
  · intro b hb
    apply Riesz.Negative.negative_spherical_upper_to_balanced_density d hd q hq hq2 b
    rw [heq]
    exact hb

/-- The exact Showcase normalization follows from the actual negative limit. -/
theorem negative_normalizedLimit
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hq2 : q < 2) :
    Tendsto (fun N : ℕ => (E_K d (-q) N-V_K d (-q)*(N : ℝ)^(2 : ℕ))/
      (N : ℝ)^(1+(-q)/(d : ℝ))) atTop
      (𝓝 ((omega d)^(-(-q)/(d : ℝ))*e d (-q))) := by
  have hscaled := tendsto_scaledOptimalKernelEnergy_neg d hd q hq hq2
  apply (hscaled.const_mul ((omega d)^(-(-q)/(d : ℝ)))).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [scaledOptimalKernelEnergy_eq_omega_mul_normalized d (-q) N hN,
    show -(-q)/(d : ℝ) = -((-q)/(d : ℝ)) by ring,Real.rpow_neg (omega_pos d).le]
  simp only [← mul_assoc,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos (omega_pos d) ((-q)/(d : ℝ))).ne',one_mul]

/-- The optimal negative weak limit is simple: otherwise actual heat
displacement strictly beats the original simple-law infimum. -/
theorem negative_attained
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hq2 : q < 2) :
    ∃ P : ConfigurationLaw d, Admissible d P ∧ W d (-q) P = (e d (-q) : EReal) := by
  have hs_lower : -2 < -q := neg_lt_neg hq2
  have hs_neg : -q < 0 := neg_lt_zero.mpr hq
  have hsd : -q < (d : ℝ) := hs_neg.trans_le (Nat.cast_nonneg d)
  have hfinite := (Riesz.Stationary.negative_constant_finiteness_and_sign
    d hd (-q) hs_lower hs_neg).1
  have hopt := tendsto_scaledOptimalKernelEnergy_neg d hd q hq hq2
  let N : ℕ → ℕ := fun n => n+1
  have hN : Tendsto N atTop atTop :=
    (show StrictMono N from fun a b hab => Nat.add_lt_add_right hab 1).tendsto_atTop
  have hNpos (n : ℕ) : 0 < N n := Nat.succ_pos n
  let ε : ℕ → ℝ := fun n => (N n : ℝ)⁻¹
  have hεpos (n : ℕ) : 0 < ε n := inv_pos.mpr (Nat.cast_pos.mpr (hNpos n))
  have hε : Tendsto ε atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hN)
  have hchoice : ∀ n : ℕ, ∃ x : SphereConfiguration d (N n),
      scaledSphericalKernelEnergy d (N n) (-q) x <
        scaledOptimalKernelEnergy d (-q) (N n)+ε n :=
    fun n => exists_scaled_spherical_near_minimizer d hd (-q) (N n) (hNpos n) (ε n) (hεpos n)
  choose x hx using hchoice
  have hlo (n : ℕ) : scaledOptimalKernelEnergy d (-q) (N n) ≤
      scaledSphericalKernelEnergy d (N n) (-q) (x n) :=
    negative_scaledOptimal_le_scaledSpherical d hd q hq hq2 (N n) (hNpos n) (x n)
  have hE : Tendsto (fun n => scaledSphericalKernelEnergy d (N n) (-q) (x n))
      atTop (𝓝 (e d (-q))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hopt.comp hN)
      (by simpa only [add_zero] using (hopt.comp hN).add hε)
    · exact Eventually.of_forall hlo
    · exact Eventually.of_forall (fun n => (hx n).le)
  let L : ℝ := e d (-q)+1
  have henergy : ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N n) (-q) (x n) ≤ L :=
    (hE.eventually (gt_mem_nhds (by dsimp [L]; linarith))).mono (fun _ hn => hn.le)
  obtain ⟨Q,φ,hφ,hQ,hsecondAmbient⟩ :=
    exists_sphereLocalCountingProbability_limit_with_second_moments
      d hd (-q) hs_lower hsd hs_neg.ne N hN x ⟨L,henergy⟩
  have hNφ : Tendsto (N ∘ φ) atTop atTop := hN.comp hφ.tendsto_atTop
  have henergyφ : ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N (φ n)) (-q) (x (φ n)) ≤ L :=
    hφ.tendsto_atTop.eventually henergy
  have hQφ : Tendsto (fun n => sphereLocalCountingProbability d (N (φ n))
      (sphericalRadius d (N (φ n))) (x (φ n)).val) atTop (𝓝 Q) := hQ
  have hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T))^2
        ∂(sphereLocalCountingProbability d (N (φ n))
          (sphericalRadius d (N (φ n))) (x (φ n)).val).toMeasure) ≤ C :=
    fun T hT => exists_sphereLocalCountingProbability_ball_second_moment_bound_of_energy_bound
      d hd (-q) hs_lower hsd hs_neg.ne (N ∘ φ) hNφ (fun n => x (φ n)) ⟨L,henergyφ⟩ T hT
  have hstationary : IsStationary d (Q.toMeasure.map Subtype.val) :=
    sphereLocalCountingProbability_limit_stationary
      d hd (N ∘ φ) hNφ (fun n => (x (φ n)).val) Q hQφ
  have hmean : (Q.toMeasure.map Subtype.val).join = (volume : Measure (Rd d)) :=
    sphereLocalCountingProbability_limit_mean_eq_volume_unconditional
      d hd (N ∘ φ) hNφ (fun n => (x (φ n)).val) Q hQφ hball
  have hsecond : ∀ K : Set (Rd d), MeasurableSet K → Bornology.IsBounded K →
      (∫⁻ μ, (μ.val K)^2 ∂Q.toMeasure) < ∞ := by
    intro K hK hKb
    have h := hsecondAmbient K hK hKb
    rw [lintegral_map ((Measure.measurable_coe hK).pow_const 2) measurable_subtype_coe] at h
    exact h
  obtain ⟨hsecondQ,hFatou,hWfinite⟩ :=
    sphereLocalCountingProbability_limit_factorialW_le_liminf_of_negative_energy_bound
      d hd (-q) hs_lower hs_neg (N ∘ φ) hNφ (fun n => x (φ n)) ⟨L,henergyφ⟩ Q hQφ
  have hWhat : Riesz.Stationary.factorialW d (-q) Q.toMeasure hsecondQ ≤
      (e d (-q) : EReal) :=
    hFatou.trans_eq (EReal.tendsto_coe.mpr (hE.comp hφ.tendsto_atTop)).liminf_eq
  have hsimple : ∀ᵐ μ ∂Q.toMeasure, IsSimpleConfiguration d μ.val := by
    by_contra hnonsimple
    obtain ⟨t,_ht,hPt,hWt⟩ :=
      Riesz.Stationary.exists_admissible_displacedLaw_energy_lt_factorialW_of_not_ae_simple
        d hd (-q) hs_lower hs_neg Q.toMeasure hstationary hmean hsecond hWfinite hnonsimple
    have he : eExtended d (-q) ≤ W d (-q) (displacedLaw d t Q.toMeasure) :=
      sInf_le ⟨displacedLaw d t Q.toMeasure,hPt,rfl⟩
    have hcontradiction : (e d (-q) : EReal) < (e d (-q) : EReal) :=
      (hfinite ▸ he).trans_lt (hWt.trans_le hWhat)
    exact lt_irrefl _ hcontradiction
  have hsimpleAmbient : ∀ᵐ μ ∂Q.toMeasure.map Subtype.val, IsSimpleConfiguration d μ :=
    (ae_map_iff measurable_subtype_coe.aemeasurable (measurableSet_isSimpleConfiguration d)).mpr hsimple
  have hAdmissible : Admissible d (Q.toMeasure.map Subtype.val) :=
    ⟨Measure.isProbabilityMeasure_map (μ := Q.toMeasure) measurable_subtype_coe.aemeasurable,
      hsimpleAmbient,hstationary,
      fun K hK _ => (Measure.join_apply hK).symm.trans
        (congrArg (fun ν : Measure (Rd d) => ν K) hmean),hsecondAmbient⟩
  have hWupper : W d (-q) (Q.toMeasure.map Subtype.val) ≤ (e d (-q) : EReal) := by
    rw [← Riesz.Stationary.factorialW_eq_W_of_ae_simple d (-q) Q.toMeasure hsecondQ hsimple]
    exact hWhat
  have he : eExtended d (-q) ≤ W d (-q) (Q.toMeasure.map Subtype.val) :=
    sInf_le ⟨Q.toMeasure.map Subtype.val,hAdmissible,rfl⟩
  exact ⟨Q.toMeasure.map Subtype.val,hAdmissible,le_antisymm hWupper (hfinite ▸ he)⟩

/-- All original negative analytic clauses from actual producer theorems. -/
theorem negative_analyticClaims
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hq2 : q < 2) :
    AnalyticClaims d (-q) := by
  have hconstant := Riesz.Stationary.negative_constant_finiteness_and_sign
    d hd (-q) (neg_lt_neg hq2) (neg_lt_zero.mpr hq)
  refine ⟨negative_normalizedLimit d hd q hq hq2,hconstant.1,
    (fun hs => (show False by linarith only [hs,hq]).elim),negative_attained d hd q hq hq2,?_⟩
  intro q' hq' hq2' hqq'
  have heqq : q' = q := by linarith only [hqq']
  subst q'
  have hcube := (Riesz.Stationary.balanced_cube_density_limit_and_stationary_bound
    d hd q hq hq2).1
  have heq := Riesz.Negative.balanced_density_inf_eq_e d hd q hq hq2
  change sInf {r : ℝ | ∃ m : ℕ, 1 ≤ m ∧ r = b d q m/(m : ℝ)^d} = e d (-q) at heq
  rw [heq] at hcube
  exact ⟨hcube,heq.symm⟩

end Riesz.Asymptotics
