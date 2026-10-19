import Riesz.Asymptotics.SphericalSharpLower
import Riesz.Asymptotics.Assembly
import Riesz.Geometry.CountRepairFromProblem1
import Riesz.Stationary.GridEnergyPositive
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The positive optimal spherical lower bound

Near-infimum configurations and the actual admissible weak-limit bound suffice;
no finite-size minimizer or convergent scalar energy subsequence is needed.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal Topology Classical

namespace Riesz.Asymptotics

/-- The optimal spherical energy in the enlarged-sphere units of the paper. -/
def scaledOptimalKernelEnergy (d : ℕ) (s : ℝ) (N : ℕ) : ℝ :=
  (sphericalRadius d N) ^ (-s) / (N : ℝ) *
    (E_K d s N - V_K d s * (N : ℝ) ^ (2 : ℕ))

theorem exists_scaled_spherical_near_minimizer
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (N : ℕ) (hN : 0 < N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x : SphereConfiguration d N,
      scaledSphericalKernelEnergy d N s x < scaledOptimalKernelEnergy d s N + ε := by
  let a : ℝ := (sphericalRadius d N) ^ (-s) / (N : ℝ)
  have ha : 0 < a :=
    div_pos (Real.rpow_pos_of_pos (sphericalRadius_pos d N hN) _) (Nat.cast_pos.mpr hN)
  have hnonempty : (Set.range (Riesz.Energy.kernelEnergy d s N)).Nonempty :=
    (sphereConfiguration_nonempty d hd N).elim (fun x => ⟨_, x, rfl⟩)
  have hlt : sInf (Set.range (Riesz.Energy.kernelEnergy d s N)) <
      E_K d s N + ε / a := lt_add_of_pos_right _ (div_pos hε ha)
  obtain ⟨r, ⟨x, rfl⟩, hx⟩ := exists_lt_of_csInf_lt hnonempty hlt
  refine ⟨x, ?_⟩
  change a * (Riesz.Energy.kernelEnergy d s N x - V_K d s * (N : ℝ) ^ 2) <
    a * (E_K d s N - V_K d s * (N : ℝ) ^ 2) + ε
  have hxscale := mul_lt_mul_of_pos_left (sub_lt_sub_right hx (V_K d s * (N : ℝ) ^ 2)) ha
  nlinarith only [hxscale, div_mul_cancel₀ ε ha.ne']

theorem exists_admissible_W_le_of_spherical_energy_threshold
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n)) (L : ℝ)
    (henergy : ∀ᶠ n : ℕ in atTop, scaledSphericalKernelEnergy d (N n) s (x n) ≤ L) :
    ∃ P : ConfigurationLaw d, Admissible d P ∧ W d s P ≤ (L : EReal) := by
  obtain ⟨Q, φ, hφ, hQ, hAdmissible⟩ :=
    exists_sphereLocalCountingProbability_admissible_limit_of_positive_energy_bound
      d hd s hs hsd N hN x ⟨L, henergy⟩
  have henergyφ : ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N (φ n)) s (x (φ n)) ≤ L :=
    hφ.tendsto_atTop.eventually henergy
  have hW := sphereLocalCountingProbability_limit_W_le_liminf_of_positive_energy_bound
    d hd s hs hsd (N ∘ φ) (hN.comp hφ.tendsto_atTop) (fun n => x (φ n))
    ⟨L, henergyφ⟩ Q hQ
  have hupper : atTop.liminf (fun n : ℕ =>
      (scaledSphericalKernelEnergy d (N (φ n)) s (x (φ n)) : EReal)) ≤ (L : EReal) :=
    Filter.liminf_le_of_frequently_le'
      (henergyφ.mono (fun n hn => EReal.coe_le_coe_iff.mpr hn)).frequently
  exact ⟨Q.toMeasure.map Subtype.val, hAdmissible, hW.trans hupper⟩

theorem e_le_spherical_energy_threshold
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n)) (L : ℝ)
    (henergy : ∀ᶠ n : ℕ in atTop, scaledSphericalKernelEnergy d (N n) s (x n) ≤ L) :
    e d s ≤ L := by
  obtain ⟨P, hP, hW⟩ := exists_admissible_W_le_of_spherical_energy_threshold
    d hd s hs hsd N hN x L henergy
  have hfinite := (Riesz.Stationary.positive_constant_finiteness_and_sign
    d (by omega : 0 < d) s hs hsd).1
  have he : eExtended d s ≤ W d s P := sInf_le ⟨P, hP, rfl⟩
  rw [hfinite] at he
  exact EReal.coe_le_coe_iff.mp (he.trans hW)

/-- The positive optimal lower bound follows from the actual weak-limit bound. -/
theorem eventually_lt_scaledOptimalKernelEnergy_of_lt_e
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (a : ℝ) (ha : a < e d s) :
    ∀ᶠ N : ℕ in atTop, a < scaledOptimalKernelEnergy d s N := by
  by_contra h
  have hbad : ∃ᶠ N : ℕ in atTop, scaledOptimalKernelEnergy d s N ≤ a :=
    (Filter.not_eventually.mp h).mono (fun N hN => le_of_not_gt hN)
  have hbadpos : ∃ᶠ N : ℕ in atTop,
      0 < N ∧ scaledOptimalKernelEnergy d s N ≤ a :=
    (hbad.and_eventually (eventually_gt_atTop (0 : ℕ))).mono
      (fun N hN => ⟨hN.2, hN.1⟩)
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hbadpos
  let L : ℝ := (a + e d s) / 2
  have hε : 0 < L - a := by
    dsimp [L]
    linarith only [ha]
  have hchoice : ∀ n : ℕ, ∃ x : SphereConfiguration d (φ n),
      scaledSphericalKernelEnergy d (φ n) s x ≤ L := by
    intro n
    obtain ⟨x, hx⟩ := exists_scaled_spherical_near_minimizer
      d hd s (φ n) (hφbad n).1 (L - a) hε
    exact ⟨x, by linarith [(hφbad n).2]⟩
  choose x hx using hchoice
  have he := e_le_spherical_energy_threshold d hd s hs hsd φ
    hφ.tendsto_atTop x L (Eventually.of_forall hx)
  dsimp [L] at he
  linarith only [ha, he]

/-- Full convergence once the genuine positive spherical upper bound is supplied. -/
theorem tendsto_scaledOptimalKernelEnergy_of_positive_spherical_upper
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (hupper : ∀ b : ℝ, e d s < b →
      ∀ᶠ N : ℕ in atTop, scaledOptimalKernelEnergy d s N < b) :
    Tendsto (scaledOptimalKernelEnergy d s) atTop (𝓝 (e d s)) := by
  exact tendsto_order.mpr
    ⟨fun a ha => eventually_lt_scaledOptimalKernelEnergy_of_lt_e d hd s hs hsd a ha, hupper⟩

/-- Exact conversion from enlarged-sphere units to the Showcase normalization. -/
theorem scaledOptimalKernelEnergy_eq_omega_mul_normalized
    (d : ℕ) (s : ℝ) (N : ℕ) (hN : 0 < N) :
    scaledOptimalKernelEnergy d s N = (omega d) ^ (s / (d : ℝ)) *
      ((E_K d s N - V_K d s * (N : ℝ) ^ (2 : ℕ)) /
        (N : ℝ) ^ (1 + s / (d : ℝ))) := by
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hω : 0 < omega d := omega_pos d
  unfold scaledOptimalKernelEnergy sphericalRadius
  rw [← Real.rpow_mul (div_nonneg hNr.le hω.le),
    show (1 / (d : ℝ)) * (-s) = -(s / (d : ℝ)) by ring,
    Real.div_rpow hNr.le hω.le, Real.rpow_neg hNr.le, Real.rpow_neg hω.le,
    Real.rpow_add hNr, Real.rpow_one]
  field_simp [hNr.ne', (Real.rpow_pos_of_pos hNr (s / (d : ℝ))).ne',
    (Real.rpow_pos_of_pos hω (s / (d : ℝ))).ne']

/-- The exact normalized limit, conditional only on the remaining sphere upper bound. -/
theorem positive_normalizedLimit_of_spherical_upper
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (hupper : ∀ b : ℝ, e d s < b →
      ∀ᶠ N : ℕ in atTop, scaledOptimalKernelEnergy d s N < b) :
    Tendsto (fun N : ℕ => (E_K d s N - V_K d s * (N : ℝ) ^ (2 : ℕ)) /
      (N : ℝ) ^ (1 + s / (d : ℝ))) atTop
        (𝓝 ((omega d) ^ (-s / (d : ℝ)) * e d s)) := by
  have hscaled := tendsto_scaledOptimalKernelEnergy_of_positive_spherical_upper
    d hd s hs hsd hupper
  apply (hscaled.const_mul ((omega d) ^ (-s / (d : ℝ)))).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [scaledOptimalKernelEnergy_eq_omega_mul_normalized d s N hN,
    show -s / (d : ℝ) = -(s / (d : ℝ)) by ring, Real.rpow_neg (omega_pos d).le]
  simp only [← mul_assoc,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos (omega_pos d) (s / (d : ℝ))).ne', one_mul]

/-- Every concrete tuple bounds the positive optimal scaled value from above. -/
theorem scaledOptimalKernelEnergy_le_scaledSphericalKernelEnergy
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (N : ℕ) (hN : 0 < N) (x : SphereConfiguration d N) :
    scaledOptimalKernelEnergy d s N ≤ scaledSphericalKernelEnergy d N s x := by
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_right (positive_sphere_optimalEnergy_le d hd s hs hsd N x) _)
    (div_nonneg (Real.rpow_nonneg (sphericalRadius_pos d N hN).le _) (Nat.cast_nonneg N))

/-- A convergent actual energy sequence produces an admissible law below its limit. -/
theorem exists_admissible_W_le_of_spherical_energy_tendsto
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n)) (L : ℝ)
    (hE : Tendsto (fun n => scaledSphericalKernelEnergy d (N n) s (x n))
      atTop (𝓝 L)) :
    ∃ P : ConfigurationLaw d, Admissible d P ∧ W d s P ≤ (L : EReal) := by
  have henergy : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N n) s (x n) ≤ C :=
    ⟨L + 1, (hE.eventually (gt_mem_nhds (show L < L + 1 by linarith))).mono
      (fun n hn => hn.le)⟩
  obtain ⟨Q, φ, hφ, hQ, hAdmissible⟩ :=
    exists_sphereLocalCountingProbability_admissible_limit_of_positive_energy_bound
      d hd s hs hsd N hN x henergy
  have henergyφ : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N (φ n)) s (x (φ n)) ≤ C :=
    ⟨henergy.choose, hφ.tendsto_atTop.eventually henergy.choose_spec⟩
  have hW := sphereLocalCountingProbability_limit_W_le_liminf_of_positive_energy_bound
    d hd s hs hsd (N ∘ φ) (hN.comp hφ.tendsto_atTop) (fun n => x (φ n)) henergyφ Q hQ
  have hEφ : Tendsto (fun n => scaledSphericalKernelEnergy d (N (φ n)) s (x (φ n)))
      atTop (𝓝 L) := hE.comp hφ.tendsto_atTop
  exact ⟨Q.toMeasure.map Subtype.val, hAdmissible,
    hW.trans_eq (EReal.tendsto_coe.mpr hEφ).liminf_eq⟩

/-- The same near-minimizing spherical sequence proves positive attainment after upper. -/
theorem positive_attained_of_spherical_upper
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (hupper : ∀ b : ℝ, e d s < b →
      ∀ᶠ N : ℕ in atTop, scaledOptimalKernelEnergy d s N < b) :
    ∃ P : ConfigurationLaw d, Admissible d P ∧ W d s P = (e d s : EReal) := by
  have hopt := tendsto_scaledOptimalKernelEnergy_of_positive_spherical_upper
    d hd s hs hsd hupper
  let N : ℕ → ℕ := fun n => n + 1
  have hN : Tendsto N atTop atTop :=
    (show StrictMono N from fun a b hab => Nat.add_lt_add_right hab 1).tendsto_atTop
  have hNpos (n : ℕ) : 0 < N n := Nat.succ_pos n
  let ε : ℕ → ℝ := fun n => (N n : ℝ)⁻¹
  have hεpos (n : ℕ) : 0 < ε n := inv_pos.mpr (Nat.cast_pos.mpr (hNpos n))
  have hε : Tendsto ε atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hN)
  have hchoice : ∀ n : ℕ, ∃ x : SphereConfiguration d (N n),
      scaledSphericalKernelEnergy d (N n) s x < scaledOptimalKernelEnergy d s (N n) + ε n :=
    fun n => exists_scaled_spherical_near_minimizer d hd s (N n) (hNpos n) (ε n) (hεpos n)
  choose x hx using hchoice
  have hlo (n : ℕ) : scaledOptimalKernelEnergy d s (N n) ≤
      scaledSphericalKernelEnergy d (N n) s (x n) :=
    scaledOptimalKernelEnergy_le_scaledSphericalKernelEnergy d hd s hs hsd
      (N n) (hNpos n) (x n)
  have hE : Tendsto (fun n => scaledSphericalKernelEnergy d (N n) s (x n))
      atTop (𝓝 (e d s)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hopt.comp hN)
      (by simpa only [add_zero] using (hopt.comp hN).add hε)
    · exact Eventually.of_forall hlo
    · exact Eventually.of_forall (fun n => (hx n).le)
  obtain ⟨P, hP, hW⟩ := exists_admissible_W_le_of_spherical_energy_tendsto
    d hd s hs hsd N hN x (e d s) hE
  have hfinite := (Riesz.Stationary.positive_constant_finiteness_and_sign
    d (by omega : 0 < d) s hs hsd).1
  have he : eExtended d s ≤ W d s P := sInf_le ⟨P, hP, rfl⟩
  rw [hfinite] at he
  exact ⟨P, hP, le_antisymm hW he⟩

/-- All positive analytic conclusions reduce to the genuine spherical upper bound. -/
theorem positive_analyticClaims_of_spherical_upper
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (hupper : ∀ b : ℝ, e d s < b →
      ∀ᶠ N : ℕ in atTop, scaledOptimalKernelEnergy d s N < b) :
    AnalyticClaims d s := by
  have hconstant := Riesz.Stationary.positive_constant_finiteness_and_sign
    d (by omega : 0 < d) s hs hsd
  refine ⟨positive_normalizedLimit_of_spherical_upper d hd s hs hsd hupper,
    hconstant.1, fun _ => hconstant.2.1,
    positive_attained_of_spherical_upper d hd s hs hsd hupper, ?_⟩
  intro q hq _hsq heq
  exact (show False by linarith only [hs, hq, heq]).elim

end Riesz.Asymptotics
