import Riesz.Negative.DiscrepancyBridge
import Riesz.Negative.CubeReverseRepair
import Riesz.Configuration.PositiveFiniteCellLaws

/-!
The actual iid residual mixture for the reverse cube
argument. The good-event law and its dominated scaled mean are displayed
inputs; their construction and quantitative energy bounds remain separate.
Neither a balanced output law nor its energy is assumed.
-/

noncomputable section
open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Configuration

/-- The compact-closure argument also labels every bounded Borel restriction. -/
theorem simple_bounded_restrict_representation (d : ℕ)
    (μ : Measure (Rd d)) (hμ : IsSimpleConfiguration d μ)
    (K : Set (Rd d)) (hK : MeasurableSet K) (hbounded : Bornology.IsBounded K) :
    ∃ n : ℕ, ∃ x : Fin n → Rd d, Function.Injective x ∧
      μ.restrict K = Riesz.Negative.tupleCounting d n x ∧ ∀ i, x i ∈ K := by
  rcases hμ with ⟨S, hS, rfl⟩
  have hfinite : (S ∩ K).Finite :=
    (hS (closure K) hbounded.isCompact_closure).subset
      (Set.inter_subset_inter_right S subset_closure)
  letI := hfinite.fintype
  let e : Fin (Fintype.card ↥(S ∩ K)) ≃ ↥(S ∩ K) := (Fintype.equivFin ↥(S ∩ K)).symm
  refine ⟨Fintype.card ↥(S ∩ K), fun i => (e i).val,
    Subtype.val_injective.comp e.injective,
    (restrict_sum_dirac d S K hK).trans ?_, fun i => (e i).property.2⟩
  simpa only [Measure.sum_fintype, Function.comp_def, Riesz.Negative.tupleCounting] using
    (Measure.sum_comp_equiv e (fun z : ↥(S ∩ K) => Measure.dirac z.val)).symm

/-- The existing measurable labels represent the actual half-open cube input. -/
theorem window_selected_bounded_label_spec (d : ℕ) (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ) (K : Set (Rd d))
    (hK : MeasurableSet K) (hbounded : Bornology.IsBounded K) :
    Function.Injective (windowLabel d (windowInputCount d K μ) (μ.restrict K)) ∧
      Riesz.Negative.tupleCounting d (windowInputCount d K μ)
        (windowLabel d (windowInputCount d K μ) (μ.restrict K)) = μ.restrict K ∧
      ∀ i, windowLabel d (windowInputCount d K μ) (μ.restrict K) i ∈ K := by
  obtain ⟨n, x, hx, hrep, hxK⟩ := simple_bounded_restrict_representation d μ hμ K hK hbounded
  have hmass : μ K = (n : ℝ≥0∞) := by
    simpa only [Measure.restrict_apply_univ, Riesz.Negative.tupleCounting_univ] using
      congrArg (fun ρ : Measure (Rd d) => ρ Set.univ) hrep
  have hn : windowInputCount d K μ = n := by simp [windowInputCount, hmass]
  rw [hn]
  have hl := windowLabel_spec d n (μ.restrict K) ⟨x, hx, hrep⟩
  refine ⟨hl.1, hl.2,
    (Riesz.Negative.tupleCounting_compl_eq_zero_iff d n _ K hK).mp ?_⟩
  simp only [hl.2, Measure.restrict_apply hK.compl, Set.compl_inter_self, measure_empty]

end Riesz.Configuration

namespace Riesz.Negative

/-- Restore the residual mean by an explicit fixed-count iid branch. -/
def cubeResidualIIDMixture (d m : ℕ) (A : ConfigurationLaw d)
    (θ : ℝ≥0∞) (ν : Measure (Rd d)) : ConfigurationLaw d :=
  let η := volume.restrict (cube d (m : ℝ)) - θ • ν
  θ • A + (η Set.univ * ((m ^ d : ℕ) : ℝ≥0∞)⁻¹) •
    iidCountingLaw d (m ^ d) ((η Set.univ)⁻¹ • η)

/-- The residual mixture has the exact original balanced predicate. The zero
residual branch needs no normalization to a probability measure. -/
theorem cubeResidualIIDMixture_balanced
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (A : ConfigurationLaw d) [IsFiniteMeasure A]
    (hA : ∀ᵐ μ ∂A, IsSimpleConfiguration d μ ∧
      μ (cube d (m : ℝ))ᶜ = 0 ∧ μ Set.univ = (m ^ d : ℕ))
    (ν : Measure (Rd d))
    (hmean : ∀ D : Set (Rd d), MeasurableSet D → (∫⁻ μ, μ D ∂A) = ν D)
    (θ : ℝ≥0∞) (hdom : θ • ν ≤ volume.restrict (cube d (m : ℝ))) :
    BalancedAdmissible d m (cubeResidualIIDMixture d m A θ ν) := by
  let ρ : Measure (Rd d) := volume.restrict (cube d (m : ℝ))
  let η : Measure (Rd d) := ρ - θ • ν
  let N : ℝ≥0∞ := (m ^ d : ℕ)
  have hN0 : N ≠ 0 := by
    dsimp only [N]
    exact_mod_cast (pow_pos hm d).ne'
  have hNtop : N ≠ ∞ := ENNReal.natCast_ne_top _
  letI : IsFiniteMeasure ρ := cube_background_isFiniteMeasure d m
  letI : NullSingletonClass ρ := cube_background_nullSingletonClass d m hd
  letI : IsFiniteMeasure (θ • ν) := isFiniteMeasure_of_le ρ hdom
  have hηle : η ≤ ρ := Measure.sub_le
  letI : IsFiniteMeasure η := isFiniteMeasure_of_le ρ hηle
  have hηadd : η + θ • ν = ρ := Measure.sub_add_cancel_of_le hdom
  have hρmass : ρ Set.univ = N := by
    simp only [ρ, N, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      volume_cube, ENNReal.ofReal_natCast, ← Nat.cast_pow]
  have hνmass : ν Set.univ = N * A Set.univ := by
    rw [← hmean Set.univ MeasurableSet.univ]
    calc
      _ = ∫⁻ _μ, N ∂A := lintegral_congr_ae (hA.mono (fun _ h => h.2.2))
      _ = _ := by rw [lintegral_const]
  have hmass : η Set.univ + (θ * A Set.univ) * N = N := by
    have h := congrArg (fun σ : Measure (Rd d) => σ Set.univ) hηadd
    simpa only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      hνmass, hρmass, mul_assoc, mul_comm, mul_left_comm] using h
  have hweights : θ * A Set.univ + η Set.univ * N⁻¹ = 1 := by
    calc
      _ = (η Set.univ + (θ * A Set.univ) * N) * N⁻¹ := by
        rw [add_mul, mul_assoc, ENNReal.mul_inv_cancel hN0 hNtop, mul_one]
        ac_rfl
      _ = 1 := by rw [hmass, ENNReal.mul_inv_cancel hN0 hNtop]
  have hρsupp : ρ (cube d (m : ℝ))ᶜ = 0 := by
    simp only [ρ, Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
      Set.compl_inter_self, measure_empty]
  have hηsupp : η (cube d (m : ℝ))ᶜ = 0 :=
    le_antisymm ((hηle _).trans_eq hρsupp) bot_le
  change BalancedAdmissible d m
    (θ • A + (η Set.univ * N⁻¹) • iidCountingLaw d (m ^ d) ((η Set.univ)⁻¹ • η))
  by_cases hη0 : η Set.univ = 0
  · simp only [hη0, zero_mul, zero_smul, add_zero]
    have hηzero : η = 0 := Measure.measure_univ_eq_zero.mp hη0
    have hθmass : θ * A Set.univ = 1 := by simpa only [hη0, zero_mul, add_zero] using hweights
    refine ⟨⟨by simpa only [Measure.smul_apply, smul_eq_mul] using hθmass⟩,
      Measure.ae_smul_measure hA θ, ?_⟩
    intro D hD
    rw [lintegral_smul_measure, smul_eq_mul, hmean D hD]
    have heq : θ • ν = ρ := by simpa only [hηzero, zero_add] using hηadd
    exact congrArg (fun σ : Measure (Rd d) => σ D) heq
  · let β : Measure (Rd d) := (η Set.univ)⁻¹ • η
    letI : IsProbabilityMeasure β := ⟨by
      simpa only [β, Measure.smul_apply, smul_eq_mul] using
        ENNReal.inv_mul_cancel hη0 (measure_ne_top η Set.univ)⟩
    letI : NullSingletonClass β := ⟨fun x => by
      have hx : η {x} = 0 := le_antisymm ((hηle {x}).trans_eq (measure_singleton x)) bot_le
      simp only [β, Measure.smul_apply, smul_eq_mul, hx, mul_zero]⟩
    have hβsupp : β (cube d (m : ℝ))ᶜ = 0 := by
      simp only [β, Measure.smul_apply, smul_eq_mul, hηsupp, mul_zero]
    obtain ⟨hBprob, hBclass, hBmean⟩ := iidCountingLaw_spec d (m ^ d) β
      (cube d (m : ℝ)) (measurableSet_cube d (m : ℝ)) hβsupp
    letI := hBprob
    refine ⟨⟨by
      simpa only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        measure_univ, mul_one] using hweights⟩,
      ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure hA θ,
        Measure.ae_smul_measure hBclass (η Set.univ * N⁻¹)⟩, ?_⟩
    intro D hD
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      smul_eq_mul, smul_eq_mul, hmean D hD, hBmean D hD]
    have hcancel : (η Set.univ * N⁻¹) * (((m ^ d : ℕ) : ℝ≥0∞) * β D) = η D := by
      simp only [β, Measure.smul_apply, smul_eq_mul]
      calc
        _ = (η Set.univ * (η Set.univ)⁻¹) * (N⁻¹ * N) * η D := by
          change (η Set.univ * N⁻¹) * (N * ((η Set.univ)⁻¹ * η D)) = _
          ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel hη0 (measure_ne_top η Set.univ),
          ENNReal.inv_mul_cancel hN0 hNtop, one_mul, one_mul]
    rw [hcancel]
    have heq := congrArg (fun σ : Measure (Rd d) => σ D) hηadd
    simpa only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, add_comm] using heq

/-- A finite fixed-count cube law has finite energy without a mean premise.
This applies to each branch before the residual mixture restores balance. -/
theorem cube_fixed_count_D_q_integrable_and_bounds
    (d m : ℕ) (q L : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (hdiam : ∀ x ∈ cube d (m : ℝ), ∀ y ∈ cube d (m : ℝ), ‖x - y‖ ≤ L)
    (P : ConfigurationLaw d) [IsFiniteMeasure P]
    (hP : ∀ᵐ μ ∂P, μ (cube d (m : ℝ))ᶜ = 0 ∧ μ Set.univ = ((m ^ d : ℕ) : ℝ≥0∞)) :
    Integrable (D_q d q m) P ∧
      (∀ᵐ μ ∂P, 0 ≤ D_q d q m μ ∧
        D_q d q m μ ≤ 2 * L ^ q * ((m ^ d : ℕ) : ℝ) ^ 2 / q) := by
  let ρ : Measure (Rd d) := volume.restrict (cube d (m : ℝ))
  letI : IsFiniteMeasure ρ := cube_background_isFiniteMeasure d m
  have hρmass : ρ Set.univ = (m ^ d : ℕ) := cube_background_mass d m
  have hρsupport : ρ (cube d (m : ℝ))ᶜ = 0 := by
    simp only [ρ, Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
      Set.compl_inter_self, measure_empty]
  have hbound : ∀ᵐ μ ∂P, 0 ≤ D_q d q m μ ∧
      D_q d q m μ ≤ 2 * L ^ q * ((m ^ d : ℕ) : ℝ) ^ 2 / q := by
    filter_upwards [hP] with μ hμ
    letI : IsFiniteMeasure μ := ⟨hμ.2.symm ▸ ENNReal.natCast_lt_top (m ^ d)⟩
    have hmass : μ.real Set.univ = ρ.real Set.univ :=
      congrArg ENNReal.toReal (hμ.2.trans hρmass.symm)
    have hμμ := Riesz.Analysis.ae_distance_le_of_concentrated μ μ
      (cube d (m : ℝ)) L hμ.1 hμ.1 hdiam
    have hμρ := Riesz.Analysis.ae_distance_le_of_concentrated μ ρ
      (cube d (m : ℝ)) L hμ.1 hρsupport hdiam
    have hρρ := Riesz.Analysis.ae_distance_le_of_concentrated ρ ρ
      (cube d (m : ℝ)) L hρsupport hρsupport hdiam
    refine ⟨Riesz.Analysis.D_q_nonneg_of_bounded d m q L hq hqTwo μ hmass
      hμμ hμρ hρρ, ?_⟩
    have hmreal : μ.real Set.univ = ((m ^ d : ℕ) : ℝ) := by
      rw [measureReal_def, hμ.2, ENNReal.toReal_natCast]
    have hρreal : ρ.real Set.univ = ((m ^ d : ℕ) : ℝ) := by
      rw [measureReal_def, hρmass, ENNReal.toReal_natCast]
    simpa only [hmreal, (show (volume.restrict (cube d (m : ℝ))).real Set.univ =
      ((m ^ d : ℕ) : ℝ) from hρreal), pow_two, mul_assoc] using
      D_q_le_of_bounded d m q L hq μ hμμ hμρ hρρ
  have hk : StronglyMeasurable (fun p : Rd d × Rd d => K_s (-q) ‖p.1 - p.2‖) := by
    simpa only [K_s, neg_neg, Pi.sub_apply] using
      (((measurable_fst.sub measurable_snd).norm.pow_const q).div_const (-q)).stronglyMeasurable
  have hmeas : AEStronglyMeasurable (D_q d q m) P := by
    refine (stronglyMeasurable_boundedQuadratic d (m ^ d) ρ
      (fun x y => K_s (-q) ‖x - y‖) hk).aestronglyMeasurable.congr ?_
    filter_upwards [hP] with μ hμ
    letI : IsFiniteMeasure μ := ⟨hμ.2.symm ▸ ENNReal.natCast_lt_top (m ^ d)⟩
    simpa only [boundedMeasureKernel, ProbabilityTheory.Kernel.coe_mk, if_pos hμ.2.le] using
      (Riesz.Analysis.D_q_eq_kernel_quadratic d m q L hq.le μ
        (Riesz.Analysis.ae_distance_le_of_concentrated μ μ
          (cube d (m : ℝ)) L hμ.1 hμ.1 hdiam)
        (Riesz.Analysis.ae_distance_le_of_concentrated μ ρ
          (cube d (m : ℝ)) L hμ.1 hρsupport hdiam)
        (Riesz.Analysis.ae_distance_le_of_concentrated ρ ρ
          (cube d (m : ℝ)) L hρsupport hρsupport hdiam)).symm
  refine ⟨(integrable_const (2 * L ^ q * ((m ^ d : ℕ) : ℝ) ^ 2 / q)).mono' hmeas ?_, hbound⟩
  exact hbound.mono (fun μ hμ => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hμ.1] using hμ.2)

/-- The actual residual mixture has the good-branch energy plus an explicit
fallback cost; fixed count and support suffice for the fallback estimate. -/
theorem cubeResidualIIDMixture_expected_energy_le
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) (q L : ℝ)
    (hq : 0 < q) (hqTwo : q < 2)
    (hdiam : ∀ x ∈ cube d (m : ℝ), ∀ y ∈ cube d (m : ℝ), ‖x - y‖ ≤ L)
    (A : ConfigurationLaw d) [IsFiniteMeasure A]
    (hA : ∀ᵐ μ ∂A, IsSimpleConfiguration d μ ∧
      μ (cube d (m : ℝ))ᶜ = 0 ∧ μ Set.univ = (m ^ d : ℕ))
    (ν : Measure (Rd d))
    (θ : ℝ≥0∞) (hθ : θ ≠ ∞) :
    let η := volume.restrict (cube d (m : ℝ)) - θ • ν
    (∫ μ, D_q d q m μ ∂cubeResidualIIDMixture d m A θ ν) ≤
      θ.toReal * (∫ μ, D_q d q m μ ∂A) +
        (η Set.univ * ((m ^ d : ℕ) : ℝ≥0∞)⁻¹).toReal *
          (2 * L ^ q * ((m ^ d : ℕ) : ℝ) ^ 2 / q) := by
  dsimp only
  let ρ : Measure (Rd d) := volume.restrict (cube d (m : ℝ))
  let η : Measure (Rd d) := ρ - θ • ν
  let N : ℝ≥0∞ := (m ^ d : ℕ)
  let r : ℝ≥0∞ := η Set.univ * N⁻¹
  let C : ℝ := 2 * L ^ q * ((m ^ d : ℕ) : ℝ) ^ 2 / q
  letI : IsFiniteMeasure ρ := cube_background_isFiniteMeasure d m
  letI : NullSingletonClass ρ := cube_background_nullSingletonClass d m hd
  have hηle : η ≤ ρ := Measure.sub_le
  letI : IsFiniteMeasure η := isFiniteMeasure_of_le ρ hηle
  have hN0 : N ≠ 0 := by
    dsimp only [N]
    exact_mod_cast (pow_pos hm d).ne'
  have hrfinite : r ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top η Set.univ)
    (ENNReal.inv_ne_top.mpr hN0)
  have hAi := (cube_fixed_count_D_q_integrable_and_bounds d m q L hq hqTwo
    hdiam A (hA.mono (fun _ h => h.2))).1
  change (∫ μ, D_q d q m μ ∂(θ • A + r •
      iidCountingLaw d (m ^ d) ((η Set.univ)⁻¹ • η))) ≤
    θ.toReal * (∫ μ, D_q d q m μ ∂A) + r.toReal * C
  by_cases hη0 : η Set.univ = 0
  · have hr0 : r = 0 := by simp only [r, hη0, zero_mul]
    simp only [hr0, zero_smul, add_zero, integral_smul_measure,
      smul_eq_mul, ENNReal.toReal_zero, zero_mul, le_refl]
  · let β : Measure (Rd d) := (η Set.univ)⁻¹ • η
    letI : IsProbabilityMeasure β := ⟨by
      simpa only [β, Measure.smul_apply, smul_eq_mul] using
        ENNReal.inv_mul_cancel hη0 (measure_ne_top η Set.univ)⟩
    letI : NullSingletonClass β := ⟨fun x => by
      have hx : η {x} = 0 := le_antisymm ((hηle {x}).trans_eq (measure_singleton x)) bot_le
      simp only [β, Measure.smul_apply, smul_eq_mul, hx, mul_zero]⟩
    have hρsupport : ρ (cube d (m : ℝ))ᶜ = 0 := by
      simp only [ρ, Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
        Set.compl_inter_self, measure_empty]
    have hβsupport : β (cube d (m : ℝ))ᶜ = 0 := by
      have hηsupport : η (cube d (m : ℝ))ᶜ = 0 :=
        le_antisymm ((hηle _).trans_eq hρsupport) bot_le
      simp only [β, Measure.smul_apply, smul_eq_mul, hηsupport, mul_zero]
    obtain ⟨hBprob, hBclass, _⟩ := iidCountingLaw_spec d (m ^ d) β
      (cube d (m : ℝ)) (measurableSet_cube d (m : ℝ)) hβsupport
    letI := hBprob
    obtain ⟨hBi, hBbound⟩ := cube_fixed_count_D_q_integrable_and_bounds d m q L hq hqTwo
      hdiam (iidCountingLaw d (m ^ d) β) (hBclass.mono (fun _ h => h.2))
    have hBcost : (∫ μ, D_q d q m μ ∂iidCountingLaw d (m ^ d) β) ≤ C := by
      have hi := integral_mono_ae hBi (integrable_const C) (hBbound.mono (fun _ h => h.2))
      simpa only [integral_const, probReal_univ, one_smul] using hi
    rw [integral_add_measure (hAi.smul_measure hθ) (hBi.smul_measure hrfinite),
      integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hBcost ENNReal.toReal_nonneg)

/-- The two tail bounds used for the actual good-event intensity and fallback.
They follow from the original second moment, before any normalization. -/
theorem square_tail_mass_and_mean_bounds {α : Type*} [MeasurableSpace α]
    (P : Measure α) [IsFiniteMeasure P] (D : α → ℝ) (hD : Measurable D)
    (hDi : Integrable D P) (hD2 : Integrable (fun x => D x ^ 2) P)
    (hmean : (∫ x, D x ∂P) = 0) (T : ℝ) (hT : 0 < T) :
    let B := {x | T < |D x|}
    let M := ∫ x, D x ^ 2 ∂P
    P.real B ≤ M / T ^ 2 ∧
      |∫ x in B, D x ∂P| ≤ M / T ∧
      |∫ x in Bᶜ, D x ∂P| ≤ M / T := by
  dsimp only
  let B : Set α := {x | T < |D x|}
  let M : ℝ := ∫ x, D x ^ 2 ∂P
  have hB : MeasurableSet B := measurableSet_lt measurable_const
    (by simpa only [Real.norm_eq_abs] using hD.norm)
  have hsub : (∫ x in B, D x ^ 2 ∂P) ≤ M :=
    setIntegral_le_integral hD2 (Filter.Eventually.of_forall (fun x => sq_nonneg (D x)))
  have hmass : P.real B ≤ M / T ^ 2 := by
    have hconst : (∫ _x in B, T ^ 2 ∂P) = P.real B * T ^ 2 := by
      simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
    have hpoint : ∀ᵐ x ∂P.restrict B, T ^ 2 ≤ D x ^ 2 := by
      filter_upwards [ae_restrict_mem hB] with x hx
      have hxT : T ≤ |D x| := (show T < |D x| from hx).le
      simpa only [sq_abs] using (sq_le_sq₀ hT.le (abs_nonneg (D x))).2 hxT
    have hle := (integral_mono_ae (integrable_const (T ^ 2)) hD2.integrableOn hpoint).trans hsub
    rw [hconst] at hle
    exact (le_div_iff₀ (sq_pos_of_pos hT)).2 hle
  have hbad : |∫ x in B, D x ∂P| ≤ M / T := by
    have hpoint : ∀ᵐ x ∂P.restrict B, |D x| ≤ D x ^ 2 / T := by
      filter_upwards [ae_restrict_mem hB] with x hx
      apply (le_div_iff₀ hT).2
      have hm := mul_le_mul_of_nonneg_right
        (show T ≤ |D x| from (show T < |D x| from hx).le) (abs_nonneg (D x))
      nlinarith only [hm, sq_abs (D x)]
    calc
      _ ≤ ∫ x in B, |D x| ∂P := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (f := D) (μ := P.restrict B))
      _ ≤ ∫ x in B, D x ^ 2 / T ∂P :=
        integral_mono_ae hDi.abs.integrableOn (hD2.div_const T).integrableOn hpoint
      _ = (∫ x in B, D x ^ 2 ∂P) / T := integral_div T _
      _ ≤ M / T := div_le_div_of_nonneg_right hsub hT.le
  have hgood : (∫ x in Bᶜ, D x ∂P) = -(∫ x in B, D x ∂P) := by
    have he := integral_add_compl hB hDi
    rw [hmean] at he
    linarith only [he]
  exact ⟨hmass, hbad, by rw [hgood, abs_neg]; exact hbad⟩

end Riesz.Negative
