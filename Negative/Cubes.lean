import Riesz.Analysis.NegativeGaussian
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.Prod

/-! Consequences of the concrete balanced-law predicates in `Showcase.lean`.
The finite-volume limit and its identification with the stationary infimum
are separate, still unproved targets. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal

namespace Riesz.Negative

theorem measurableSet_cube (d : ℕ) (L : ℝ) : MeasurableSet (cube d L) := by
  simpa only [cube, Set.setOf_forall, Set.preimage, Set.mem_Ico] using
    MeasurableSet.iInter (fun i : Fin d =>
      (measurableSet_Ico (a := (0 : ℝ)) (b := L)).preimage
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable)

theorem cube_isBounded (d : ℕ) (L : ℝ) : Bornology.IsBounded (cube d L) := by
  have hcompact : IsCompact ((WithLp.toLp (2 : ℝ≥0∞)) ''
      {x : Fin d → ℝ | ∀ i, x i ∈ Set.Icc 0 L}) :=
    (isCompact_pi_infinite (fun _ : Fin d => isCompact_Icc (a := (0 : ℝ)) (b := L))).image
      (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ))
  exact hcompact.isBounded.subset (fun x hx =>
    ⟨WithLp.ofLp x, fun i => ⟨(hx i).1, (hx i).2.le⟩, rfl⟩)

/-- The balanced mean and point count fix the volume of the background cube. -/
theorem balanced_background_mass (d m : ℕ) (P : ConfigurationLaw d)
    (hP : BalancedAdmissible d m P) :
    (volume.restrict (cube d (m : ℝ))) Set.univ = (m ^ d : ℕ) := by
  letI : IsProbabilityMeasure P := hP.1
  have hmass : (∫⁻ μ, μ Set.univ ∂P) = (m ^ d : ℕ) := by
    simpa only [lintegral_const, measure_univ, mul_one] using
      lintegral_congr_ae (hP.2.1.mono (fun μ hμ => hμ.2.2))
  exact (hP.2.2 Set.univ MeasurableSet.univ).symm.trans hmass

/-- The exact showcase cube energy is nonnegative almost surely for a balanced law. -/
theorem balanced_D_q_nonneg (d m : ℕ) (q : ℝ) (hq_pos : 0 < q) (hq_two : q < 2)
    (P : ConfigurationLaw d) (hP : BalancedAdmissible d m P) :
    ∀ᵐ μ ∂P, 0 ≤ D_q d q m μ := by
  have hbackground := balanced_background_mass d m P hP
  letI : IsFiniteMeasure (volume.restrict (cube d (m : ℝ))) :=
    ⟨hbackground.symm ▸ ENNReal.natCast_lt_top (m ^ d)⟩
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp (cube_isBounded d (m : ℝ))
  have hdiam : ∀ x ∈ cube d (m : ℝ), ∀ y ∈ cube d (m : ℝ), ‖x - y‖ ≤ L :=
    fun x hx y hy => by simpa only [dist_eq_norm] using hL hx hy
  have hsupport : (volume.restrict (cube d (m : ℝ))) (cube d (m : ℝ))ᶜ = 0 := by
    simp only [Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
      Set.compl_inter_self, measure_empty]
  filter_upwards [hP.2.1] with μ hμ
  letI : IsFiniteMeasure μ := ⟨hμ.2.2.symm ▸ ENNReal.natCast_lt_top (m ^ d)⟩
  have hequal : μ.real Set.univ = (volume.restrict (cube d (m : ℝ))).real Set.univ :=
    congrArg ENNReal.toReal (hμ.2.2.trans hbackground.symm)
  exact Riesz.Analysis.D_q_nonneg_of_bounded d m q L hq_pos hq_two μ hequal
    (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hμ.2.1 hμ.2.1 hdiam)
    (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hμ.2.1 hsupport hdiam)
    (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hsupport hsupport hdiam)

open scoped Classical

/-- A finite measurable kernel agreeing with every measure of mass at most `n`. -/
def boundedMeasureKernel (d n : ℕ) :
    ProbabilityTheory.Kernel (Measure (Rd d)) (Rd d) where
  toFun μ := if μ Set.univ ≤ (n : ℝ≥0∞) then μ else 0
  measurable' := by
    exact Measurable.ite
      (measurableSet_le (Measure.measurable_coe MeasurableSet.univ) measurable_const)
      measurable_id measurable_const

instance boundedMeasureKernel_isFinite (d n : ℕ) :
    ProbabilityTheory.IsFiniteKernel (boundedMeasureKernel d n) := by
  refine ⟨⟨n, ENNReal.natCast_lt_top n, ?_⟩⟩
  intro μ
  by_cases h : μ Set.univ ≤ (n : ℝ≥0∞) <;> simp [boundedMeasureKernel, h]

/-- Product-kernel integration makes the bounded quadratic energy measurable. -/
theorem stronglyMeasurable_boundedQuadratic (d n : ℕ) (ν : Measure (Rd d))
    [IsFiniteMeasure ν] (k : Rd d → Rd d → ℝ)
    (hk : StronglyMeasurable (fun p : Rd d × Rd d => k p.1 p.2)) :
    StronglyMeasurable (fun μ : Measure (Rd d) =>
      Riesz.Analysis.differenceKernelQuadratic k (boundedMeasureKernel d n μ) ν) := by
  have hA := hk.integral_kernel
    (κ := (boundedMeasureKernel d n).prod (boundedMeasureKernel d n))
  have hB := hk.integral_kernel
    (κ := (boundedMeasureKernel d n).prod (ProbabilityTheory.Kernel.const (Measure (Rd d)) ν))
  simpa only [Riesz.Analysis.differenceKernelQuadratic,
    ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.const_apply,
    Pi.sub_def, Pi.mul_def, Pi.add_def] using
    (hA.sub (stronglyMeasurable_const.mul hB)).add stronglyMeasurable_const

/-- A pointwise upper bound for the showcase energy on finite bounded configurations. -/
theorem D_q_le_of_bounded (d m : ℕ) (q L : ℝ) (hq : 0 < q)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    [IsFiniteMeasure (volume.restrict (cube d (m : ℝ)))]
    (hμμ : ∀ᵐ p : Rd d × Rd d ∂μ.prod μ, ‖p.1 - p.2‖ ≤ L)
    (hμν : ∀ᵐ p : Rd d × Rd d ∂μ.prod (volume.restrict (cube d (m : ℝ))),
      ‖p.1 - p.2‖ ≤ L)
    (hνν : ∀ᵐ p : Rd d × Rd d ∂(volume.restrict (cube d (m : ℝ))).prod
      (volume.restrict (cube d (m : ℝ))), ‖p.1 - p.2‖ ≤ L) :
    D_q d q m μ ≤ 2 * L ^ q * μ.real Set.univ *
      (volume.restrict (cube d (m : ℝ))).real Set.univ / q := by
  rw [Riesz.Analysis.D_q_eq_kernel_quadratic d m q L hq.le μ hμμ hμν hνν]
  have hbound := div_le_div_of_nonneg_right
    (Riesz.Analysis.neg_rpow_quadratic_le q L hq.le μ
      (volume.restrict (cube d (m : ℝ))) hμν) hq.le
  convert! hbound using 1
  simp only [Riesz.Analysis.differenceKernelQuadratic, K_s, neg_neg, div_neg,
    integral_neg, integral_div]
  ring

/-- A balanced cube law has a uniform bound on the absolute energy. -/
theorem balanced_D_q_bounded (d m : ℕ) (q : ℝ) (hq_pos : 0 < q) (hq_two : q < 2)
    (P : ConfigurationLaw d) (hP : BalancedAdmissible d m P) :
    ∃ C : ℝ, ∀ᵐ μ ∂P, ‖D_q d q m μ‖ ≤ C := by
  have hbackground := balanced_background_mass d m P hP
  letI : IsFiniteMeasure (volume.restrict (cube d (m : ℝ))) :=
    ⟨hbackground.symm ▸ ENNReal.natCast_lt_top (m ^ d)⟩
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp (cube_isBounded d (m : ℝ))
  refine ⟨2 * L ^ q * (volume.restrict (cube d (m : ℝ))).real Set.univ *
    (volume.restrict (cube d (m : ℝ))).real Set.univ / q, ?_⟩
  have hdiam : ∀ x ∈ cube d (m : ℝ), ∀ y ∈ cube d (m : ℝ), ‖x - y‖ ≤ L :=
    fun x hx y hy => by simpa only [dist_eq_norm] using hL hx hy
  have hsupport : (volume.restrict (cube d (m : ℝ))) (cube d (m : ℝ))ᶜ = 0 := by
    simp only [Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
      Set.compl_inter_self, measure_empty]
  filter_upwards [hP.2.1, balanced_D_q_nonneg d m q hq_pos hq_two P hP] with μ hμ hnonneg
  letI : IsFiniteMeasure μ := ⟨hμ.2.2.symm ▸ ENNReal.natCast_lt_top (m ^ d)⟩
  have hequal : μ.real Set.univ = (volume.restrict (cube d (m : ℝ))).real Set.univ :=
    congrArg ENNReal.toReal (hμ.2.2.trans hbackground.symm)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg, hequal] using
    D_q_le_of_bounded d m q L hq_pos μ
      (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hμ.2.1 hμ.2.1 hdiam)
      (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hμ.2.1 hsupport hdiam)
      (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hsupport hsupport hdiam)

/-- The exact showcase energy is a measurable random variable under a balanced law. -/
theorem balanced_D_q_aestronglyMeasurable (d m : ℕ) (q : ℝ) (hq_pos : 0 < q)
    (P : ConfigurationLaw d) (hP : BalancedAdmissible d m P) :
    AEStronglyMeasurable (D_q d q m) P := by
  have hbackground := balanced_background_mass d m P hP
  letI : IsFiniteMeasure (volume.restrict (cube d (m : ℝ))) :=
    ⟨hbackground.symm ▸ ENNReal.natCast_lt_top (m ^ d)⟩
  have hk : StronglyMeasurable (fun p : Rd d × Rd d => K_s (-q) ‖p.1 - p.2‖) := by
    simpa only [K_s, neg_neg, Pi.sub_apply] using
      (((measurable_fst.sub measurable_snd).norm.pow_const q).div_const (-q)).stronglyMeasurable
  have hmeas := stronglyMeasurable_boundedQuadratic d (m ^ d)
    (volume.restrict (cube d (m : ℝ))) (fun x y => K_s (-q) ‖x - y‖) hk
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp (cube_isBounded d (m : ℝ))
  refine hmeas.aestronglyMeasurable.congr ?_
  have hdiam : ∀ x ∈ cube d (m : ℝ), ∀ y ∈ cube d (m : ℝ), ‖x - y‖ ≤ L :=
    fun x hx y hy => by simpa only [dist_eq_norm] using hL hx hy
  have hsupport : (volume.restrict (cube d (m : ℝ))) (cube d (m : ℝ))ᶜ = 0 := by
    simp only [Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
      Set.compl_inter_self, measure_empty]
  filter_upwards [hP.2.1] with μ hμ
  letI : IsFiniteMeasure μ := ⟨hμ.2.2.symm ▸ ENNReal.natCast_lt_top (m ^ d)⟩
  simpa only [boundedMeasureKernel, ProbabilityTheory.Kernel.coe_mk, if_pos hμ.2.2.le] using
    (Riesz.Analysis.D_q_eq_kernel_quadratic d m q L hq_pos.le μ
      (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hμ.2.1 hμ.2.1 hdiam)
      (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hμ.2.1 hsupport hdiam)
      (Riesz.Analysis.ae_distance_le_of_concentrated _ _ _ L hsupport hsupport hdiam)).symm

/-- Expectations of the showcase energy are justified by absolute integrability. -/
theorem balanced_D_q_integrable (d m : ℕ) (q : ℝ) (hq_pos : 0 < q) (hq_two : q < 2)
    (P : ConfigurationLaw d) (hP : BalancedAdmissible d m P) :
    Integrable (D_q d q m) P := by
  letI : IsProbabilityMeasure P := hP.1
  obtain ⟨C, hC⟩ := balanced_D_q_bounded d m q hq_pos hq_two P hP
  exact (integrable_const C).mono'
    (balanced_D_q_aestronglyMeasurable d m q hq_pos P hP) hC

/-- A balanced law has a finite, well-defined, nonnegative expected energy. -/
theorem balanced_D_q_integrable_and_nonneg (d m : ℕ) (q : ℝ)
    (hq_pos : 0 < q) (hq_two : q < 2) (P : ConfigurationLaw d)
    (hP : BalancedAdmissible d m P) :
    Integrable (D_q d q m) P ∧ 0 ≤ (∫ μ, D_q d q m μ ∂P) := by
  exact ⟨balanced_D_q_integrable d m q hq_pos hq_two P hP,
    integral_nonneg_of_ae (balanced_D_q_nonneg d m q hq_pos hq_two P hP)⟩

/-- The showcase's finite-volume infimum is nonnegative, including its empty-set convention. -/
theorem b_nonneg (d m : ℕ) (q : ℝ) (hq_pos : 0 < q) (hq_two : q < 2) :
    0 ≤ b d q m := by
  apply Real.sInf_nonneg
  rintro r ⟨P, hP, rfl⟩
  exact (balanced_D_q_integrable_and_nonneg d m q hq_pos hq_two P hP).2

end Riesz.Negative
