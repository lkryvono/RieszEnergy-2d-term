import Riesz.Analysis.Gaussian
import Riesz.Analysis.GaussianQuadratic
import Mathlib.Tactic.Linarith

/-! Absolute-integral calculations for the negative Riesz kernel.
These supply the bounds needed to exchange the Gaussian and spatial integrals. -/

noncomputable section

open MeasureTheory RieszShowcase

namespace Riesz.Analysis

/-- The quadratic form of `μ - ν` for a symmetric kernel. -/
def differenceKernelQuadratic {α : Type*} [MeasurableSpace α]
    (k : α → α → ℝ) (μ ν : Measure α) : ℝ :=
  (∫ p : α × α, k p.1 p.2 ∂μ.prod μ) -
    2 * (∫ p : α × α, k p.1 p.2 ∂μ.prod ν) +
    (∫ p : α × α, k p.1 p.2 ∂ν.prod ν)

/-- The constant kernel integrates to the product of the two total masses. -/
theorem integral_one_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] :
    (∫ _ : α × β, (1 : ℝ) ∂μ.prod ν) = μ.real Set.univ * ν.real Set.univ := by
  simpa only [one_mul, integral_const, smul_eq_mul, mul_one] using
    (integral_prod_mul (μ := μ) (ν := ν) (fun _ : α => (1 : ℝ)) (fun _ : β => (1 : ℝ)))

/-- A constant kernel integrates to the constant times the product of the masses. -/
theorem integral_const_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (a : ℝ) (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] :
    (∫ _ : α × β, a ∂μ.prod ν) = a * μ.real Set.univ * ν.real Set.univ := by
  simpa only [mul_one, one_mul, integral_const, smul_eq_mul, mul_comm, mul_assoc] using
    (integral_prod_mul (μ := μ) (ν := ν) (fun _ : α => a) (fun _ : β => (1 : ℝ)))

/-- A symmetric kernel has a symmetric bilinear integral. -/
theorem integral_symmetric_kernel {α : Type*} [MeasurableSpace α]
    (k : α → α → ℝ) (hk : ∀ x y, k x y = k y x)
    (μ ν : Measure α) [SFinite μ] [SFinite ν] :
    (∫ p : α × α, k p.1 p.2 ∂μ.prod ν) = (∫ p : α × α, k p.1 p.2 ∂ν.prod μ) := by
  simpa only [Prod.swap, hk] using
    (integral_prod_swap (μ := μ) (ν := ν) (fun p : α × α => k p.1 p.2)).symm

/-- The Jordan expansion agrees with the quadratic form of the two Jordan parts. -/
theorem signedKernelQuadratic_eq_difference {α : Type*} [MeasurableSpace α]
    (k : α → α → ℝ) (hk : ∀ x y, k x y = k y x) (η : SignedMeasure α) :
    signedKernelQuadratic k η =
      differenceKernelQuadratic k η.toJordanDecomposition.posPart η.toJordanDecomposition.negPart := by
  unfold signedKernelQuadratic differenceKernelQuadratic
  rw [integral_symmetric_kernel k hk η.toJordanDecomposition.negPart η.toJordanDecomposition.posPart]
  ring

/-- Zero signed mass is equality of the masses of the two Jordan parts. -/
theorem jordan_masses_eq_of_zero {α : Type*} [MeasurableSpace α]
    (η : SignedMeasure α) (hmass : η Set.univ = 0) :
    η.toJordanDecomposition.posPart.real Set.univ =
      η.toJordanDecomposition.negPart.real Set.univ := by
  have h := congrArg (fun θ : SignedMeasure α => θ Set.univ)
    (SignedMeasure.toSignedMeasure_toJordanDecomposition η)
  simpa only [JordanDecomposition.toSignedMeasure,
    Measure.toSignedMeasure_sub_apply MeasurableSet.univ, sub_eq_zero] using h.trans hmass

/-- The subtracted negative-exponent kernel is integrable, also at zero distance. -/
theorem integrable_negative_kernel (s r : ℝ) (hs_lower : -2 < s)
    (hs_upper : s < 0) (hr : 0 ≤ r) :
    IntegrableOn (fun t : ℝ =>
      t ^ (s / 2 - 1) * (Real.exp (-(t * r ^ 2)) - 1)) (Set.Ioi 0) := by
  rcases eq_or_lt_of_le hr with hzero | hpos
  · subst r
    simp
  · exact integrable_negative_gamma_scaled (s / 2) (r ^ 2)
      (by linarith) (by linarith) (sq_pos_of_pos hpos)

/-- Exact absolute integral of the negative Gaussian kernel. -/
theorem integral_norm_negative_kernel (s r : ℝ) (hs_lower : -2 < s)
    (hs_upper : s < 0) (hr : 0 ≤ r) :
    (∫ t : ℝ in Set.Ioi 0,
      ‖t ^ (s / 2 - 1) * (Real.exp (-(t * r ^ 2)) - 1)‖) =
        -(K_s s r / gamma_s s) := by
  have hnorm : (∫ t : ℝ in Set.Ioi 0,
      ‖t ^ (s / 2 - 1) * (Real.exp (-(t * r ^ 2)) - 1)‖) =
        -(∫ t : ℝ in Set.Ioi 0,
          t ^ (s / 2 - 1) * (Real.exp (-(t * r ^ 2)) - 1)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply Real.norm_of_nonpos
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (Set.mem_Ioi.mp ht).le _)
      (sub_nonpos.mpr (Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg (Set.mem_Ioi.mp ht).le (sq_nonneg r)))))
  have hbase : (∫ t : ℝ in Set.Ioi 0,
      t ^ (s / 2 - 1) * (Real.exp (-(t * r ^ 2)) - 1)) = K_s s r / gamma_s s := by
    apply (eq_div_iff (gamma_s_pos s hs_lower).ne').mpr
    simpa only [mul_comm] using (gamma_kernel_neg_nonneg s r hs_lower hs_upper hr).symm
  rw [hnorm, hbase]

/-- A uniform absolute-integral bound when the distance is bounded. -/
theorem integral_norm_negative_kernel_le (s r L : ℝ) (hs_lower : -2 < s)
    (hs_upper : s < 0) (hr : 0 ≤ r) (hrL : r ≤ L) :
    (∫ t : ℝ in Set.Ioi 0,
      ‖t ^ (s / 2 - 1) * (Real.exp (-(t * r ^ 2)) - 1)‖) ≤
        -(K_s s L / gamma_s s) := by
  rw [integral_norm_negative_kernel s r hs_lower hs_upper hr]
  exact neg_le_neg (div_le_div_of_nonneg_right
    ((div_le_div_right_of_neg hs_upper).mpr
      (Real.rpow_le_rpow hr hrL (neg_nonneg.mpr hs_upper.le))) (gamma_s_pos s hs_lower).le)

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

omit [BorelSpace V] in
/-- Measures concentrated on a set inherit any bound on its pairwise distances. -/
theorem ae_distance_le_of_concentrated (μ ν : Measure V) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (S : Set V) (L : ℝ) (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L) :
    ∀ᵐ p : V × V ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L := by
  filter_upwards [show ∀ᵐ p : V × V ∂μ.prod ν, p ∈ S ×ˢ S from
    mem_ae_iff.mpr (Measure.measure_prod_compl_eq_zero hμ hν)] with p hp
  exact hdiam p.1 hp.1 p.2 hp.2

/-- A nonnegative power of distance is integrable for finite measures at bounded distance. -/
theorem integrable_rpow_distance (q L : ℝ) (hq : 0 ≤ q)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbound : ∀ᵐ p : V × V ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L) :
    Integrable (fun p : V × V => ‖p.1 - p.2‖ ^ q) (μ.prod ν) := by
  refine (integrable_const (L ^ q)).mono'
    ((continuous_fst.sub continuous_snd).norm.measurable.pow_const q).aestronglyMeasurable ?_
  filter_upwards [hbound] with p hp
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow (norm_nonneg _) hp hq

/-- The distance-power integral is bounded by the diameter power times the two masses. -/
theorem integral_rpow_distance_le (q L : ℝ) (hq : 0 ≤ q)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbound : ∀ᵐ p : V × V ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L) :
    (∫ p : V × V, ‖p.1 - p.2‖ ^ q ∂μ.prod ν) ≤
      L ^ q * μ.real Set.univ * ν.real Set.univ := by
  exact (integral_mono_ae (integrable_rpow_distance q L hq μ ν hbound) (integrable_const _)
    (hbound.mono (fun p hp => Real.rpow_le_rpow (norm_nonneg _) hp hq))).trans_eq
      (integral_const_prod (L ^ q) μ ν)

/-- Subtracting the constant Gaussian mode subtracts the product of the masses. -/
theorem integral_gaussian_sub_one (t : ℝ) (ht : 0 ≤ t)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ p : V × V, Real.exp (-(t * ‖p.1 - p.2‖ ^ 2)) - 1 ∂μ.prod ν) =
      (∫ p : V × V, Real.exp (-(t * ‖p.1 - p.2‖ ^ 2)) ∂μ.prod ν) -
        μ.real Set.univ * ν.real Set.univ := by
  have hgauss : Integrable (fun p : V × V => Real.exp (-(t * ‖p.1 - p.2‖ ^ 2)))
      (μ.prod ν) := by
    simpa only [neg_mul] using integrable_gaussian_prod_measure t ht μ ν
  rw [integral_sub hgauss (integrable_const (1 : ℝ)), integral_one_prod μ ν]

/-- The constant mode cancels in a discrepancy with zero total mass. -/
theorem gaussian_sub_one_quadratic_eq (t : ℝ) (ht : 0 ≤ t)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real Set.univ = ν.real Set.univ) :
    differenceKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2)) - 1) μ ν =
      differenceKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2))) μ ν := by
  unfold differenceKernelQuadratic
  rw [integral_gaussian_sub_one t ht μ μ, integral_gaussian_sub_one t ht μ ν,
    integral_gaussian_sub_one t ht ν ν, hmass]
  ring

/-- The joint negative kernel is integrable for finite measures at bounded distance. -/
theorem integrable_negative_kernel_prod (s L : ℝ) (hs_lower : -2 < s) (hs_upper : s < 0)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbound : ∀ᵐ p : V × V ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L) :
    Integrable (fun p : (V × V) × ℝ =>
      p.2 ^ (s / 2 - 1) * (Real.exp (-(p.2 * ‖p.1.1 - p.1.2‖ ^ 2)) - 1))
        ((μ.prod ν).prod (volume.restrict (Set.Ioi 0))) := by
  have hcont : Continuous (fun p : (V × V) × ℝ =>
      Real.exp (-(p.2 * ‖p.1.1 - p.1.2‖ ^ 2)) - 1) :=
    (Real.continuous_exp.comp
      (continuous_snd.mul ((continuous_fst.fst.sub continuous_fst.snd).norm.pow 2)).neg).sub
        continuous_const
  have hmeas : AEStronglyMeasurable (fun p : (V × V) × ℝ =>
      p.2 ^ (s / 2 - 1) * (Real.exp (-(p.2 * ‖p.1.1 - p.1.2‖ ^ 2)) - 1))
        ((μ.prod ν).prod (volume.restrict (Set.Ioi 0))) :=
    ((measurable_snd.pow_const (s / 2 - 1)).mul hcont.measurable).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).mpr ⟨ae_of_all _ (fun p =>
    integrable_negative_kernel s ‖p.1 - p.2‖ hs_lower hs_upper (norm_nonneg _)), ?_⟩
  refine (integrable_const (-(K_s s L / gamma_s s))).mono'
    hmeas.norm.integral_prod_right' ?_
  filter_upwards [hbound] with p hp
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact integral_norm_negative_kernel_le s ‖p.1 - p.2‖ L hs_lower hs_upper (norm_nonneg _) hp

/-- The weighted Gaussian profile is integrable over the scale parameter. -/
theorem integrable_negative_gaussian_profile (s L : ℝ) (hs_lower : -2 < s)
    (hs_upper : s < 0) (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbound : ∀ᵐ p : V × V ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L) :
    IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1) *
      (∫ p : V × V, Real.exp (-(t * ‖p.1 - p.2‖ ^ 2)) - 1 ∂μ.prod ν)) (Set.Ioi 0) := by
  simpa only [IntegrableOn, integral_const_mul] using
    (integrable_negative_kernel_prod s L hs_lower hs_upper μ ν hbound).integral_prod_right

/-- The measure-level Gamma identity, with Fubini justified by bounded distance. -/
theorem integral_negative_riesz_kernel_eq (s L : ℝ) (hs_lower : -2 < s) (hs_upper : s < 0)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbound : ∀ᵐ p : V × V ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L) :
    (∫ p : V × V, K_s s ‖p.1 - p.2‖ ∂μ.prod ν) =
      gamma_s s * (∫ t : ℝ in Set.Ioi 0, t ^ (s / 2 - 1) *
        (∫ p : V × V, Real.exp (-(t * ‖p.1 - p.2‖ ^ 2)) - 1 ∂μ.prod ν)) := by
  have hpoint : (fun p : V × V => K_s s ‖p.1 - p.2‖) =
      (fun p : V × V => gamma_s s * (∫ t : ℝ in Set.Ioi 0,
        t ^ (s / 2 - 1) * (Real.exp (-(t * ‖p.1 - p.2‖ ^ 2)) - 1))) := by
    funext p
    exact gamma_kernel_neg_nonneg s ‖p.1 - p.2‖ hs_lower hs_upper (norm_nonneg _)
  rw [hpoint, integral_const_mul]
  congr 1
  rw [integral_integral_swap (integrable_negative_kernel_prod s L hs_lower hs_upper μ ν hbound)]
  exact integral_congr_ae (ae_of_all _ (fun t => integral_const_mul (t ^ (s / 2 - 1))
    (fun p : V × V => Real.exp (-(t * ‖p.1 - p.2‖ ^ 2)) - 1)))

/-- Spatial integrability of the negative Riesz kernel under the same distance bound. -/
theorem integrable_negative_riesz_kernel (s L : ℝ) (hs_lower : -2 < s) (hs_upper : s < 0)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbound : ∀ᵐ p : V × V ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L) :
    Integrable (fun p : V × V => K_s s ‖p.1 - p.2‖) (μ.prod ν) := by
  convert! (integrable_negative_kernel_prod s L hs_lower hs_upper μ ν hbound).integral_prod_left.const_mul
    (gamma_s s) using 1
  funext p
  exact gamma_kernel_neg_nonneg s ‖p.1 - p.2‖ hs_lower hs_upper (norm_nonneg _)

/-- The negative Riesz discrepancy is an integral of Gaussian discrepancies.
Equal total masses remove the constant mode; bounded distances justify Fubini. -/
theorem negative_riesz_quadratic_eq (s L : ℝ) (hs_lower : -2 < s) (hs_upper : s < 0)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real Set.univ = ν.real Set.univ)
    (hμμ : ∀ᵐ p : V × V ∂μ.prod μ, ‖p.1 - p.2‖ ≤ L)
    (hμν : ∀ᵐ p : V × V ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L)
    (hνν : ∀ᵐ p : V × V ∂ν.prod ν, ‖p.1 - p.2‖ ≤ L) :
    differenceKernelQuadratic (fun x y : V => K_s s ‖x - y‖) μ ν =
      gamma_s s * (∫ t : ℝ in Set.Ioi 0, t ^ (s / 2 - 1) *
        differenceKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2))) μ ν) := by
  have hA := integrable_negative_gaussian_profile s L hs_lower hs_upper μ μ hμμ
  have hB := integrable_negative_gaussian_profile s L hs_lower hs_upper μ ν hμν
  have hC := integrable_negative_gaussian_profile s L hs_lower hs_upper ν ν hνν
  have hremove : (fun t : ℝ => t ^ (s / 2 - 1) *
      differenceKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2))) μ ν) =ᵐ[
        volume.restrict (Set.Ioi 0)] (fun t : ℝ => t ^ (s / 2 - 1) *
      differenceKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2)) - 1) μ ν) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [gaussian_sub_one_quadratic_eq t (Set.mem_Ioi.mp ht).le μ ν hmass]
  rw [integral_congr_ae hremove]
  unfold differenceKernelQuadratic
  rw [integral_negative_riesz_kernel_eq s L hs_lower hs_upper μ μ hμμ,
    integral_negative_riesz_kernel_eq s L hs_lower hs_upper μ ν hμν,
    integral_negative_riesz_kernel_eq s L hs_lower hs_upper ν ν hνν]
  simp_rw [mul_add, mul_sub, mul_left_comm]
  rw [integral_add (f := fun t : ℝ =>
    t ^ (s / 2 - 1) * (∫ p : V × V, Real.exp (-(t * ‖p.1 - p.2‖ ^ 2)) - 1 ∂μ.prod μ) -
      2 * (t ^ (s / 2 - 1) * (∫ p : V × V, Real.exp (-(t * ‖p.1 - p.2‖ ^ 2)) - 1 ∂μ.prod ν)))
        (hA.sub (hB.const_mul 2)) hC, integral_sub hA (hB.const_mul 2), integral_const_mul]
  ring

/-- An upper bound for the negative of the distance-power discrepancy form. -/
theorem neg_rpow_quadratic_le (q L : ℝ) (hq : 0 ≤ q)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbound : ∀ᵐ p : V × V ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L) :
    -differenceKernelQuadratic (fun x y : V => ‖x - y‖ ^ q) μ ν ≤
      2 * L ^ q * μ.real Set.univ * ν.real Set.univ := by
  have hA : 0 ≤ (∫ p : V × V, ‖p.1 - p.2‖ ^ q ∂μ.prod μ) :=
    integral_nonneg (fun p => Real.rpow_nonneg (norm_nonneg _) _)
  have hC : 0 ≤ (∫ p : V × V, ‖p.1 - p.2‖ ^ q ∂ν.prod ν) :=
    integral_nonneg (fun p => Real.rpow_nonneg (norm_nonneg _) _)
  have hB := integral_rpow_distance_le q L hq μ ν hbound
  unfold differenceKernelQuadratic
  linarith

omit [BorelSpace V] [SecondCountableTopology V] in
/-- Every kernel that depends only on distance has a symmetric Jordan expansion. -/
theorem signed_distance_quadratic_eq (f : ℝ → ℝ) (η : SignedMeasure V) :
    signedKernelQuadratic (fun x y : V => f ‖x - y‖) η =
      differenceKernelQuadratic (fun x y : V => f ‖x - y‖)
        η.toJordanDecomposition.posPart η.toJordanDecomposition.negPart := by
  exact signedKernelQuadratic_eq_difference _ (fun x y => congrArg f (norm_sub_rev x y)) η

omit [BorelSpace V] [SecondCountableTopology V] in
/-- The Gaussian Jordan expansion in difference form. -/
theorem signed_gaussian_quadratic_eq (t : ℝ) (η : SignedMeasure V) :
    signedKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2))) η =
      differenceKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2)))
        η.toJordanDecomposition.posPart η.toJordanDecomposition.negPart := by
  exact signed_distance_quadratic_eq (fun r => Real.exp (-(t * r ^ 2))) η

/-- The Gaussian representation for a signed zero-mass discrepancy on a bounded set. -/
theorem negative_signed_quadratic_eq (s L : ℝ) (hs_lower : -2 < s) (hs_upper : s < 0)
    (η : SignedMeasure V) (hmass : η Set.univ = 0) (S : Set V)
    (hsupport : η.totalVariation Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L) :
    signedKernelQuadratic (fun x y : V => K_s s ‖x - y‖) η =
      gamma_s s * (∫ t : ℝ in Set.Ioi 0, t ^ (s / 2 - 1) *
        signedKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2))) η) := by
  have hparts : η.toJordanDecomposition.posPart Sᶜ = 0 ∧
      η.toJordanDecomposition.negPart Sᶜ = 0 := by
    simpa only [SignedMeasure.totalVariation, Measure.add_apply, add_eq_zero] using hsupport
  simp_rw [signed_distance_quadratic_eq (K_s s) η, signed_gaussian_quadratic_eq]
  exact negative_riesz_quadratic_eq s L hs_lower hs_upper
    η.toJordanDecomposition.posPart η.toJordanDecomposition.negPart (jordan_masses_eq_of_zero η hmass)
    (ae_distance_le_of_concentrated _ _ S L hparts.1 hparts.1 hdiam)
    (ae_distance_le_of_concentrated _ _ S L hparts.1 hparts.2 hdiam)
    (ae_distance_le_of_concentrated _ _ S L hparts.2 hparts.2 hdiam)

/-- The paper's `D_q(η)`, with the signed product integral expanded into Jordan parts. -/
def signedDiscrepancyEnergy (q : ℝ) (η : SignedMeasure V) : ℝ :=
  -(1 / q) * signedKernelQuadratic (fun x y : V => ‖x - y‖ ^ q) η

omit [BorelSpace V] [SecondCountableTopology V] in
/-- `D_q` is exactly the signed quadratic form for `K_{-q}`. -/
theorem signedDiscrepancyEnergy_eq_kernel (q : ℝ) (η : SignedMeasure V) :
    signedDiscrepancyEnergy q η = signedKernelQuadratic (fun x y : V => K_s (-q) ‖x - y‖) η := by
  simp only [signedDiscrepancyEnergy, signedKernelQuadratic, K_s, neg_neg, div_neg,
    integral_neg, integral_div]
  ring

/-- The diameter and total-variation bound from the proof of Lemma `gamma`.
The upper estimate itself does not require zero signed mass or `q < 2`. -/
theorem signedDiscrepancyEnergy_le (q L : ℝ) (hq : 0 < q) (hL : 0 ≤ L)
    (η : SignedMeasure V) (S : Set V) (hsupport : η.totalVariation Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L) :
    signedDiscrepancyEnergy q η ≤ L ^ q * (η.totalVariation.real Set.univ) ^ 2 / q := by
  let μ := η.toJordanDecomposition.posPart
  let ν := η.toJordanDecomposition.negPart
  have hparts : μ Sᶜ = 0 ∧ ν Sᶜ = 0 := by
    simpa only [SignedMeasure.totalVariation, Measure.add_apply, add_eq_zero] using hsupport
  have hcross := neg_rpow_quadratic_le q L hq.le μ ν
    (ae_distance_le_of_concentrated μ ν S L hparts.1 hparts.2 hdiam)
  have hsquare : 2 * μ.real Set.univ * ν.real Set.univ ≤
      (μ.real Set.univ + ν.real Set.univ) ^ 2 := by
    nlinarith [sq_nonneg (μ.real Set.univ), sq_nonneg (ν.real Set.univ)]
  have hweight : 2 * L ^ q * μ.real Set.univ * ν.real Set.univ ≤
      L ^ q * (μ.real Set.univ + ν.real Set.univ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsquare (Real.rpow_nonneg hL q)]
  rw [signedDiscrepancyEnergy, signed_distance_quadratic_eq (fun r => r ^ q) η,
    SignedMeasure.totalVariation, measureReal_add_apply]
  convert! div_le_div_of_nonneg_right (hcross.trans hweight) hq.le using 1
  ring

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Nonnegativity of the negative Riesz energy of an equal-mass discrepancy. -/
theorem negative_riesz_quadratic_nonneg (s L : ℝ) (hs_lower : -2 < s) (hs_upper : s < 0)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real Set.univ = ν.real Set.univ)
    (hμμ : ∀ᵐ p : V × V ∂μ.prod μ, ‖p.1 - p.2‖ ≤ L)
    (hμν : ∀ᵐ p : V × V ∂μ.prod ν, ‖p.1 - p.2‖ ≤ L)
    (hνν : ∀ᵐ p : V × V ∂ν.prod ν, ‖p.1 - p.2‖ ≤ L) :
    0 ≤ differenceKernelQuadratic (fun x y : V => K_s s ‖x - y‖) μ ν := by
  rw [negative_riesz_quadratic_eq s L hs_lower hs_upper μ ν hmass hμμ hμν hνν]
  refine mul_nonneg (gamma_s_pos s hs_lower).le (integral_nonneg_of_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  refine mul_nonneg (Real.rpow_nonneg (Set.mem_Ioi.mp ht).le _) ?_
  simpa only [differenceKernelQuadratic, neg_mul] using
    gaussian_quadratic_nonneg t (Set.mem_Ioi.mp ht) μ ν

/-- Positivity for a signed zero-mass discrepancy concentrated on a bounded set. -/
theorem negative_signed_quadratic_nonneg (s L : ℝ) (hs_lower : -2 < s) (hs_upper : s < 0)
    (η : SignedMeasure V) (hmass : η Set.univ = 0) (S : Set V)
    (hsupport : η.totalVariation Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L) :
    0 ≤ signedKernelQuadratic (fun x y : V => K_s s ‖x - y‖) η := by
  rw [negative_signed_quadratic_eq s L hs_lower hs_upper η hmass S hsupport hdiam]
  refine mul_nonneg (gamma_s_pos s hs_lower).le (integral_nonneg_of_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  refine mul_nonneg (Real.rpow_nonneg (Set.mem_Ioi.mp ht).le _) ?_
  simpa only [neg_mul] using gaussian_signed_quadratic_nonneg t (Set.mem_Ioi.mp ht) η

/-- The compactly supported signed-measure assertion of Lemma `gamma`, in `D_q` notation. -/
theorem signedDiscrepancyEnergy_gaussian_compact (q : ℝ) (hq_pos : 0 < q) (hq_two : q < 2)
    (η : SignedMeasure V) (hmass : η Set.univ = 0) (S : Set V)
    (hcompact : IsCompact S) (hsupport : η.totalVariation Sᶜ = 0) :
    signedDiscrepancyEnergy q η =
      gamma_s (-q) * (∫ t : ℝ in Set.Ioi 0, t ^ (-q / 2 - 1) *
        signedKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2))) η) ∧
      0 ≤ signedDiscrepancyEnergy q η := by
  obtain ⟨L, hL⟩ := Metric.isBounded_iff.mp hcompact.isBounded
  have hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L := fun x hx y hy => by
    simpa only [dist_eq_norm] using hL hx hy
  rw [signedDiscrepancyEnergy_eq_kernel]
  exact ⟨negative_signed_quadratic_eq (-q) L (neg_lt_neg hq_two) (neg_lt_zero.mpr hq_pos)
    η hmass S hsupport hdiam,
    negative_signed_quadratic_nonneg (-q) L (neg_lt_neg hq_two) (neg_lt_zero.mpr hq_pos)
      η hmass S hsupport hdiam⟩

/-- The complete finite bound used later in the paper's negative-exponent arguments. -/
theorem signedDiscrepancyEnergy_bounds (q L : ℝ) (hq_pos : 0 < q) (hq_two : q < 2)
    (hL : 0 ≤ L) (η : SignedMeasure V) (hmass : η Set.univ = 0) (S : Set V)
    (hsupport : η.totalVariation Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L) :
    0 ≤ signedDiscrepancyEnergy q η ∧
      signedDiscrepancyEnergy q η ≤ L ^ q * (η.totalVariation.real Set.univ) ^ 2 / q := by
  refine ⟨?_, signedDiscrepancyEnergy_le q L hq_pos hL η S hsupport hdiam⟩
  rw [signedDiscrepancyEnergy_eq_kernel]
  exact negative_signed_quadratic_nonneg (-q) L (neg_lt_neg hq_two) (neg_lt_zero.mpr hq_pos)
    η hmass S hsupport hdiam

/-- All assertions of the paper's scalar Gamma and quadratic-positivity lemma.
The compact-support predicate is expressed using the total variation measure. -/
theorem gamma_kernel_and_quadratic_positivity :
    (∀ s r : ℝ, 0 < s → 0 < r → K_s s r = gamma_s s *
      (∫ t : ℝ in Set.Ioi 0, t ^ (s / 2 - 1) * Real.exp (-(t * r ^ 2)))) ∧
    (∀ s r : ℝ, -2 < s → s < 0 → 0 ≤ r → K_s s r = gamma_s s *
      (∫ t : ℝ in Set.Ioi 0, t ^ (s / 2 - 1) * (Real.exp (-(t * r ^ 2)) - 1))) ∧
    (∀ t : ℝ, 0 < t → ∀ η : SignedMeasure V,
      0 ≤ signedKernelQuadratic (fun x y : V => Real.exp (-t * ‖x - y‖ ^ 2)) η) ∧
    (∀ q : ℝ, 0 < q → q < 2 → ∀ η : SignedMeasure V, η Set.univ = 0 →
      ∀ S : Set V, IsCompact S → η.totalVariation Sᶜ = 0 →
      signedDiscrepancyEnergy q η = gamma_s (-q) *
        (∫ t : ℝ in Set.Ioi 0, t ^ (-q / 2 - 1) *
          signedKernelQuadratic (fun x y : V => Real.exp (-(t * ‖x - y‖ ^ 2))) η) ∧
        0 ≤ signedDiscrepancyEnergy q η) := by
  exact ⟨gamma_kernel_pos, gamma_kernel_neg_nonneg, gaussian_signed_quadratic_nonneg,
    signedDiscrepancyEnergy_gaussian_compact⟩

/-- The showcase's three iterated cube integrals equal the `K_{-q}` quadratic form.
Finiteness and all three distance bounds are explicit hypotheses here. -/
theorem D_q_eq_kernel_quadratic (d m : ℕ) (q L : ℝ) (hq : 0 ≤ q)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    [IsFiniteMeasure (volume.restrict (cube d (m : ℝ)))]
    (hμμ : ∀ᵐ p : Rd d × Rd d ∂μ.prod μ, ‖p.1 - p.2‖ ≤ L)
    (hμν : ∀ᵐ p : Rd d × Rd d ∂μ.prod (volume.restrict (cube d (m : ℝ))),
      ‖p.1 - p.2‖ ≤ L)
    (hνν : ∀ᵐ p : Rd d × Rd d ∂(volume.restrict (cube d (m : ℝ))).prod
      (volume.restrict (cube d (m : ℝ))), ‖p.1 - p.2‖ ≤ L) :
    D_q d q m μ = differenceKernelQuadratic (fun x y : Rd d => K_s (-q) ‖x - y‖)
      μ (volume.restrict (cube d (m : ℝ))) := by
  simp only [D_q, differenceKernelQuadratic, K_s, neg_neg, div_neg, integral_neg, integral_div]
  rw [integral_prod _ (integrable_rpow_distance q L hq μ μ hμμ),
    integral_prod _ (integrable_rpow_distance q L hq μ (volume.restrict (cube d (m : ℝ))) hμν),
    integral_prod _ (integrable_rpow_distance q L hq (volume.restrict (cube d (m : ℝ)))
      (volume.restrict (cube d (m : ℝ))) hνν)]
  ring

/-- Nonnegativity of the exact showcase cube energy under finite, equal-mass bounds.
The balanced-law predicates still need to be shown to supply these hypotheses. -/
theorem D_q_nonneg_of_bounded (d m : ℕ) (q L : ℝ) (hq_pos : 0 < q) (hq_two : q < 2)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    [IsFiniteMeasure (volume.restrict (cube d (m : ℝ)))]
    (hmass : μ.real Set.univ = (volume.restrict (cube d (m : ℝ))).real Set.univ)
    (hμμ : ∀ᵐ p : Rd d × Rd d ∂μ.prod μ, ‖p.1 - p.2‖ ≤ L)
    (hμν : ∀ᵐ p : Rd d × Rd d ∂μ.prod (volume.restrict (cube d (m : ℝ))),
      ‖p.1 - p.2‖ ≤ L)
    (hνν : ∀ᵐ p : Rd d × Rd d ∂(volume.restrict (cube d (m : ℝ))).prod
      (volume.restrict (cube d (m : ℝ))), ‖p.1 - p.2‖ ≤ L) :
    0 ≤ D_q d q m μ := by
  rw [D_q_eq_kernel_quadratic d m q L hq_pos.le μ hμμ hμν hνν]
  exact negative_riesz_quadratic_nonneg (-q) L (neg_lt_neg hq_two) (neg_lt_zero.mpr hq_pos)
    μ (volume.restrict (cube d (m : ℝ))) hmass hμμ hμν hνν

end Riesz.Analysis
