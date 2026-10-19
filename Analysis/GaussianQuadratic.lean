import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Gaussian convolution calculations for the quadratic-positivity part
of Lemma `gamma` in the paper. -/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Riesz.Analysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Completing the square in two squared Euclidean distances. -/
theorem gaussian_complete_square (x y z : V) :
    ‖x - z‖ ^ 2 + ‖y - z‖ ^ 2 =
      2 * ‖z - (1 / 2 : ℝ) • (x + y)‖ ^ 2 + ‖x - y‖ ^ 2 / 2 := by
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    real_inner_smul_right, inner_add_right]
  norm_num only [abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num), mul_pow,
    norm_add_sq_real, real_inner_comm]
  ring

/-- Pointwise Gaussian factorization after completing the square. -/
theorem gaussian_product (t : ℝ) (x y z : V) :
    Real.exp (-2 * t * ‖x - z‖ ^ 2) * Real.exp (-2 * t * ‖y - z‖ ^ 2) =
      Real.exp (-t * ‖x - y‖ ^ 2) *
        Real.exp (-4 * t * ‖z - (1 / 2 : ℝ) • (x + y)‖ ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [← mul_add (-2 * t), gaussian_complete_square]
  ring

omit [InnerProductSpace ℝ V] in
/-- A Gaussian kernel is bounded by one at every pair of points. -/
theorem norm_gaussian_le_one (t : ℝ) (ht : 0 ≤ t) (x y : V) :
    ‖Real.exp (-t * ‖x - y‖ ^ 2)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _))

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The integral form of the completed-square Gaussian product. -/
theorem integral_gaussian_product (t : ℝ) (ht : 0 < t) (x y : V) :
    (∫ z : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) * Real.exp (-2 * t * ‖y - z‖ ^ 2)) =
      Real.exp (-t * ‖x - y‖ ^ 2) *
        (Real.pi / (4 * t)) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  simp_rw [gaussian_product]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun z : V => Real.exp (-4 * t * ‖z‖ ^ 2)) ((1 / 2 : ℝ) • (x + y))]
  rw [show (-4 : ℝ) * t = -(4 * t) from by ring,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) (b := 4 * t) (by positivity)]

/-- The Gaussian convolution identity with the normalization used in the paper. -/
theorem gaussian_convolution (t : ℝ) (ht : 0 < t) (x y : V) :
    Real.exp (-t * ‖x - y‖ ^ 2) =
      (4 * t / Real.pi) ^ ((Module.finrank ℝ V : ℝ) / 2) *
        (∫ z : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) *
          Real.exp (-2 * t * ‖y - z‖ ^ 2)) := by
  rw [integral_gaussian_product t ht x y, ← inv_div (4 * t) Real.pi,
    Real.inv_rpow (by positivity)]
  rw [mul_left_comm, mul_inv_cancel₀
    (Real.rpow_pos_of_pos (show 0 < 4 * t / Real.pi by positivity) _).ne', mul_one]

/-- The completed-square product is integrable over the intermediate point. -/
theorem integrable_gaussian_product (t : ℝ) (ht : 0 < t) (x y : V) :
    Integrable (fun z : V => Real.exp (-2 * t * ‖x - z‖ ^ 2) *
      Real.exp (-2 * t * ‖y - z‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gaussian_product t ht x y]
  exact mul_ne_zero (Real.exp_pos _).ne'
    (Real.rpow_pos_of_pos (show 0 < Real.pi / (4 * t) by positivity) _).ne'

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Integrability of a Gaussian test against an arbitrary finite measure. -/
theorem integrable_gaussian_finite_measure (t : ℝ) (ht : 0 ≤ t) (x : V)
    (μ : Measure V) [IsFiniteMeasure μ] :
    Integrable (fun y : V => Real.exp (-t * ‖x - y‖ ^ 2)) μ := by
  refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all μ (fun y => norm_gaussian_le_one t ht x y))
  exact (Real.continuous_exp.comp
    (continuous_const.mul ((continuous_const.sub continuous_id).norm.pow 2))).aestronglyMeasurable

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Integrability of the kernel on the product of any two finite measures. -/
theorem integrable_gaussian_prod_measure [SecondCountableTopology V] (t : ℝ) (ht : 0 ≤ t)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun p : V × V => Real.exp (-t * ‖p.1 - p.2‖ ^ 2)) (μ.prod ν) := by
  refine (integrable_const (1 : ℝ)).mono' ?_
    (ae_of_all (μ.prod ν) (fun p => norm_gaussian_le_one t ht p.1 p.2))
  exact (Real.continuous_exp.comp
    (continuous_const.mul ((continuous_fst.sub continuous_snd).norm.pow 2))).aestronglyMeasurable

/-- Absolute integrability needed to apply Fubini to the Gaussian factorization. -/
theorem integrable_gaussian_triple (t : ℝ) (ht : 0 < t)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun p : (V × V) × V =>
      Real.exp (-2 * t * ‖p.1.1 - p.2‖ ^ 2) *
        Real.exp (-2 * t * ‖p.1.2 - p.2‖ ^ 2)) ((μ.prod ν).prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : (V × V) × V =>
      Real.exp (-2 * t * ‖p.1.1 - p.2‖ ^ 2) *
        Real.exp (-2 * t * ‖p.1.2 - p.2‖ ^ 2)) ((μ.prod ν).prod volume) :=
    ((Real.continuous_exp.comp
      (continuous_const.mul ((continuous_fst.fst.sub continuous_snd).norm.pow 2))).mul
      (Real.continuous_exp.comp
        (continuous_const.mul ((continuous_fst.snd.sub continuous_snd).norm.pow 2)))).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).mpr ⟨ae_of_all _ (fun p =>
    integrable_gaussian_product t ht p.1 p.2), ?_⟩
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  simp_rw [integral_gaussian_product t ht]
  exact (integrable_gaussian_prod_measure t ht.le μ ν).mul_const _

/-- Integrating the Gaussian factorization against two finite measures. -/
theorem gaussian_bilinear_factorization (t : ℝ) (ht : 0 < t)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ p : V × V, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂μ.prod ν) =
      (4 * t / Real.pi) ^ ((Module.finrank ℝ V : ℝ) / 2) *
        (∫ z : V, (∫ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂μ) *
          (∫ y : V, Real.exp (-2 * t * ‖y - z‖ ^ 2) ∂ν)) := by
  simp_rw [gaussian_convolution t ht]
  rw [integral_const_mul]
  congr 1
  rw [integral_integral_swap (integrable_gaussian_triple t ht μ ν)]
  exact integral_congr_ae (ae_of_all _ (fun z => integral_prod_mul
    (fun x : V => Real.exp (-2 * t * ‖x - z‖ ^ 2))
    (fun y : V => Real.exp (-2 * t * ‖y - z‖ ^ 2))))

/-- Integrability of the product of the two Gaussian smoothings. -/
theorem integrable_gaussian_smoothing_product (t : ℝ) (ht : 0 < t)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun z : V =>
      (∫ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂μ) *
        (∫ y : V, Real.exp (-2 * t * ‖y - z‖ ^ 2) ∂ν)) := by
  convert! (integrable_gaussian_triple t ht μ ν).integral_prod_right using 1
  ext z
  exact (integral_prod_mul (fun x : V => Real.exp (-2 * t * ‖x - z‖ ^ 2))
    (fun y : V => Real.exp (-2 * t * ‖y - z‖ ^ 2))).symm

/-- The Gaussian quadratic form of the difference of two finite measures is a square. -/
theorem gaussian_quadratic_eq_integral_square (t : ℝ) (ht : 0 < t)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ p : V × V, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂μ.prod μ) -
        2 * (∫ p : V × V, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂μ.prod ν) +
        (∫ p : V × V, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂ν.prod ν) =
      (4 * t / Real.pi) ^ ((Module.finrank ℝ V : ℝ) / 2) *
        (∫ z : V, ((∫ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂μ) -
          (∫ y : V, Real.exp (-2 * t * ‖y - z‖ ^ 2) ∂ν)) ^ 2) := by
  let f : V → ℝ := fun z => ∫ x : V, Real.exp (-2 * t * ‖x - z‖ ^ 2) ∂μ
  let g : V → ℝ := fun z => ∫ y : V, Real.exp (-2 * t * ‖y - z‖ ^ 2) ∂ν
  have hff : Integrable (fun z => f z * f z) :=
    integrable_gaussian_smoothing_product t ht μ μ
  have hfg : Integrable (fun z => f z * g z) :=
    integrable_gaussian_smoothing_product t ht μ ν
  have hgg : Integrable (fun z => g z * g z) :=
    integrable_gaussian_smoothing_product t ht ν ν
  have hsquare : (∫ z : V, (f z - g z) ^ 2) =
      (∫ z : V, f z * f z) - 2 * (∫ z : V, f z * g z) + (∫ z : V, g z * g z) := by
    have hpoint : (fun z : V => (f z - g z) ^ 2) =
        (fun z : V => f z * f z - 2 * (f z * g z) + g z * g z) := by
      ext z
      ring
    rw [hpoint, integral_add (f := fun z => f z * f z - 2 * (f z * g z))
      (hff.sub (hfg.const_mul 2)) hgg,
      integral_sub hff (hfg.const_mul 2), integral_const_mul]
  rw [gaussian_bilinear_factorization t ht μ μ,
    gaussian_bilinear_factorization t ht μ ν, gaussian_bilinear_factorization t ht ν ν]
  change _ = (4 * t / Real.pi) ^ ((Module.finrank ℝ V : ℝ) / 2) *
    (∫ z : V, (f z - g z) ^ 2)
  rw [hsquare]
  ring

/-- Gaussian quadratic positivity for the difference of two finite measures. -/
theorem gaussian_quadratic_nonneg (t : ℝ) (ht : 0 < t)
    (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ (∫ p : V × V, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂μ.prod μ) -
      2 * (∫ p : V × V, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂μ.prod ν) +
      (∫ p : V × V, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂ν.prod ν) := by
  rw [gaussian_quadratic_eq_integral_square t ht μ ν]
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (integral_nonneg (fun z => sq_nonneg _))

/-- A kernel quadratic form on a finite signed measure, expanded using its Jordan parts.
The four terms are the usual integral against `η ⊗ η`. -/
def signedKernelQuadratic {α : Type*} [MeasurableSpace α]
    (k : α → α → ℝ) (η : SignedMeasure α) : ℝ :=
  (∫ p : α × α, k p.1 p.2 ∂η.toJordanDecomposition.posPart.prod η.toJordanDecomposition.posPart) -
    (∫ p : α × α, k p.1 p.2 ∂η.toJordanDecomposition.posPart.prod η.toJordanDecomposition.negPart) -
    (∫ p : α × α, k p.1 p.2 ∂η.toJordanDecomposition.negPart.prod η.toJordanDecomposition.posPart) +
    (∫ p : α × α, k p.1 p.2 ∂η.toJordanDecomposition.negPart.prod η.toJordanDecomposition.negPart)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- Symmetry of the Gaussian bilinear form under exchanging its two measures. -/
theorem gaussian_bilinear_symm (t : ℝ) (μ ν : Measure V)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ p : V × V, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂μ.prod ν) =
      (∫ p : V × V, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂ν.prod μ) := by
  simpa only [Prod.swap, norm_sub_rev] using
    (integral_prod_swap (μ := μ) (ν := ν)
      (fun p : V × V => Real.exp (-t * ‖p.1 - p.2‖ ^ 2))).symm

/-- Gaussian quadratic positivity for every finite signed measure.
Compact support is not needed for this Gaussian part of Lemma `gamma`. -/
theorem gaussian_signed_quadratic_nonneg (t : ℝ) (ht : 0 < t) (η : SignedMeasure V) :
    0 ≤ signedKernelQuadratic (fun x y : V => Real.exp (-t * ‖x - y‖ ^ 2)) η := by
  unfold signedKernelQuadratic
  dsimp only
  rw [gaussian_bilinear_symm t η.toJordanDecomposition.negPart η.toJordanDecomposition.posPart]
  convert! gaussian_quadratic_nonneg t ht η.toJordanDecomposition.posPart
    η.toJordanDecomposition.negPart using 1
  ring

end Riesz.Analysis
