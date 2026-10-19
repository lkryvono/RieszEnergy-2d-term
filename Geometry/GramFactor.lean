import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# A positive Gram factor sufficient for sphere patches

The patch construction uses the Gram identity, positive determinant and norm
identity. It does not use triangularity of the factor. The canonical positive
square root supplies precisely this sufficient interface; no upper-triangular
factorization is asserted here.
-/

noncomputable section

open Matrix
open scoped MatrixOrder

namespace Riesz.Geometry

/-- The canonical positive square root of a real Gram matrix. -/
def positiveGramFactor (d : ℕ) (S : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := CFC.sqrt S

theorem positiveGramFactor_transpose_mul_self (d : ℕ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) :
    (positiveGramFactor d S).transpose * positiveGramFactor d S = S := by
  simpa only [positiveGramFactor, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian.eq]
    using CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg

theorem positiveGramFactor_det (d : ℕ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) :
    (positiveGramFactor d S).det = Real.sqrt S.det := by
  simpa only [positiveGramFactor, RCLike.sqrt_real] using hS.posSemidef.det_sqrt

theorem positiveGramFactor_det_pos (d : ℕ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) :
    0 < (positiveGramFactor d S).det := by
  simpa only [positiveGramFactor, hS.posSemidef.det_sqrt, RCLike.sqrt_real]
    using Real.sqrt_pos_of_pos hS.det_pos

/-- The squared Euclidean norm depends only on the Gram matrix. -/
theorem matrix_euclidean_norm_sq (d m : ℕ) (A : Matrix (Fin m) (Fin d) ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    ‖A.toEuclideanLin v‖ ^ 2 =
      WithLp.ofLp v ⬝ᵥ ((A.transpose * A) *ᵥ WithLp.ofLp v) := by
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    EuclideanSpace.inner_toLp_toLp, star_trivial, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec]
    using (real_inner_self_eq_norm_sq (A.toEuclideanLin v)).symm

/-- Two rectangular matrices with the same Gram matrix have the same norm on
every Euclidean vector. -/
theorem matrix_euclidean_norm_eq_of_gram_eq (d m n : ℕ)
    (A : Matrix (Fin m) (Fin d) ℝ) (L : Matrix (Fin n) (Fin d) ℝ)
    (hGram : A.transpose * A = L.transpose * L)
    (v : EuclideanSpace ℝ (Fin d)) : ‖A.toEuclideanLin v‖ = ‖L.toEuclideanLin v‖ := by
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    ((matrix_euclidean_norm_sq d m A v).trans
      ((congrArg (fun S : Matrix (Fin d) (Fin d) ℝ =>
        WithLp.ofLp v ⬝ᵥ (S *ᵥ WithLp.ofLp v)) hGram).trans
        (matrix_euclidean_norm_sq d n L v).symm))

/-- An injective rectangular Euclidean map has a positive definite Gram matrix. -/
theorem rectangular_gram_posDef (d m : ℕ) (L : Matrix (Fin m) (Fin d) ℝ)
    (hL : Function.Injective L.toEuclideanLin) : (L.transpose * L).PosDef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self L
      (fun v w h => WithLp.toLp_injective 2 (hL (congrArg (WithLp.toLp 2) h)))

/-- The Gram matrix of a map between the standard Euclidean spaces. -/
def euclideanGramMatrix (d m : ℕ)
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.toEuclideanLin.symm L).transpose * Matrix.toEuclideanLin.symm L

/-- The positive Gram factor of a Euclidean linear map. -/
def euclideanGramFactor (d m : ℕ)
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin d) (Fin d) ℝ := positiveGramFactor d (euclideanGramMatrix d m L)

theorem euclideanGramMatrix_posDef (d m : ℕ)
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) : (euclideanGramMatrix d m L).PosDef := by
  apply rectangular_gram_posDef
  simpa only [LinearEquiv.apply_symm_apply] using hL

theorem euclideanGramFactor_transpose_mul_self (d m : ℕ)
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) :
    (euclideanGramFactor d m L).transpose * euclideanGramFactor d m L =
      euclideanGramMatrix d m L := by
  exact positiveGramFactor_transpose_mul_self d _ (euclideanGramMatrix_posDef d m L hL)

theorem euclideanGramFactor_det (d m : ℕ)
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) :
    (euclideanGramFactor d m L).det = Real.sqrt (euclideanGramMatrix d m L).det := by
  exact positiveGramFactor_det d _ (euclideanGramMatrix_posDef d m L hL)

theorem euclideanGramFactor_det_pos (d m : ℕ)
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) : 0 < (euclideanGramFactor d m L).det := by
  exact positiveGramFactor_det_pos d _ (euclideanGramMatrix_posDef d m L hL)

/-- The factor preserves precisely the norm of the original rectangular map. -/
theorem euclideanGramFactor_norm (d m : ℕ)
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) (v : EuclideanSpace ℝ (Fin d)) :
    ‖(euclideanGramFactor d m L).toEuclideanLin v‖ = ‖L v‖ := by
  simpa only [LinearEquiv.apply_symm_apply] using
    matrix_euclidean_norm_eq_of_gram_eq d d m (euclideanGramFactor d m L)
      (Matrix.toEuclideanLin.symm L) (euclideanGramFactor_transpose_mul_self d m L hL) v

theorem euclideanGramFactor_mul_inverse_apply (d m : ℕ)
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) (v : EuclideanSpace ℝ (Fin d)) :
    (euclideanGramFactor d m L).toEuclideanLin
      ((euclideanGramFactor d m L)⁻¹.toEuclideanLin v) = v := by
  simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    Matrix.toLpLin_one, LinearMap.id_apply] using
    congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => Matrix.toLpLin 2 2 A v)
      (Matrix.mul_nonsing_inv (euclideanGramFactor d m L)
        (isUnit_iff_ne_zero.mpr (euclideanGramFactor_det_pos d m L hL).ne'))

/-- A lower Euclidean norm bound on the original map bounds the inverse factor. -/
theorem euclideanGramFactor_inverse_norm_le (d m : ℕ)
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) (c : ℝ) (hc : 0 < c)
    (hLower : ∀ v, c * ‖v‖ ≤ ‖L v‖) (v : EuclideanSpace ℝ (Fin d)) :
    ‖(euclideanGramFactor d m L)⁻¹.toEuclideanLin v‖ ≤ ‖v‖ / c := by
  apply (le_div_iff₀ hc).mpr
  simpa only [← euclideanGramFactor_norm d m L hL,
    euclideanGramFactor_mul_inverse_apply d m L hL, mul_comm] using
    hLower ((euclideanGramFactor d m L)⁻¹.toEuclideanLin v)

/-- The inverse bound uses the Euclidean operator norm, rather than an
entrywise matrix norm. -/
theorem euclideanGramFactor_inverse_opNorm_le (d m : ℕ)
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) (c : ℝ) (hc : 0 < c)
    (hLower : ∀ v, c * ‖v‖ ≤ ‖L v‖) :
    ‖((euclideanGramFactor d m L)⁻¹.toEuclideanLin).toContinuousLinearMap‖ ≤ c⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le) ?_
  intro v
  simpa only [LinearMap.coe_toContinuousLinearMap', div_eq_mul_inv, mul_comm] using
    euclideanGramFactor_inverse_norm_le d m L hL c hc hLower v

end Riesz.Geometry
