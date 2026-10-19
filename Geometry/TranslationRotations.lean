import Riesz.Geometry.NormalCoordinates

/-!
# Small orthogonal motions in normal coordinates

Two Householder reflections give translations in the flat limit. The centered
chart and rescaled inverse extend continuously through inverse radius zero.
-/

noncomputable section

open Filter Set RieszShowcase
open scoped Topology

namespace Riesz.Geometry

theorem normalCenteredVector_joint_continuous (d : ℕ) :
    Continuous (fun p : ℝ × Rd d => normalCenteredVector d p.1 p.2) := by
  have hds : Continuous (dslope Real.cos 0) :=
    continuousOn_univ.mp ((continuousOn_dslope (f := Real.cos) (a := 0)
      (s := Set.univ) Filter.univ_mem).mpr
        ⟨Real.differentiable_cos.continuous.continuousOn, Real.differentiable_cos 0⟩)
  fun_prop [normalCenteredVector, euclideanCons]

/-- The inverse normal coordinates after removing the inverse-radius singularity. -/
def normalRescaledInverse (d : ℕ) (t : ℝ) (C : Rd (d + 1)) : Rd d :=
  (Real.sinc (Real.arccos (max (1 + t * C 0) 0)))⁻¹ • euclideanTail d C

theorem normalRescaledInverse_joint_continuous (d : ℕ) :
    Continuous (fun p : ℝ × Rd (d + 1) => normalRescaledInverse d p.1 p.2) := by
  have hden : Continuous (fun p : ℝ × Rd (d + 1) =>
      Real.sinc (Real.arccos (max (1 + p.1 * p.2 0) 0))) := by fun_prop
  exact (hden.inv₀ (fun p => (sinc_arccos_max_pos (1 + p.1 * p.2 0)).ne')).smul
    ((euclideanTail_continuous d).comp continuous_snd)

theorem normalRescaledInverse_zero (d : ℕ) (C : Rd (d + 1)) :
    normalRescaledInverse d 0 C = euclideanTail d C := by
  simp [normalRescaledInverse]

theorem normalInverse_centered (d : ℕ) {t : ℝ} (ht : t ≠ 0) (C : Rd (d + 1)) :
    normalInverse d t⁻¹ (normalNorth d + t • C) = normalRescaledInverse d t C := by
  ext i
  simp [normalInverse, normalRescaledInverse, normalNorth, euclideanCons,
    euclideanTail, div_eq_mul_inv, mul_assoc, mul_left_comm, ht]

theorem normalNorth_norm (d : ℕ) : ‖normalNorth d‖ = 1 := by
  simpa only [normalPoint_zero] using (normalPoint d 0 0).property

theorem normalNorth_ne_zero (d : ℕ) : normalNorth d ≠ 0 := by
  exact norm_pos_iff.mp ((normalNorth_norm d).symm ▸ zero_lt_one)

def normalTranslationAxis (d : ℕ) (a : Rd d) (t : ℝ) : Rd (d + 1) :=
  normalNorth d + normalUnitVector d t a

/-- The right reflection acts first. The fallback is irrelevant near `t = 0`. -/
def normalTranslationOrthogonal (d : ℕ) (a : Rd d) (t : ℝ) : Problem1.Orthogonal d :=
  if h : normalTranslationAxis d a t ≠ 0 then
    Problem1.householderOrthogonal (normalTranslationAxis d a t) h *
      Problem1.householderOrthogonal (normalNorth d) (normalNorth_ne_zero d)
  else 1

theorem householder_apply_self {m : ℕ} (v : Problem1.EuclideanN m) (hv : v ≠ 0) :
    Problem1.householder v hv v = -v := by
  rw [Problem1.householder_apply]
  simp only [mul_div_cancel_right₀ _ (Problem1.householder_denominator_pos v hv).2.ne',
    two_smul, sub_add_eq_sub_sub, sub_self, zero_sub]

theorem householder_apply_bisector {m : ℕ} (p q : Problem1.EuclideanN m)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hm : p + q ≠ 0) :
    Problem1.householder (p + q) hm p = -q := by
  have hinner : 2 * inner ℝ p (p + q) = inner ℝ (p + q) (p + q) := by
    simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq,
      hp, hq, one_pow, real_inner_comm q p]
    ring
  rw [Problem1.householder_apply, hinner,
    div_self (Problem1.householder_denominator_pos (p + q) hm).2.ne', one_smul]
  abel

theorem normalUnitVector_zero (d : ℕ) (x : Rd d) :
    normalUnitVector d 0 x = normalNorth d := by
  simp [normalUnitVector_eq_centered]

theorem orthogonalLin_mul_apply {m : ℕ} (U V : Problem1.OrthogonalN m)
    (z : Problem1.EuclideanN m) :
    Problem1.orthogonalLin (U * V) z =
      Problem1.orthogonalLin U (Problem1.orthogonalLin V z) := by
  simp only [Problem1.orthogonalLin, Problem1.orthogonalN_coe_mul,
    Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem normalTranslationAxis_zero_ne (d : ℕ) (a : Rd d) :
    normalTranslationAxis d a 0 ≠ 0 := by
  simpa only [normalTranslationAxis, normalUnitVector_zero, ← two_smul ℝ] using
    smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (normalNorth_ne_zero d)

theorem normalTranslationOrthogonal_north (d : ℕ) (a : Rd d) {t : ℝ}
    (ht : normalTranslationAxis d a t ≠ 0) :
    Problem1.orthogonalLin (normalTranslationOrthogonal d a t) (normalNorth d) =
      normalUnitVector d t a := by
  rw [normalTranslationOrthogonal, dif_pos ht, orthogonalLin_mul_apply,
    Problem1.householderOrthogonal_lin, Problem1.householderOrthogonal_lin,
    householder_apply_self, map_neg]
  exact (congrArg Neg.neg (householder_apply_bisector (normalNorth d)
    (normalUnitVector d t a) (normalNorth_norm d) (normalUnitVector_norm d t a) ht)).trans
      (neg_neg _)

theorem householderOrthogonal_inv {m : ℕ} (v : Problem1.EuclideanN m) (hv : v ≠ 0) :
    (Problem1.householderOrthogonal v hv)⁻¹ = Problem1.householderOrthogonal v hv := by
  apply Subtype.ext
  rw [Problem1.orthogonalN_coe_inv]
  ext i j
  simp [Problem1.householderOrthogonal, Problem1.householderMatrix,
    Matrix.transpose_apply, eq_comm, mul_left_comm, mul_comm, mul_assoc]

theorem householderOrthogonal_add_self {m : ℕ} (v : Problem1.EuclideanN m)
    (hv : v ≠ 0) (hvv : v + v ≠ 0) :
    Problem1.householderOrthogonal (v + v) hvv = Problem1.householderOrthogonal v hv := by
  apply Subtype.ext
  ext i j
  simp only [Problem1.householderOrthogonal, Problem1.householderMatrix,
    PiLp.add_apply, inner_add_left, inner_add_right]
  ring_nf

theorem normalTranslationOrthogonal_zero (d : ℕ) (a : Rd d) :
    normalTranslationOrthogonal d a 0 = 1 := by
  rw [normalTranslationOrthogonal, dif_pos (normalTranslationAxis_zero_ne d a)]
  simp only [normalTranslationAxis, normalUnitVector_zero,
    householderOrthogonal_add_self _ (normalNorth_ne_zero d)]
  exact (congrArg (fun U => U * Problem1.householderOrthogonal (normalNorth d)
    (normalNorth_ne_zero d)) (householderOrthogonal_inv (normalNorth d)
      (normalNorth_ne_zero d))).symm.trans (inv_mul_cancel _)

theorem householderOrthogonal_continuous (m : ℕ) :
    Continuous (fun v : {v : Problem1.EuclideanN m // v ≠ 0} =>
      Problem1.householderOrthogonal v.val v.property) := by
  apply Continuous.subtype_mk
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  have hi := (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).comp
    (continuous_subtype_val : Continuous (Subtype.val : {v : Problem1.EuclideanN m // v ≠ 0} → _))
  have hj := (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) j).comp
    (continuous_subtype_val : Continuous (Subtype.val : {v : Problem1.EuclideanN m // v ≠ 0} → _))
  exact continuous_const.sub (((continuous_const.mul hi).mul hj).div
    (continuous_subtype_val.inner continuous_subtype_val)
    (fun v => (Problem1.householder_denominator_pos v.val v.property).2.ne'))

theorem normalTranslationAxis_continuous (d : ℕ) (a : Rd d) :
    Continuous (normalTranslationAxis d a) := by
  fun_prop [normalTranslationAxis, normalUnitVector, euclideanCons]

theorem normalTranslationOrthogonal_continuousOn (d : ℕ) (a : Rd d) :
    ContinuousOn (normalTranslationOrthogonal d a)
      {t | normalTranslationAxis d a t ≠ 0} := by
  let g : {t : ℝ // normalTranslationAxis d a t ≠ 0} →
      {v : Problem1.EuclideanN (d + 1) // v ≠ 0} :=
    fun t => ⟨normalTranslationAxis d a t.val, t.property⟩
  have hg : Continuous g := ((normalTranslationAxis_continuous d a).comp
    continuous_subtype_val).subtype_mk _
  have hh := ((householderOrthogonal_continuous (d + 1)).comp hg).mul
    (continuous_const (y := Problem1.householderOrthogonal (normalNorth d)
      (normalNorth_ne_zero d)))
  refine continuousOn_iff_continuous_restrict.mpr (hh.congr (fun t => ?_))
  simp [normalTranslationOrthogonal, t.property, g]

theorem normalTranslationAxis_ne_mem_nhds (d : ℕ) (a : Rd d) :
    {t | normalTranslationAxis d a t ≠ 0} ∈ 𝓝 (0 : ℝ) := by
  exact (isOpen_ne.preimage (normalTranslationAxis_continuous d a)).mem_nhds
    (normalTranslationAxis_zero_ne d a)

theorem orthogonalLin_joint_continuous (m : ℕ) :
    Continuous (fun p : Problem1.OrthogonalN m × Problem1.EuclideanN m =>
      Problem1.orthogonalLin p.1 p.2) := by
  have hR : Continuous (fun p : Problem1.OrthogonalN m × Problem1.EuclideanN m =>
      (p.1 : Matrix (Fin m) (Fin m) ℝ)) := continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : Problem1.OrthogonalN m × Problem1.EuclideanN m =>
      WithLp.ofLp p.2) := (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ)).comp continuous_snd
  simpa only [Problem1.orthogonalLin, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Function.comp_def] using
    (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp (hR.matrix_mulVec hx)

theorem orthogonalLin_one_apply {m : ℕ} (z : Problem1.EuclideanN m) :
    Problem1.orthogonalLin (1 : Problem1.OrthogonalN m) z = z := by
  simp [Problem1.orthogonalLin, Matrix.toEuclideanLin]

def normalTranslationCentered (d : ℕ) (a : Rd d) (t : ℝ) (z : Rd d) : Rd (d + 1) :=
  normalCenteredVector d t a +
    Problem1.orthogonalLin (normalTranslationOrthogonal d a t) (normalCenteredVector d t z)

def normalTranslationCenteredInverse (d : ℕ) (a : Rd d) (t : ℝ) (z : Rd d) : Rd (d + 1) :=
  Problem1.orthogonalLin (normalTranslationOrthogonal d a t)⁻¹
    (normalCenteredVector d t z - normalCenteredVector d t a)

def normalTranslationCoordinates (d : ℕ) (a : Rd d) (t : ℝ) (z : Rd d) : Rd d :=
  normalRescaledInverse d t (normalTranslationCentered d a t z)

def normalTranslationCoordinatesInverse (d : ℕ) (a : Rd d) (t : ℝ) (z : Rd d) : Rd d :=
  normalRescaledInverse d t (normalTranslationCenteredInverse d a t z)

theorem normalTranslationCoordinates_zero (d : ℕ) (a z : Rd d) :
    normalTranslationCoordinates d a 0 z = a + z := by
  ext i
  simp [normalTranslationCoordinates, normalTranslationCentered,
    normalRescaledInverse_zero, normalTranslationOrthogonal_zero,
    normalCenteredVector_zero, orthogonalLin_one_apply, euclideanTail, euclideanCons]

theorem normalTranslationCoordinatesInverse_zero (d : ℕ) (a z : Rd d) :
    normalTranslationCoordinatesInverse d a 0 z = z - a := by
  ext i
  simp [normalTranslationCoordinatesInverse, normalTranslationCenteredInverse,
    normalRescaledInverse_zero, normalTranslationOrthogonal_zero,
    normalCenteredVector_zero, orthogonalLin_one_apply, euclideanTail, euclideanCons]

theorem normalTranslationCentered_continuousOn (d : ℕ) (a : Rd d) :
    ContinuousOn (fun p : ℝ × Rd d => normalTranslationCentered d a p.1 p.2)
      ({t | normalTranslationAxis d a t ≠ 0} ×ˢ univ) := by
  have hA : ContinuousOn (fun p : ℝ × Rd d => normalTranslationOrthogonal d a p.1)
      ({t | normalTranslationAxis d a t ≠ 0} ×ˢ univ) :=
    (normalTranslationOrthogonal_continuousOn d a).comp continuousOn_fst
      (fun _ hp => hp.1)
  have hamap : Continuous (fun p : ℝ × Rd d => (p.1, a)) :=
    continuous_fst.prodMk continuous_const
  have ha := (normalCenteredVector_joint_continuous d).comp hamap
  have hAz := (orthogonalLin_joint_continuous (d + 1)).comp_continuousOn
    (hA.prodMk (normalCenteredVector_joint_continuous d).continuousOn)
  exact ha.continuousOn.add hAz

theorem normalTranslationCenteredInverse_continuousOn (d : ℕ) (a : Rd d) :
    ContinuousOn (fun p : ℝ × Rd d => normalTranslationCenteredInverse d a p.1 p.2)
      ({t | normalTranslationAxis d a t ≠ 0} ×ˢ univ) := by
  have hA : ContinuousOn (fun p : ℝ × Rd d => normalTranslationOrthogonal d a p.1)
      ({t | normalTranslationAxis d a t ≠ 0} ×ˢ univ) :=
    (normalTranslationOrthogonal_continuousOn d a).comp continuousOn_fst
      (fun _ hp => hp.1)
  have hamap : Continuous (fun p : ℝ × Rd d => (p.1, a)) :=
    continuous_fst.prodMk continuous_const
  have ha := (normalCenteredVector_joint_continuous d).comp hamap
  have hdelta : Continuous (fun p : ℝ × Rd d =>
      normalCenteredVector d p.1 p.2 - normalCenteredVector d p.1 a) :=
    (normalCenteredVector_joint_continuous d).sub ha
  have hAi : ContinuousOn (fun p : ℝ × Rd d => (normalTranslationOrthogonal d a p.1)⁻¹)
      ({t | normalTranslationAxis d a t ≠ 0} ×ˢ univ) := hA.inv
  have hcomp := (orthogonalLin_joint_continuous (d + 1)).comp_continuousOn
    (hAi.prodMk hdelta.continuousOn)
  simpa only [normalTranslationCenteredInverse, Function.comp_def] using hcomp

theorem normalTranslationCoordinates_continuousOn (d : ℕ) (a : Rd d) :
    ContinuousOn (fun p : ℝ × Rd d => normalTranslationCoordinates d a p.1 p.2)
      ({t | normalTranslationAxis d a t ≠ 0} ×ˢ univ) := by
  have hcomp := (normalRescaledInverse_joint_continuous d).comp_continuousOn
    (continuousOn_fst.prodMk (normalTranslationCentered_continuousOn d a))
  simpa only [normalTranslationCoordinates, Function.comp_def] using hcomp

theorem normalTranslationCoordinatesInverse_continuousOn (d : ℕ) (a : Rd d) :
    ContinuousOn (fun p : ℝ × Rd d => normalTranslationCoordinatesInverse d a p.1 p.2)
      ({t | normalTranslationAxis d a t ≠ 0} ×ˢ univ) := by
  have hcomp := (normalRescaledInverse_joint_continuous d).comp_continuousOn
    (continuousOn_fst.prodMk (normalTranslationCenteredInverse_continuousOn d a))
  simpa only [normalTranslationCoordinatesInverse, Function.comp_def] using hcomp

theorem tendstoUniformlyOn_of_continuousOn_prod {E : Type*} [UniformSpace E]
    {d : ℕ} {f : ℝ → Rd d → E} {U : Set ℝ} {K : Set (Rd d)}
    (hU : U ∈ 𝓝 (0 : ℝ)) (hK : IsCompact K)
    (hf : ContinuousOn (fun p : ℝ × Rd d => f p.1 p.2) (U ×ˢ univ)) :
    TendstoUniformlyOn f (f 0) (𝓝 0) K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hm : Continuous (fun p : ℝ × K => (p.1, p.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hc : ContinuousOn (fun p : ℝ × K => f p.1 p.2.val) (U ×ˢ univ) :=
    hf.comp hm.continuousOn (fun _ hp => ⟨hp.1, mem_univ _⟩)
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr (hc.tendstoUniformly hU)

theorem normalTranslationCoordinates_tendstoUniformlyOn (d : ℕ) (a : Rd d)
    {K : Set (Rd d)} (hK : IsCompact K) :
    TendstoUniformlyOn (normalTranslationCoordinates d a) (fun z => a + z) (𝓝 0) K := by
  have h0 : normalTranslationCoordinates d a 0 = (fun z => a + z) :=
    funext (normalTranslationCoordinates_zero d a)
  simpa only [h0] using
    tendstoUniformlyOn_of_continuousOn_prod (normalTranslationAxis_ne_mem_nhds d a) hK
      (normalTranslationCoordinates_continuousOn d a)

theorem normalTranslationCoordinatesInverse_tendstoUniformlyOn (d : ℕ) (a : Rd d)
    {K : Set (Rd d)} (hK : IsCompact K) :
    TendstoUniformlyOn (normalTranslationCoordinatesInverse d a) (fun z => z - a) (𝓝 0) K := by
  have h0 : normalTranslationCoordinatesInverse d a 0 = (fun z => z - a) :=
    funext (normalTranslationCoordinatesInverse_zero d a)
  simpa only [h0] using
    tendstoUniformlyOn_of_continuousOn_prod (normalTranslationAxis_ne_mem_nhds d a) hK
      (normalTranslationCoordinatesInverse_continuousOn d a)

theorem rotateSphere_val (d : ℕ) (U : Problem1.Orthogonal d) (y : Sphere d) :
    (rotateSphere d U y).val = Problem1.orthogonalLin U y.val := by
  rfl

theorem orthogonalLin_inv_left {m : ℕ} (U : Problem1.OrthogonalN m)
    (z : Problem1.EuclideanN m) :
    Problem1.orthogonalLin U⁻¹ (Problem1.orthogonalLin U z) = z := by
  rw [← orthogonalLin_mul_apply, inv_mul_cancel, orthogonalLin_one_apply]

theorem rotateSphere_inv_left (d : ℕ) (U : Problem1.Orthogonal d) (y : Sphere d) :
    rotateSphere d U⁻¹ (rotateSphere d U y) = y := by
  rw [← rotateSphere_mul, inv_mul_cancel, rotateSphere_one]

theorem normalTranslationOrthogonal_unitVector (d : ℕ) (a z : Rd d) {t : ℝ}
    (ht : normalTranslationAxis d a t ≠ 0) :
    Problem1.orthogonalLin (normalTranslationOrthogonal d a t) (normalUnitVector d t z) =
      normalNorth d + t • normalTranslationCentered d a t z := by
  rw [normalUnitVector_eq_centered d t z, map_add, map_smul,
    normalTranslationOrthogonal_north d a ht, normalUnitVector_eq_centered d t a,
    normalTranslationCentered, smul_add]
  exact add_assoc _ _ _

theorem normalTranslationOrthogonal_inv_unitVector (d : ℕ) (a z : Rd d) {t : ℝ}
    (ht : normalTranslationAxis d a t ≠ 0) :
    Problem1.orthogonalLin (normalTranslationOrthogonal d a t)⁻¹ (normalUnitVector d t z) =
      normalNorth d + t • normalTranslationCenteredInverse d a t z := by
  have hq : Problem1.orthogonalLin (normalTranslationOrthogonal d a t)⁻¹
      (normalUnitVector d t a) = normalNorth d :=
    (congrArg (Problem1.orthogonalLin (normalTranslationOrthogonal d a t)⁻¹)
      (normalTranslationOrthogonal_north d a ht)).symm.trans
        (orthogonalLin_inv_left _ _)
  have hdiff : normalUnitVector d t z - normalUnitVector d t a =
      t • (normalCenteredVector d t z - normalCenteredVector d t a) := by
    rw [normalUnitVector_eq_centered d t z, normalUnitVector_eq_centered d t a,
      add_sub_add_left_eq_sub, smul_sub]
  have hsplit : Problem1.orthogonalLin (normalTranslationOrthogonal d a t)⁻¹
      (normalUnitVector d t z) =
      Problem1.orthogonalLin (normalTranslationOrthogonal d a t)⁻¹
        (normalUnitVector d t z - normalUnitVector d t a) + normalNorth d := by
    rw [map_sub, hq, sub_add_cancel]
  rw [hsplit, hdiff, map_smul]
  exact add_comm _ _

theorem normalInverse_rotate_normalPoint (d : ℕ) (a z : Rd d) {t : ℝ}
    (ht : t ≠ 0) (haxis : normalTranslationAxis d a t ≠ 0) :
    normalInverse d t⁻¹
        (rotateSphere d (normalTranslationOrthogonal d a t) (normalPoint d t⁻¹ z)).val =
      normalTranslationCoordinates d a t z := by
  rw [rotateSphere_val]
  change normalInverse d t⁻¹ (Problem1.orthogonalLin (normalTranslationOrthogonal d a t)
    (normalUnitVector d (t⁻¹)⁻¹ z)) = _
  rw [inv_inv, normalTranslationOrthogonal_unitVector d a z haxis, normalInverse_centered d ht]
  rfl

theorem normalInverse_rotate_inv_normalPoint (d : ℕ) (a z : Rd d) {t : ℝ}
    (ht : t ≠ 0) (haxis : normalTranslationAxis d a t ≠ 0) :
    normalInverse d t⁻¹
        (rotateSphere d (normalTranslationOrthogonal d a t)⁻¹ (normalPoint d t⁻¹ z)).val =
      normalTranslationCoordinatesInverse d a t z := by
  rw [rotateSphere_val]
  change normalInverse d t⁻¹ (Problem1.orthogonalLin (normalTranslationOrthogonal d a t)⁻¹
    (normalUnitVector d (t⁻¹)⁻¹ z)) = _
  rw [inv_inv, normalTranslationOrthogonal_inv_unitVector d a z haxis, normalInverse_centered d ht]
  rfl

theorem eventually_normalCentered_head_pos {d : ℕ} {C : ℝ → Rd d → Rd (d + 1)}
    {U : Set ℝ} {K : Set (Rd d)} (hU : U ∈ 𝓝 (0 : ℝ)) (hK : IsCompact K)
    (hC : ContinuousOn (fun p : ℝ × Rd d => C p.1 p.2) (U ×ˢ univ)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ z ∈ K, 0 < (normalNorth d + t • C t z) 0 := by
  have hc : ContinuousOn (fun p : ℝ × Rd d => normalNorth d + p.1 • C p.1 p.2)
      (U ×ˢ univ) := continuousOn_const.add (continuousOn_fst.smul hC)
  have hh := (PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => ℝ) 0).comp_continuousOn hc
  have hu := tendstoUniformlyOn_of_continuousOn_prod
    (f := fun t z => (normalNorth d + t • C t z) 0) hU hK hh
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one] with t ht z hz
  have he : |1 - (normalNorth d + t • C t z) 0| < 1 := by
    simpa only [zero_smul, add_zero, normalNorth, euclideanCons, WithLp.ofLp_toLp,
      Fin.cons_zero, Real.dist_eq] using ht z hz
  linarith [(abs_lt.mp he).2]

theorem eventually_rotate_normalPoint_mem_northHemisphere (d : ℕ) (a : Rd d)
    {K : Set (Rd d)} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ z ∈ K,
      rotateSphere d (normalTranslationOrthogonal d a t) (normalPoint d t⁻¹ z) ∈
        northHemisphere d := by
  have hh := eventually_normalCentered_head_pos (normalTranslationAxis_ne_mem_nhds d a) hK
    (normalTranslationCentered_continuousOn d a)
  filter_upwards [normalTranslationAxis_ne_mem_nhds d a, hh] with t haxis ht z hz
  simpa only [northHemisphere, Set.mem_setOf_eq, rotateSphere_val, normalPoint,
    inv_inv, normalTranslationOrthogonal_unitVector d a z haxis] using ht z hz

theorem eventually_rotate_inv_normalPoint_mem_northHemisphere (d : ℕ) (a : Rd d)
    {K : Set (Rd d)} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ z ∈ K,
      rotateSphere d (normalTranslationOrthogonal d a t)⁻¹ (normalPoint d t⁻¹ z) ∈
        northHemisphere d := by
  have hh := eventually_normalCentered_head_pos (normalTranslationAxis_ne_mem_nhds d a) hK
    (normalTranslationCenteredInverse_continuousOn d a)
  filter_upwards [normalTranslationAxis_ne_mem_nhds d a, hh] with t haxis ht z hz
  simpa only [northHemisphere, Set.mem_setOf_eq, rotateSphere_val, normalPoint,
    inv_inv, normalTranslationOrthogonal_inv_unitVector d a z haxis] using ht z hz

theorem eventually_rotate_inv_cap_subset (d : ℕ) (a : Rd d) (T : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t → ∀ y : Sphere d,
      y ∈ northHemisphere d → ‖normalInverse d t⁻¹ y.val‖ ≤ T →
      rotateSphere d (normalTranslationOrthogonal d a t)⁻¹ y ∈ northHemisphere d ∧
        ‖normalInverse d t⁻¹
          (rotateSphere d (normalTranslationOrthogonal d a t)⁻¹ y).val‖ < T + ‖a‖ + 1 := by
  have hK : IsCompact (Metric.closedBall (0 : Rd d) T) := isCompact_closedBall _ _
  filter_upwards [normalTranslationAxis_ne_mem_nhds d a,
    eventually_rotate_inv_normalPoint_mem_northHemisphere d a hK,
    Metric.tendstoUniformlyOn_iff.mp
      (normalTranslationCoordinatesInverse_tendstoUniformlyOn d a hK) 1 zero_lt_one]
      with t haxis hhemi hdist ht y hy hn
  let z := normalInverse d t⁻¹ y.val
  have hz : z ∈ Metric.closedBall (0 : Rd d) T := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn
  have hpoint : normalPoint d t⁻¹ z = y := normalPoint_normalInverse d (inv_pos.mpr ht) hy
  refine ⟨hpoint ▸ hhemi z hz, ?_⟩
  rw [← hpoint, normalInverse_rotate_inv_normalPoint d a z ht.ne' haxis]
  have he : ‖normalTranslationCoordinatesInverse d a t z - (z - a)‖ < 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hdist z hz
  have hza : ‖z - a‖ ≤ T + ‖a‖ :=
    (norm_sub_le z a).trans (add_le_add hn le_rfl)
  linarith [norm_sub_norm_le (normalTranslationCoordinatesInverse d a t z) (z - a)]

theorem eventually_translation_cap_preimage_subset (d : ℕ) (a : Rd d) (T : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t → ∀ y : Sphere d,
      rotateSphere d (normalTranslationOrthogonal d a t) y ∈ northHemisphere d →
      ‖normalInverse d t⁻¹
        (rotateSphere d (normalTranslationOrthogonal d a t) y).val‖ ≤ T →
      y ∈ northHemisphere d ∧ ‖normalInverse d t⁻¹ y.val‖ < T + ‖a‖ + 1 := by
  filter_upwards [eventually_rotate_inv_cap_subset d a T] with t hcap ht y hy hn
  simpa only [rotateSphere_inv_left] using
    hcap ht (rotateSphere d (normalTranslationOrthogonal d a t) y) hy hn

theorem eventually_rotate_cap_subset (d : ℕ) (a : Rd d) (T : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t → ∀ y : Sphere d,
      y ∈ northHemisphere d → ‖normalInverse d t⁻¹ y.val‖ ≤ T →
      rotateSphere d (normalTranslationOrthogonal d a t) y ∈ northHemisphere d ∧
        ‖normalInverse d t⁻¹
          (rotateSphere d (normalTranslationOrthogonal d a t) y).val‖ < T + ‖a‖ + 1 := by
  have hK : IsCompact (Metric.closedBall (0 : Rd d) T) := isCompact_closedBall _ _
  filter_upwards [normalTranslationAxis_ne_mem_nhds d a,
    eventually_rotate_normalPoint_mem_northHemisphere d a hK,
    Metric.tendstoUniformlyOn_iff.mp
      (normalTranslationCoordinates_tendstoUniformlyOn d a hK) 1 zero_lt_one]
      with t haxis hhemi hdist ht y hy hn
  let z := normalInverse d t⁻¹ y.val
  have hz : z ∈ Metric.closedBall (0 : Rd d) T := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn
  have hpoint : normalPoint d t⁻¹ z = y := normalPoint_normalInverse d (inv_pos.mpr ht) hy
  refine ⟨hpoint ▸ hhemi z hz, ?_⟩
  rw [← hpoint, normalInverse_rotate_normalPoint d a z ht.ne' haxis]
  have he : ‖normalTranslationCoordinates d a t z - (a + z)‖ < 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hdist z hz
  have haz : ‖a + z‖ ≤ ‖a‖ + T :=
    (norm_add_le a z).trans (add_le_add le_rfl hn)
  linarith [norm_sub_norm_le (normalTranslationCoordinates d a t z) (a + z)]

end Riesz.Geometry
