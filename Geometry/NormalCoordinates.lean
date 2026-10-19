import Riesz.Geometry.RotationsFromProblem1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# North-hemisphere normal coordinates

The north coordinate is coordinate zero, as in the audited Problem 1 action.
The `sinc` and `dslope` formulas extend through the origin and through inverse
radius zero. Area identification is separate from this geometric construction.
-/

noncomputable section

open Filter Set RieszShowcase
open scoped Topology

namespace Riesz.Geometry

/-- Split ambient coordinates into the north coordinate and tangent coordinates. -/
def euclideanCons (d : ℕ) (a : ℝ) (x : Rd d) : Rd (d + 1) :=
  WithLp.toLp 2 (Fin.cons a (fun i => x i))

/-- The tangent coordinates of an ambient vector. -/
def euclideanTail (d : ℕ) (y : Rd (d + 1)) : Rd d :=
  WithLp.toLp 2 (fun i => y i.succ)

/-- The north vector, with the convention used by the existing orthogonal action. -/
def normalNorth (d : ℕ) : Rd (d + 1) := euclideanCons d 1 0

/-- The unit-radius exponential-chart vector, parametrized by inverse radius. -/
def normalUnitVector (d : ℕ) (t : ℝ) (x : Rd d) : Rd (d + 1) :=
  euclideanCons d (Real.cos (t * ‖x‖))
    ((t * Real.sinc (t * ‖x‖)) • x)

/-- The continuous centered chart, including the flat value at inverse radius zero. -/
def normalCenteredVector (d : ℕ) (t : ℝ) (x : Rd d) : Rd (d + 1) :=
  euclideanCons d (‖x‖ * dslope Real.cos 0 (t * ‖x‖))
    (Real.sinc (t * ‖x‖) • x)

/-- The normal chart on the sphere of radius `R`. -/
def normalChart (d : ℕ) (R : ℝ) (x : Rd d) : Rd (d + 1) :=
  R • normalUnitVector d R⁻¹ x

/-- The parameter domain of the northern open hemisphere. -/
def normalDomain (d : ℕ) (R : ℝ) : Set (Rd d) :=
  {x | ‖x‖ < Real.pi * R / 2}

/-- The northern open hemisphere in the exact Showcase sphere. -/
def northHemisphere (d : ℕ) : Set (Sphere d) :=
  {y | 0 < y.val 0}

/-- A total inverse extension, agreeing with normal coordinates on the north hemisphere. -/
def normalInverse (d : ℕ) (R : ℝ) (y : Rd (d + 1)) : Rd d :=
  (R / Real.sinc (Real.arccos (max (y 0) 0))) • euclideanTail d y

theorem euclideanCons_norm_sq (d : ℕ) (a : ℝ) (x : Rd d) :
    ‖euclideanCons d a x‖ ^ 2 = a ^ 2 + ‖x‖ ^ 2 := by
  simp [euclideanCons, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

theorem mul_sinc (u : ℝ) : u * Real.sinc u = Real.sin u := by
  simpa only [Real.sinc_eq_dslope, sub_zero, smul_eq_mul, Real.sin_zero] using
    (sub_smul_dslope Real.sin 0 u)

theorem normalUnitVector_norm_sq (d : ℕ) (t : ℝ) (x : Rd d) :
    ‖normalUnitVector d t x‖ ^ 2 = 1 := by
  rw [normalUnitVector, euclideanCons_norm_sq, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq (t * ‖x‖),
    congrArg (fun z : ℝ => z ^ 2) (mul_sinc (t * ‖x‖))]

theorem normalUnitVector_norm (d : ℕ) (t : ℝ) (x : Rd d) :
    ‖normalUnitVector d t x‖ = 1 := by
  nlinarith [normalUnitVector_norm_sq d t x, norm_nonneg (normalUnitVector d t x)]

/-- The normal chart as a point of the exact Showcase sphere. -/
def normalPoint (d : ℕ) (R : ℝ) (x : Rd d) : Sphere d :=
  ⟨normalUnitVector d R⁻¹ x, normalUnitVector_norm d R⁻¹ x⟩

theorem normalCenteredVector_zero (d : ℕ) (x : Rd d) :
    normalCenteredVector d 0 x = euclideanCons d 0 x := by
  simp [normalCenteredVector, dslope_same, Real.deriv_cos]

theorem normalUnitVector_eq_centered (d : ℕ) (t : ℝ) (x : Rd d) :
    normalUnitVector d t x = normalNorth d + t • normalCenteredVector d t x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [normalUnitVector, normalNorth, normalCenteredVector, euclideanCons]
    simpa only [sub_zero, smul_eq_mul, Real.cos_zero, mul_assoc] using
      (sub_eq_iff_eq_add').1 (sub_smul_dslope Real.cos 0 (t * ‖x‖)).symm
  · simp [normalUnitVector, normalNorth, normalCenteredVector, euclideanCons, mul_assoc]

theorem euclideanCons_head_tail (d : ℕ) (y : Rd (d + 1)) :
    euclideanCons d (y 0) (euclideanTail d y) = y := by
  ext i
  exact congrFun (Fin.cons_self_tail (fun j => y j)) i

theorem sinc_pos_of_nonneg_of_le_pi_div_two {u : ℝ}
    (hu : 0 ≤ u) (hu' : u ≤ Real.pi / 2) : 0 < Real.sinc u := by
  by_cases h : u = 0
  · simp [h]
  rw [Real.sinc_of_ne_zero h]
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne hu (Ne.symm h))
    (lt_of_le_of_lt hu' (by linarith [Real.pi_pos])))
    (lt_of_le_of_ne hu (Ne.symm h))

theorem sinc_arccos_max_pos (u : ℝ) :
    0 < Real.sinc (Real.arccos (max u 0)) := by
  exact sinc_pos_of_nonneg_of_le_pi_div_two (Real.arccos_nonneg _)
    (Real.arccos_le_pi_div_two.mpr (le_max_right _ _))

theorem euclideanTail_continuous (d : ℕ) : Continuous (euclideanTail d) := by
  fun_prop [euclideanTail]

theorem normalInverse_continuous (d : ℕ) (R : ℝ) : Continuous (normalInverse d R) := by
  exact (continuous_const.div (Real.continuous_sinc.comp
    (Real.continuous_arccos.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => ℝ) 0).max continuous_const)))
    (fun y => ne_of_gt (sinc_arccos_max_pos (y 0)))).smul
    (euclideanTail_continuous d)

theorem northHemisphere_isOpen (d : ℕ) : IsOpen (northHemisphere d) := by
  exact isOpen_lt continuous_const
    ((PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => ℝ) 0).comp continuous_subtype_val)

theorem normalDomain_angle (d : ℕ) {R : ℝ} (hR : 0 < R) {x : Rd d}
    (hx : x ∈ normalDomain d R) :
    R⁻¹ * ‖x‖ ∈ Ico 0 (Real.pi / 2) := by
  constructor
  · positivity
  · simpa only [inv_mul_eq_div, div_lt_iff₀ hR, div_mul_eq_mul_div, mul_comm R] using
      (show ‖x‖ < Real.pi * R / 2 from hx)

theorem normalPoint_mem_northHemisphere (d : ℕ) {R : ℝ} (hR : 0 < R)
    {x : Rd d} (hx : x ∈ normalDomain d R) :
    normalPoint d R x ∈ northHemisphere d := by
  exact Real.cos_pos_of_mem_Ioo
    ⟨lt_of_lt_of_le (by linarith [Real.pi_pos]) (normalDomain_angle d hR hx).1,
      (normalDomain_angle d hR hx).2⟩

theorem sphere_head_bounds (d : ℕ) (y : Sphere d) : -1 ≤ y.val 0 ∧ y.val 0 ≤ 1 := by
  have h := PiLp.norm_apply_le y.val 0
  simpa only [Real.norm_eq_abs, y.property, abs_le] using h

theorem sphere_tail_norm (d : ℕ) (y : Sphere d) :
    ‖euclideanTail d y.val‖ = Real.sin (Real.arccos (y.val 0)) := by
  have hnorm := euclideanCons_norm_sq d (y.val 0) (euclideanTail d y.val)
  rw [euclideanCons_head_tail, y.property] at hnorm
  have htrig := Real.sin_sq_add_cos_sq (Real.arccos (y.val 0))
  rw [Real.cos_arccos (sphere_head_bounds d y).1 (sphere_head_bounds d y).2] at htrig
  nlinarith [norm_nonneg (euclideanTail d y.val),
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg (y.val 0))
      (Real.arccos_le_pi (y.val 0))]

theorem normalInverse_norm (d : ℕ) {R : ℝ} (hR : 0 < R)
    {y : Sphere d} (hy : y ∈ northHemisphere d) :
    ‖normalInverse d R y.val‖ = R * Real.arccos (y.val 0) := by
  have hhead : 0 < y.val 0 := hy
  have hsinc : 0 < Real.sinc (Real.arccos (y.val 0)) := by
    simpa only [max_eq_left hhead.le] using (sinc_arccos_max_pos (y.val 0))
  rw [normalInverse, norm_smul, Real.norm_eq_abs, max_eq_left hhead.le,
    abs_of_pos (div_pos hR hsinc), sphere_tail_norm, ← mul_sinc]
  field_simp

theorem normalInverse_mem_normalDomain (d : ℕ) {R : ℝ} (hR : 0 < R)
    {y : Sphere d} (hy : y ∈ northHemisphere d) :
    normalInverse d R y.val ∈ normalDomain d R := by
  change ‖normalInverse d R y.val‖ < Real.pi * R / 2
  rw [normalInverse_norm d hR hy]
  nlinarith [mul_lt_mul_of_pos_left (Real.arccos_lt_pi_div_two.mpr
    (show 0 < y.val 0 from hy)) hR]

theorem normalInverse_normalPoint (d : ℕ) {R : ℝ} (hR : 0 < R)
    {x : Rd d} (hx : x ∈ normalDomain d R) :
    normalInverse d R (normalPoint d R x).val = x := by
  have hangle := normalDomain_angle d hR hx
  have hcos : 0 < Real.cos (R⁻¹ * ‖x‖) := normalPoint_mem_northHemisphere d hR hx
  have hsinc := sinc_pos_of_nonneg_of_le_pi_div_two hangle.1 hangle.2.le
  have hacos := Real.arccos_cos hangle.1
    (by linarith [Real.pi_pos, hangle.2] : R⁻¹ * ‖x‖ ≤ Real.pi)
  change (R / Real.sinc (Real.arccos (max (Real.cos (R⁻¹ * ‖x‖)) 0))) •
    euclideanTail d (normalUnitVector d R⁻¹ x) = x
  rw [max_eq_left hcos.le, hacos]
  change (R / Real.sinc (R⁻¹ * ‖x‖)) • ((R⁻¹ * Real.sinc (R⁻¹ * ‖x‖)) • x) = x
  simp [smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, hsinc.ne', hR.ne']

theorem normalPoint_normalInverse (d : ℕ) {R : ℝ} (hR : 0 < R)
    {y : Sphere d} (hy : y ∈ northHemisphere d) :
    normalPoint d R (normalInverse d R y.val) = y := by
  apply Subtype.val_injective
  have hangle : R⁻¹ * ‖normalInverse d R y.val‖ = Real.arccos (y.val 0) := by
    rw [normalInverse_norm d hR hy, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  change normalUnitVector d R⁻¹ (normalInverse d R y.val) = y.val
  rw [normalUnitVector, hangle,
    Real.cos_arccos (sphere_head_bounds d y).1 (sphere_head_bounds d y).2]
  have hhead : 0 < y.val 0 := hy
  have hsinc : Real.sinc (Real.arccos (y.val 0)) ≠ 0 := by
    simpa only [max_eq_left hhead.le] using (sinc_arccos_max_pos (y.val 0)).ne'
  simpa [normalInverse, max_eq_left hhead.le, smul_smul, div_eq_mul_inv,
    mul_comm, mul_left_comm, hsinc, hR.ne'] using (euclideanCons_head_tail d y.val)

theorem normalPoint_zero (d : ℕ) (R : ℝ) :
    (normalPoint d R 0).val = normalNorth d := by
  simp [normalPoint, normalUnitVector, normalNorth]

theorem normalPoint_zero_chord_sq (d : ℕ) (R : ℝ) (y : Sphere d) :
    chord d (normalPoint d R 0) y ^ 2 = 2 - 2 * y.val 0 := by
  rw [chord, norm_sub_sq_real, (normalPoint d R 0).property, y.property]
  simp [normalPoint_zero, normalNorth, euclideanCons, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_succ]
  ring

theorem normalPoint_zero_cap_iff_angle (d : ℕ) (R : ℝ) (y : Sphere d)
    {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ Real.pi) :
    chord d (normalPoint d R 0) y ≤ 2 * Real.sin (u / 2) ↔
      Real.arccos (y.val 0) ≤ u := by
  have hsin : 0 ≤ Real.sin (u / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  rw [← sq_le_sq₀ (show 0 ≤ chord d (normalPoint d R 0) y from norm_nonneg _)
    (show 0 ≤ 2 * Real.sin (u / 2) from mul_nonneg (by norm_num) hsin),
    normalPoint_zero_chord_sq]
  have hhalf : (2 * Real.sin (u / 2)) ^ 2 = 2 - 2 * Real.cos u := by
    nlinarith [Real.sin_sq_add_cos_sq (u / 2),
      (show Real.cos u = 2 * Real.cos (u / 2) ^ 2 - 1 by
        simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
          (Real.cos_two_mul (u / 2)))]
  have hcos := Real.strictAntiOn_cos.le_iff_ge
    (show u ∈ Icc 0 Real.pi from ⟨hu, hu'⟩)
    (show Real.arccos (y.val 0) ∈ Icc 0 Real.pi from
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
  rw [Real.cos_arccos (sphere_head_bounds d y).1 (sphere_head_bounds d y).2] at hcos
  rw [hhalf, ← hcos]; constructor <;> intro h <;> linarith

theorem normalInverse_closedBall_preimage (d : ℕ) {R T : ℝ} (hR : 0 < R)
    (hT : 0 ≤ T) (hTpi : T < Real.pi * R / 2) :
    {y : Sphere d | y ∈ northHemisphere d ∧
      normalInverse d R y.val ∈ Metric.closedBall 0 T} =
    {y : Sphere d | chord d (normalPoint d R 0) y ≤
      2 * Real.sin (T / (2 * R))} := by
  have hu : T / R < Real.pi / 2 := (div_lt_iff₀ hR).mpr
    (by nlinarith : T < Real.pi / 2 * R)
  ext y
  change (y ∈ northHemisphere d ∧ normalInverse d R y.val ∈ Metric.closedBall 0 T) ↔
    chord d (normalPoint d R 0) y ≤ 2 * Real.sin (T / (2 * R))
  rw [show T / (2 * R) = (T / R) / 2 by ring,
    normalPoint_zero_cap_iff_angle d R y (div_nonneg hT hR.le)
      (by linarith [Real.pi_pos] : T / R ≤ Real.pi)]
  constructor
  · rintro ⟨hy, hball⟩
    have hn : R * Real.arccos (y.val 0) ≤ T := by
      simpa only [Metric.mem_closedBall, dist_zero_right, normalInverse_norm d hR hy] using hball
    exact (le_div_iff₀ hR).mpr (by linarith)
  · intro hangle
    have hy : y ∈ northHemisphere d := Real.arccos_lt_pi_div_two.mp (hangle.trans_lt hu)
    refine ⟨hy, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, normalInverse_norm d hR hy,
      mul_comm R] using (le_div_iff₀ hR).mp hangle

theorem normalCapRadius_bounds {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hTpi : T < Real.pi * R / 2) :
    0 < 2 * Real.sin (T / (2 * R)) ∧
    2 * Real.sin (T / (2 * R)) ≤ 2 ∧
    2 * Real.sin (T / (2 * R)) ≤ T / R := by
  have harg : 0 < T / (2 * R) := div_pos hT (by positivity)
  have hargpi : T / (2 * R) < Real.pi :=
    (div_lt_iff₀ (by positivity : 0 < 2 * R)).mpr (by nlinarith [Real.pi_pos])
  refine ⟨mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi harg hargpi), ?_, ?_⟩
  · nlinarith [Real.sin_le_one (T / (2 * R))]
  · nlinarith [Real.sin_le harg.le,
      (show T / R = 2 * (T / (2 * R)) by ring)]

end Riesz.Geometry
