import Riesz.PastProjects.Problem1.MathlibImports

/-!
Part 1 foundations: complete Stage 10 scaffold.
Authority: Part 1/Part1_Foundations.tex and Part 1/Blueprint.md.
Temporary proof placeholders are inventoried in Part 1/execution-evidence/scaffold-placeholders.json.
This file is not certified until every placeholder is discharged and all final gates pass.
-/

open MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator

set_option autoImplicit false

namespace Problem1

noncomputable section

-- def:carriers: Problem1.EuclideanN
abbrev EuclideanN (m : ℕ) : Type := by
  classical
  exact (
    EuclideanSpace ℝ (Fin m)
  )

-- def:carriers: Problem1.UnitSphereN
abbrev UnitSphereN (m : ℕ) : Set (EuclideanN m) := by
  classical
  exact (
    Metric.sphere (0 : EuclideanN m) 1
  )

-- def:carriers: Problem1.OrthogonalN
abbrev OrthogonalN (m : ℕ) : Submonoid (Matrix (Fin m) (Fin m) ℝ) := by
  classical
  exact (
    Matrix.orthogonalGroup (Fin m) ℝ
  )

-- def:carriers: Problem1.Euclidean
abbrev Euclidean (d : ℕ) : Type := by
  classical
  exact (
    EuclideanN (d + 1)
  )

-- def:carriers: Problem1.Sphere
abbrev Sphere (d : ℕ) : Set (Euclidean d) := by
  classical
  exact (
    UnitSphereN (d + 1)
  )

-- def:carriers: Problem1.Orthogonal
abbrev Orthogonal (d : ℕ) : Submonoid (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
  classical
  exact (
    OrthogonalN (d + 1)
  )

-- def:carriers: Problem1.orthogonalNMeasurableSpace
instance orthogonalNMeasurableSpace (m : ℕ) : MeasurableSpace (OrthogonalN m) := by
  classical
  exact (
    borel (OrthogonalN m)
  )

-- def:carriers: Problem1.orthogonalNBorelSpace
instance orthogonalNBorelSpace (m : ℕ) : BorelSpace (OrthogonalN m) := by
  exact ⟨rfl⟩

-- def:carriers: Problem1.unitSphereN_mem_iff
theorem unitSphereN_mem_iff {m : ℕ} (x : EuclideanN m) : x ∈ UnitSphereN m ↔ ‖x‖ = 1 := by
  change dist x 0 = 1 ↔ ‖x‖ = 1
  rw [dist_zero_right]

-- def:carriers: Problem1.unitSphereN_norm
theorem unitSphereN_norm {m : ℕ} (x : UnitSphereN m) : ‖(x : EuclideanN m)‖ = 1 := by
  exact (unitSphereN_mem_iff x.1).mp x.2

-- def:carriers: Problem1.unitSphereN_dist_eq
theorem unitSphereN_dist_eq {m : ℕ} (x y : UnitSphereN m) : dist x y = ‖(x : EuclideanN m) - (y : EuclideanN m)‖ := by
  exact dist_eq_norm (x : EuclideanN m) (y : EuclideanN m)

-- def:north-pole: Problem1.northPoleVector
noncomputable def northPoleVector (m : ℕ) (hm : 1 ≤ m) : EuclideanN m := by
  classical
  exact (
    PiLp.single 2 ⟨0, hm⟩ (1 : ℝ)
  )

-- def:north-pole: Problem1.northPoleVector_apply
theorem northPoleVector_apply (m : ℕ) (hm : 1 ≤ m) (i : Fin m) : northPoleVector m hm i = if i = ⟨0, hm⟩ then 1 else 0 := by
  simp only [northPoleVector, PiLp.single_apply]

-- lem:north-pole-norm: Problem1.northPoleVector_norm
theorem northPoleVector_norm (m : ℕ) (hm : 1 ≤ m) : ‖northPoleVector m hm‖ = 1 := by
  simp only [northPoleVector, PiLp.norm_single, norm_one]

-- lem:north-pole-norm: Problem1.northPoleVector_mem
theorem northPoleVector_mem (m : ℕ) (hm : 1 ≤ m) : northPoleVector m hm ∈ UnitSphereN m := by
  exact (unitSphereN_mem_iff _).mpr (northPoleVector_norm m hm)

-- lem:north-pole-norm: Problem1.northPoleN
noncomputable def northPoleN (m : ℕ) (hm : 1 ≤ m) : UnitSphereN m := by
  classical
  exact (
    ⟨northPoleVector m hm, northPoleVector_mem m hm⟩
  )

-- lem:north-pole-norm: Problem1.northPoleN_coe
theorem northPoleN_coe (m : ℕ) (hm : 1 ≤ m) : (northPoleN m hm : EuclideanN m) = northPoleVector m hm := by
  rfl

-- lem:north-pole-norm: Problem1.northPole
noncomputable def northPole (d : ℕ) : Sphere d := by
  classical
  exact (
    northPoleN (d + 1) (Nat.succ_pos d)
  )

-- lem:north-pole-norm: Problem1.unitSphereN_nonempty
theorem unitSphereN_nonempty (m : ℕ) (hm : 1 ≤ m) : Nonempty (UnitSphereN m) := by
  exact ⟨northPoleN m hm⟩

-- lem:sphere-geometry: Problem1.unitSphereN_isCompact
theorem unitSphereN_isCompact (m : ℕ) : IsCompact (UnitSphereN m : Set (EuclideanN m)) := by
  exact isCompact_sphere (0 : EuclideanN m) 1

-- lem:sphere-geometry: Problem1.unitSphereNCompactSpace
instance unitSphereNCompactSpace (m : ℕ) : CompactSpace (UnitSphereN m) := by
  exact isCompact_iff_compactSpace.mp (unitSphereN_isCompact m)

-- lem:sphere-geometry: Problem1.unitSphereN_geometry
theorem unitSphereN_geometry {m : ℕ} (x y : UnitSphereN m) : (0 ≤ ‖(x : EuclideanN m) - (y : EuclideanN m)‖) ∧ (‖(x : EuclideanN m) - (y : EuclideanN m)‖ ≤ 2) ∧ (‖(x : EuclideanN m) - (y : EuclideanN m)‖ = 0 ↔ x = y) := by
  refine ⟨norm_nonneg _, ?_, ?_⟩
  · calc
      ‖(x : EuclideanN m) - (y : EuclideanN m)‖ ≤
          ‖(x : EuclideanN m)‖ + ‖(y : EuclideanN m)‖ := norm_sub_le _ _
      _ = 2 := by rw [unitSphereN_norm, unitSphereN_norm]; norm_num
  · constructor
    · intro h
      apply Subtype.ext
      exact sub_eq_zero.mp (norm_eq_zero.mp h)
    · intro h
      subst y
      simp

-- def:objects: Problem1.kernel
noncomputable def kernel (d : ℕ) (s : ℝ) (x y : Sphere d) : ℝ := by
  classical
  exact (
    if x = y then 0 else if s = 0 then -Real.log (dist x y) else (1 / s) * Real.rpow (dist x y) (-s)
  )

-- def:objects: Problem1.radialKernel
noncomputable def radialKernel (s : ℝ) (r : {r : ℝ // 0 < r}) : ℝ := by
  classical
  exact (
    if s = 0 then -Real.log r.1 else (1 / s) * Real.rpow r.1 (-s)
  )

-- def:objects: Problem1.kernelLowerConstant
noncomputable def kernelLowerConstant (s : ℝ) : ℝ := by
  classical
  exact (
    if 0 < s then 0 else if s = 0 then -Real.log 2 else Real.rpow 2 (-s) / s
  )

-- lem:kernel-branches: Problem1.kernel_diag
theorem kernel_diag (d : ℕ) (s : ℝ) (x : Sphere d) : kernel d s x x = 0 := by
  rw [kernel, if_pos rfl]

-- lem:kernel-branches: Problem1.sphere_dist_pos
theorem sphere_dist_pos {d : ℕ} {x y : Sphere d} (hxy : x ≠ y) : 0 < dist x y := by
  exact dist_pos.mpr hxy

-- lem:kernel-branches: Problem1.kernel_zero_offDiag
theorem kernel_zero_offDiag {d : ℕ} {x y : Sphere d} (hxy : x ≠ y) : kernel d 0 x y = -Real.log (dist x y) := by
  rw [kernel, if_neg hxy, if_pos rfl]

-- lem:kernel-branches: Problem1.kernel_ne_zero_offDiag
theorem kernel_ne_zero_offDiag {d : ℕ} {s : ℝ} (hs : s ≠ 0) {x y : Sphere d} (hxy : x ≠ y) : kernel d s x y = (1 / s) * Real.rpow (dist x y) (-s) := by
  simp only [kernel, if_neg hxy, if_neg hs]

-- lem:kernel-branches: Problem1.kernel_radial
theorem kernel_radial {d : ℕ} (s : ℝ) {x y : Sphere d} (hxy : x ≠ y) (r : {r : ℝ // 0 < r}) (hr : r.1 = dist x y) : kernel d s x y = radialKernel s r := by
  by_cases hs : s = 0
  · simp only [kernel, radialKernel, if_neg hxy, if_pos hs, hr]
  · simp only [kernel, radialKernel, if_neg hxy, if_neg hs, hr]

-- lem:kernel-measurable: Problem1.kernel_measurable
theorem kernel_measurable (d : ℕ) (s : ℝ) : Measurable (fun p : Sphere d × Sphere d => kernel d s p.1 p.2) := by
  unfold kernel
  refine Measurable.ite
    ((isClosed_eq continuous_fst continuous_snd).measurableSet)
    measurable_const ?_
  by_cases hs : s = 0
  · simp only [hs, if_pos]
    exact (Real.measurable_log.comp measurable_dist).neg
  · simp only [hs, if_false]
    exact measurable_const.mul (measurable_dist.pow_const (-s))

-- lem:kernel-symmetry: Problem1.kernel_symmetry
theorem kernel_symmetry (d : ℕ) (s : ℝ) (x y : Sphere d) : kernel d s x y = kernel d s y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  · simp [kernel, hxy, Ne.symm hxy, dist_comm]

-- lem:kernel-isometry: Problem1.kernel_isometry
theorem kernel_isometry (d : ℕ) (s : ℝ) (T : Sphere d → Sphere d) (hT : ∀ x y, dist (T x) (T y) = dist x y) (x y : Sphere d) : kernel d s (T x) (T y) = kernel d s x y := by
  by_cases hxy : x = y
  · subst y
    simp only [kernel_diag]
  · have hTxy : T x ≠ T y := by
      intro h
      apply hxy
      apply dist_eq_zero.mp
      calc
        dist x y = dist (T x) (T y) := (hT x y).symm
        _ = 0 := by rw [h, dist_self]
    simp only [kernel, if_neg hTxy, if_neg hxy, hT x y]

-- lem:kernel-lower: Problem1.kernelLowerConstant_nonpos
theorem kernelLowerConstant_nonpos (s : ℝ) : kernelLowerConstant s ≤ 0 := by
  unfold kernelLowerConstant
  split_ifs with hspos hs0
  · exact le_rfl
  · exact neg_nonpos.mpr (Real.log_nonneg (by norm_num))
  · exact div_nonpos_of_nonneg_of_nonpos
      (Real.rpow_nonneg (by norm_num) _) (le_of_not_gt hspos)

-- lem:kernel-lower: Problem1.kernel_lower_bound
theorem kernel_lower_bound (d : ℕ) (s : ℝ) (x y : Sphere d) : kernelLowerConstant s ≤ kernel d s x y := by
  by_cases hxy : x = y
  · subst y
    rw [kernel_diag]
    exact kernelLowerConstant_nonpos s
  · have hdist : dist x y ≤ 2 := by
      rw [unitSphereN_dist_eq]
      exact (unitSphereN_geometry x y).2.1
    by_cases hspos : 0 < s
    · rw [kernelLowerConstant, if_pos hspos,
        kernel_ne_zero_offDiag hspos.ne' hxy]
      exact mul_nonneg (one_div_nonneg.mpr hspos.le)
        (Real.rpow_nonneg dist_nonneg _)
    · have hsle : s ≤ 0 := le_of_not_gt hspos
      by_cases hs0 : s = 0
      · subst s
        rw [kernelLowerConstant, if_neg (by norm_num), if_pos rfl,
          kernel_zero_offDiag hxy]
        exact neg_le_neg (Real.log_le_log (sphere_dist_pos hxy) hdist)
      · rw [kernelLowerConstant, if_neg hspos, if_neg hs0,
          kernel_ne_zero_offDiag hs0 hxy]
        have hp := Real.rpow_le_rpow dist_nonneg hdist (neg_nonneg.mpr hsle)
        have hdv := div_le_div_of_nonpos_of_le hsle hp
        simpa [div_eq_mul_inv, mul_comm] using hdv

-- lem:kernel-negative: Problem1.kernel_eq_rpow_of_neg
theorem kernel_eq_rpow_of_neg (d : ℕ) (s : ℝ) (hs : s < 0) (x y : Sphere d) : kernel d s x y = (1 / s) * Real.rpow (dist x y) (-s) := by
  by_cases hxy : x = y
  · subst y
    simp [kernel, Real.zero_rpow (neg_ne_zero.mpr hs.ne)]
  · simp [kernel, hxy, hs.ne]

-- lem:kernel-negative: Problem1.kernel_continuous_of_neg
theorem kernel_continuous_of_neg (d : ℕ) (s : ℝ) (hs : s < 0) : Continuous (fun p : Sphere d × Sphere d => kernel d s p.1 p.2) := by
  rw [show (fun p : Sphere d × Sphere d => kernel d s p.1 p.2) =
      (fun p => (1 / s) * Real.rpow (dist p.1 p.2) (-s)) by
    funext p
    exact kernel_eq_rpow_of_neg d s hs p.1 p.2]
  exact continuous_const.mul
    ((Real.continuous_rpow_const (neg_nonneg.mpr hs.le)).comp
      (continuous_fst.dist continuous_snd))

-- lem:kernel-negative: Problem1.kernel_nonpos_of_neg
theorem kernel_nonpos_of_neg (d : ℕ) (s : ℝ) (hs : s < 0) (x y : Sphere d) : kernel d s x y ≤ 0 := by
  rw [kernel_eq_rpow_of_neg d s hs]
  exact mul_nonpos_of_nonpos_of_nonneg (one_div_nonpos.mpr hs.le)
    (Real.rpow_nonneg dist_nonneg (-s))

-- lem:kernel-basic: Problem1.kernel_nonneg_of_pos
theorem kernel_nonneg_of_pos (d : ℕ) (s : ℝ) (hs : 0 < s) (x y : Sphere d) : 0 ≤ kernel d s x y := by
  by_cases hxy : x = y
  · subst y
    simp [kernel]
  · simp only [kernel, if_neg hxy, if_neg hs.ne']
    exact mul_nonneg (one_div_nonneg.mpr hs.le)
      (Real.rpow_nonneg dist_nonneg (-s))

-- lem:kernel-basic: Problem1.kernel_basic
theorem kernel_basic (d : ℕ) (s : ℝ) : (∀ x y : Sphere d, kernel d s x y = kernel d s y x) ∧ Measurable (fun p : Sphere d × Sphere d => kernel d s p.1 p.2) ∧ (∀ x y : Sphere d, kernelLowerConstant s ≤ kernel d s x y) ∧ (∀ T : Sphere d → Sphere d, (∀ x y, dist (T x) (T y) = dist x y) → ∀ x y, kernel d s (T x) (T y) = kernel d s x y) ∧ (s < 0 → Continuous (fun p : Sphere d × Sphere d => kernel d s p.1 p.2) ∧ ∀ x y : Sphere d, kernel d s x y ≤ 0) ∧ (0 < s → ∀ x y : Sphere d, 0 ≤ kernel d s x y) := by
  exact ⟨kernel_symmetry d s, kernel_measurable d s, kernel_lower_bound d s,
    kernel_isometry d s,
    fun hs => ⟨kernel_continuous_of_neg d s hs, kernel_nonpos_of_neg d s hs⟩,
    kernel_nonneg_of_pos d s⟩

-- def:circle-vector: Problem1.circleVector
noncomputable def circleVector (d : ℕ) (hd : 2 ≤ d) (t : ℝ) : Euclidean d := by
  classical
  exact (
    WithLp.toLp 2 (fun i : Fin (d + 1) => if i.val = 0 then (1 - t ^ 2) / (1 + t ^ 2) else if i.val = 1 then (2 * t) / (1 + t ^ 2) else 0)
  )

-- lem:circle-norm: Problem1.circleVector_norm
theorem circleVector_norm (d : ℕ) (hd : 2 ≤ d) (t : ℝ) : ‖circleVector d hd t‖ = 1 := by
  have hden : 0 < (1 : ℝ) + t ^ 2 := by
    nlinarith [sq_nonneg t]
  cases d with
  | zero => omega
  | succ d =>
      cases d with
      | zero => omega
      | succ d =>
          apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
          calc
            ‖circleVector (d + 1 + 1) hd t‖ ^ 2 =
                ∑ i : Fin (d + 1 + 1 + 1),
                  (circleVector (d + 1 + 1) hd t i) ^ 2 :=
              EuclideanSpace.real_norm_sq_eq _
            _ = ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 +
                ((2 * t) / (1 + t ^ 2)) ^ 2 := by
              rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
              simp [circleVector, PiLp.toLp_apply, Fin.val_succ]
            _ = (1 : ℝ) ^ 2 := by
              field_simp [ne_of_gt hden] <;> ring

-- lem:circle-norm: Problem1.circleVector_mem
theorem circleVector_mem (d : ℕ) (hd : 2 ≤ d) (t : ℝ) : circleVector d hd t ∈ Sphere d := by
  exact (unitSphereN_mem_iff _).mpr (circleVector_norm d hd t)

-- lem:circle-recovery: Problem1.circleVector_recovery
theorem circleVector_recovery (d : ℕ) (hd : 2 ≤ d) (t : ℝ) : (1 + circleVector d hd t 0 = 2 / (1 + t ^ 2)) ∧ (0 < 2 / (1 + t ^ 2)) ∧ (circleVector d hd t 1 / (1 + circleVector d hd t 0) = t) := by
  have hden : 0 < (1 : ℝ) + t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hindex : (1 : Fin (d + 1)).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < d + 1)]
  have hzero : circleVector d hd t 0 =
      (1 - t ^ 2) / (1 + t ^ 2) := by
    simp [circleVector, PiLp.toLp_apply]
  have hone : circleVector d hd t 1 =
      (2 * t) / (1 + t ^ 2) := by
    simp only [circleVector, PiLp.toLp_apply, hindex, Nat.one_ne_zero, if_false, if_true]
  have hsum : 1 + circleVector d hd t 0 = 2 / (1 + t ^ 2) := by
    rw [hzero]
    field_simp [ne_of_gt hden] <;> ring
  refine ⟨hsum, div_pos (by norm_num) hden, ?_⟩
  rw [hone, hsum]
  field_simp [ne_of_gt hden] <;> ring

-- lem:circle-parametrization: Problem1.circleParametrization
noncomputable def circleParametrization (d : ℕ) (hd : 2 ≤ d) : ℝ → Sphere d := by
  classical
  exact (
    fun t => ⟨circleVector d hd t, circleVector_mem d hd t⟩
  )

-- lem:circle-parametrization: Problem1.circleParametrization_injective
theorem circleParametrization_injective (d : ℕ) (hd : 2 ≤ d) : Function.Injective (circleParametrization d hd) := by
  intro a b hab
  have hvector : circleVector d hd a = circleVector d hd b :=
    congrArg (fun x : Sphere d => (x : Euclidean d)) hab
  calc
    a = circleVector d hd a 1 / (1 + circleVector d hd a 0) :=
      (circleVector_recovery d hd a).2.2.symm
    _ = circleVector d hd b 1 / (1 + circleVector d hd b 0) := by
      rw [hvector]
    _ = b := (circleVector_recovery d hd b).2.2

-- lem:finite-avoidance: Problem1.sphere_infinite
theorem sphere_infinite (d : ℕ) (hd : 2 ≤ d) : Infinite (Sphere d) := by
  exact Infinite.of_injective (circleParametrization d hd)
    (circleParametrization_injective d hd)

-- lem:finite-avoidance: Problem1.finite_avoidance
theorem finite_avoidance (d : ℕ) (hd : 2 ≤ d) (F : Set (Sphere d)) (hF : F.Finite) : Fᶜ.Nonempty := by
  letI : Infinite (Sphere d) := sphere_infinite d hd
  exact hF.exists_notMem

-- lem:injective-configurations: Problem1.exists_injective_configuration
theorem exists_injective_configuration (d : ℕ) (hd : 2 ≤ d) (M : ℕ) : ∃ ω : Fin M → Sphere d, Function.Injective ω := by
  refine ⟨fun i : Fin M => circleParametrization d hd (i.val : ℝ), ?_⟩
  intro i j hij
  apply Fin.val_injective
  exact (Nat.cast_injective (R := ℝ))
    (circleParametrization_injective d hd hij)

-- def:configurations: Problem1.Config
abbrev Config (d N : ℕ) : Type := by
  classical
  exact (
    Fin N → Sphere d
  )

-- def:configurations: Problem1.siteSet
noncomputable def siteSet {d N : ℕ} (ω : Config d N) : Set (Sphere d) := by
  classical
  exact (
    Set.range ω
  )

-- def:configurations: Problem1.potential
noncomputable def potential {d N : ℕ} (s : ℝ) (ω : Config d N) (x : Sphere d) : ℝ := by
  classical
  exact (
    ∑ j : Fin N, kernel d s x (ω j)
  )

-- def:configurations: Problem1.potentialValueSet
noncomputable def potentialValueSet {d N : ℕ} (s : ℝ) (ω : Config d N) : Set ℝ := by
  classical
  exact (
    {a : ℝ | ∃ x : Sphere d, x ∉ siteSet ω ∧ a = potential s ω x}
  )

-- def:configurations: Problem1.configPolarization
noncomputable def configPolarization {d N : ℕ} (s : ℝ) (ω : Config d N) : ℝ := by
  classical
  exact (
    sInf (potentialValueSet s ω)
  )

-- def:configurations: Problem1.polarizationValueSet
noncomputable def polarizationValueSet (d : ℕ) (s : ℝ) (N : ℕ) : Set ℝ := by
  classical
  exact (
    {a : ℝ | ∃ ω : Config d N, a = configPolarization s ω}
  )

-- def:configurations: Problem1.maxPolarization
noncomputable def maxPolarization (d : ℕ) (s : ℝ) (N : ℕ) : ℝ := by
  classical
  exact (
    sSup (polarizationValueSet d s N)
  )

-- def:energy: Problem1.EnergyConfig
abbrev EnergyConfig (d M : ℕ) : Type := by
  classical
  exact (
    {ω : Config d M // Function.Injective ω}
  )

-- def:energy: Problem1.finiteEnergy
noncomputable def finiteEnergy {d : ℕ} {J : Type*} [Fintype J] (s : ℝ) (z : J → Sphere d) : ℝ := by
  classical
  exact (
    ∑ i : J, ∑ j : J, if i = j then 0 else kernel d s (z i) (z j)
  )

-- def:energy: Problem1.energyValueSet
noncomputable def energyValueSet (d : ℕ) (s : ℝ) (M : ℕ) : Set ℝ := by
  classical
  exact (
    {a : ℝ | ∃ ω : EnergyConfig d M, a = finiteEnergy s ω.1}
  )

-- def:energy: Problem1.minEnergy
noncomputable def minEnergy (d : ℕ) (s : ℝ) (M : ℕ) : ℝ := by
  classical
  exact (
    sInf (energyValueSet d s M)
  )

-- lem:potential-value-set-nonempty: Problem1.potentialValueSet_nonempty
theorem potentialValueSet_nonempty (d : ℕ) (hd : 2 ≤ d) (N : ℕ) (s : ℝ) (ω : Config d N) : (potentialValueSet s ω).Nonempty := by
  have hsites : (siteSet ω).Finite := by
    simpa only [siteSet] using Set.finite_range ω
  obtain ⟨x, hx⟩ := finite_avoidance d hd (siteSet ω) hsites
  exact ⟨potential s ω x, x, hx, rfl⟩

-- lem:potential-lower: Problem1.potential_lower_bound
theorem potential_lower_bound (d N : ℕ) (s : ℝ) (ω : Config d N) (x : Sphere d) : (N : ℝ) * kernelLowerConstant s ≤ potential s ω x := by
  calc
    (N : ℝ) * kernelLowerConstant s =
        ∑ _j : Fin N, kernelLowerConstant s := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ j : Fin N, kernel d s x (ω j) :=
      Finset.sum_le_sum fun j _ => kernel_lower_bound d s x (ω j)
    _ = potential s ω x := rfl

-- lem:potential-value-set-bddBelow: Problem1.potentialValueSet_bddBelow
theorem potentialValueSet_bddBelow (d N : ℕ) (s : ℝ) (ω : Config d N) : ((N : ℝ) * kernelLowerConstant s ∈ lowerBounds (potentialValueSet s ω)) ∧ BddBelow (potentialValueSet s ω) := by
  have hLower : (N : ℝ) * kernelLowerConstant s ∈
      lowerBounds (potentialValueSet s ω) := by
    refine mem_lowerBounds.2 ?_
    rintro a ⟨x, hx, rfl⟩
    exact potential_lower_bound d N s ω x
  exact ⟨hLower, ⟨_, hLower⟩⟩

-- lem:potential-infimum: Problem1.potential_infimum
theorem potential_infimum (d : ℕ) (hd : 2 ≤ d) (N : ℕ) (s : ℝ) (ω : Config d N) : ((N : ℝ) * kernelLowerConstant s ≤ configPolarization s ω) ∧ (∀ x : Sphere d, x ∉ siteSet ω → configPolarization s ω ≤ potential s ω x) := by
  constructor
  · exact le_csInf (potentialValueSet_nonempty d hd N s ω)
      (potentialValueSet_bddBelow d N s ω).1
  · intro x hx
    exact csInf_le (potentialValueSet_bddBelow d N s ω).2 ⟨x, hx, rfl⟩

-- lem:polarization-value-set-nonempty: Problem1.polarizationValueSet_nonempty
theorem polarizationValueSet_nonempty (d N : ℕ) (s : ℝ) : (polarizationValueSet d s N).Nonempty := by
  let ω : Config d N := fun _ => northPole d
  exact ⟨configPolarization s ω, ω, rfl⟩

-- lem:energy-value-set-nonempty: Problem1.energyValueSet_nonempty
theorem energyValueSet_nonempty (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (s : ℝ) : (energyValueSet d s M).Nonempty := by
  obtain ⟨z, hz⟩ := exists_injective_configuration d hd M
  exact ⟨finiteEnergy s z, ⟨z, hz⟩, rfl⟩

-- lem:off-diagonal-count: Problem1.offDiagonal_card
theorem offDiagonal_card (M : ℕ) : ((Finset.univ : Finset (Fin M)).offDiag).card = M * (M - 1) := by
  simp only [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
    Nat.mul_sub_left_distrib, mul_one]

-- lem:energy-lower: Problem1.finiteEnergy_lower_bound
theorem finiteEnergy_lower_bound (d M : ℕ) (s : ℝ) (z : Fin M → Sphere d) : ((M * (M - 1) : ℕ) : ℝ) * kernelLowerConstant s ≤ finiteEnergy s z := by
  classical
  have hrow (i : Fin M) :
      ((M - 1 : ℕ) : ℝ) * kernelLowerConstant s ≤
        ∑ j : Fin M, if i = j then 0 else kernel d s (z i) (z j) := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i, kernelLowerConstant s := by
        simp [Finset.card_erase_of_mem]
      _ ≤ ∑ j ∈ Finset.univ.erase i, kernel d s (z i) (z j) := by
        apply Finset.sum_le_sum
        intro j _
        exact kernel_lower_bound d s (z i) (z j)
      _ = ∑ j : Fin M, if i = j then 0 else kernel d s (z i) (z j) := by
        rw [← Finset.sum_erase Finset.univ (a := i) (by simp)]
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [Ne.symm hji]
  calc
    ((M * (M - 1) : ℕ) : ℝ) * kernelLowerConstant s =
        ∑ _i : Fin M, ((M - 1 : ℕ) : ℝ) * kernelLowerConstant s := by
      simp [Nat.cast_mul, nsmul_eq_mul, mul_assoc]
    _ ≤ ∑ i : Fin M, ∑ j : Fin M,
        if i = j then 0 else kernel d s (z i) (z j) :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = finiteEnergy s z := by
      unfold finiteEnergy
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · simp only [if_pos hij]
      · simp only [if_neg hij]

-- lem:energy-value-set-bddBelow: Problem1.energyValueSet_bddBelow
theorem energyValueSet_bddBelow (d M : ℕ) (s : ℝ) : ((((M * (M - 1) : ℕ) : ℝ) * kernelLowerConstant s) ∈ lowerBounds (energyValueSet d s M)) ∧ BddBelow (energyValueSet d s M) := by
  have hLower :
      (((M * (M - 1) : ℕ) : ℝ) * kernelLowerConstant s) ∈
        lowerBounds (energyValueSet d s M) := by
    intro a ha
    rcases ha with ⟨ω, rfl⟩
    exact finiteEnergy_lower_bound d M s ω.1
  exact ⟨hLower, ⟨_, hLower⟩⟩

-- lem:energy-small: Problem1.finiteEnergy_zero
theorem finiteEnergy_zero (d : ℕ) (s : ℝ) (z : Fin 0 → Sphere d) : finiteEnergy s z = 0 := by
  simp only [finiteEnergy, Fintype.sum_empty]

-- lem:energy-small: Problem1.finiteEnergy_one
theorem finiteEnergy_one (d : ℕ) (s : ℝ) (z : Fin 1 → Sphere d) : finiteEnergy s z = 0 := by
  classical
  simp [finiteEnergy, Fintype.sum_unique]

-- lem:energy-small: Problem1.energyValueSet_zero
theorem energyValueSet_zero (d : ℕ) (s : ℝ) : energyValueSet d s 0 = {0} := by
  ext a
  constructor
  · rintro ⟨ω, rfl⟩
    exact Set.mem_singleton_iff.mpr (finiteEnergy_zero d s ω.1)
  · intro ha
    have ha0 : a = 0 := Set.mem_singleton_iff.mp ha
    let z : Fin 0 → Sphere d := Fin.elim0
    have hz : Function.Injective z := by
      intro i
      exact Fin.elim0 i
    refine ⟨⟨z, hz⟩, ?_⟩
    exact ha0.trans (finiteEnergy_zero d s z).symm

-- lem:energy-small: Problem1.energyValueSet_one
theorem energyValueSet_one (d : ℕ) (s : ℝ) : energyValueSet d s 1 = {0} := by
  ext a
  constructor
  · rintro ⟨ω, rfl⟩
    exact Set.mem_singleton_iff.mpr (finiteEnergy_one d s ω.1)
  · intro ha
    have ha0 : a = 0 := Set.mem_singleton_iff.mp ha
    let z : Fin 1 → Sphere d := fun _ => northPole d
    have hz : Function.Injective z := fun _ _ _ => Subsingleton.elim _ _
    refine ⟨⟨z, hz⟩, ?_⟩
    exact ha0.trans (finiteEnergy_one d s z).symm

-- lem:energy-small: Problem1.minEnergy_small
theorem minEnergy_small (d : ℕ) (s : ℝ) : minEnergy d s 0 = 0 ∧ minEnergy d s 1 = 0 := by
  simp only [minEnergy, energyValueSet_zero, energyValueSet_one, csInf_singleton, and_self]

-- def:pochhammer: Problem1.pochhammer
noncomputable def pochhammer (a : ℝ) (k : ℕ) : ℝ := by
  classical
  exact (
    ∏ j ∈ Finset.range k, (a + (j : ℝ))
  )

-- def:pochhammer: Problem1.fallingPochhammer
noncomputable def fallingPochhammer (a : ℝ) (k : ℕ) : ℝ := by
  classical
  exact (
    ∏ j ∈ Finset.range k, (a - (j : ℝ))
  )

-- def:pochhammer: Problem1.pochhammer_zero
theorem pochhammer_zero (a : ℝ) :
    pochhammer a 0 = 1 := by
  simpa only [pochhammer] using
    (Finset.prod_range_zero (fun j : ℕ => a + (j : ℝ)))

-- def:pochhammer: Problem1.fallingPochhammer_zero
theorem fallingPochhammer_zero (a : ℝ) :
    fallingPochhammer a 0 = 1 := by
  simpa only [fallingPochhammer] using
    (Finset.prod_range_zero (fun j : ℕ => a - (j : ℝ)))

-- lem:pochhammer-library: Problem1.pochhammer_eq_ascPochhammer_eval
theorem pochhammer_eq_ascPochhammer_eval (a : ℝ) (k : ℕ) :
    pochhammer a k = (ascPochhammer ℝ k).eval a := by
  induction k with
  | zero => simp [pochhammer]
  | succ k ih =>
      rw [pochhammer] at ih
      rw [pochhammer, Finset.prod_range_succ, ascPochhammer_succ_eval, ih]

-- lem:pochhammer-library: Problem1.fallingPochhammer_eq_descPochhammer_eval
theorem fallingPochhammer_eq_descPochhammer_eval (a : ℝ) (k : ℕ) :
    fallingPochhammer a k = (descPochhammer ℝ k).eval a := by
  simpa only [fallingPochhammer] using (descPochhammer_eval_eq_prod_range k a).symm

-- lem:pochhammer-library: Problem1.pochhammer_eq_ascPochhammer_int_smeval
theorem pochhammer_eq_ascPochhammer_int_smeval (a : ℝ) (k : ℕ) :
    pochhammer a k = (ascPochhammer ℤ k).smeval a := by
  rw [Polynomial.ascPochhammer_smeval_cast ℤ,
    Polynomial.ascPochhammer_smeval_eq_eval,
    pochhammer_eq_ascPochhammer_eval]

-- lem:pochhammer-library: Problem1.fallingPochhammer_eq_descPochhammer_int_smeval
theorem fallingPochhammer_eq_descPochhammer_int_smeval (a : ℝ) (k : ℕ) :
    fallingPochhammer a k = (descPochhammer ℤ k).smeval a := by
  rw [fallingPochhammer_eq_descPochhammer_eval,
    Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval,
    descPochhammer_eval_eq_ascPochhammer]

-- lem:pochhammer-split: Problem1.pochhammer_add
theorem pochhammer_add (a : ℝ) (j k : ℕ) :
    pochhammer a (j + k) = pochhammer a j * pochhammer (a + (j : ℝ)) k := by
  simp only [pochhammer_eq_ascPochhammer_eval]
  have h := congrArg (Polynomial.eval a) (ascPochhammer_mul ℝ j k)
  simpa [Polynomial.eval_mul, ascPochhammer_eval_comp, Nat.cast_comm] using h.symm

-- lem:pochhammer-positive: Problem1.pochhammer_positive
theorem pochhammer_positive (a : ℝ) (k : ℕ) (ha : 0 < a) :
    0 < pochhammer a k := by
  unfold pochhammer
  apply Finset.prod_pos
  intro j _
  exact add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg j)

-- lem:pochhammer-negative-natural: Problem1.pochhammer_neg_nat
theorem pochhammer_neg_nat (n k : ℕ) :
    pochhammer (-(n : ℝ)) k = if k ≤ n then (-1 : ℝ) ^ k * (n.factorial : ℝ) / ((n - k).factorial : ℝ) else 0 := by
  by_cases hkn : k ≤ n
  · rw [if_pos hkn, pochhammer_eq_ascPochhammer_eval,
      ascPochhammer_eval_neg_eq_descPochhammer,
      descPochhammer_eval_eq_descFactorial]
    have hfac :
        ((n - k).factorial : ℝ) * (n.descFactorial k : ℝ) =
          (n.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hkn
    rw [eq_div_iff (by positivity : ((n - k).factorial : ℝ) ≠ 0)]
    calc
      (-1 : ℝ) ^ k * (n.descFactorial k : ℝ) *
          ((n - k).factorial : ℝ) =
          (-1 : ℝ) ^ k *
            (((n - k).factorial : ℝ) * (n.descFactorial k : ℝ)) := by
        ring
      _ = (-1 : ℝ) ^ k * (n.factorial : ℝ) := by
        rw [hfac]
  · rw [if_neg hkn, pochhammer_eq_ascPochhammer_eval]
    exact ascPochhammer_eval_neg_coe_nat_of_lt (Nat.lt_of_not_ge hkn)

-- lem:pochhammer-reversal: Problem1.pochhammer_reverse
theorem pochhammer_reverse (x : ℝ) (n : ℕ) :
    pochhammer (1 - x - (n : ℝ)) n = (-1 : ℝ) ^ n * pochhammer x n := by
  rw [pochhammer_eq_ascPochhammer_eval,
    show 1 - x - (n : ℝ) = -(x + n - 1) by ring,
    ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_ascPochhammer,
    pochhammer_eq_ascPochhammer_eval]
  congr 2
  ring

-- lem:pochhammer-reversal: Problem1.pochhammer_reverse_prefix
theorem pochhammer_reverse_prefix (x : ℝ) (n j : ℕ) (hj : j ≤ n) :
    pochhammer (1 - x - (n : ℝ)) j = (-1 : ℝ) ^ j * pochhammer (x + (n : ℝ) - (j : ℝ)) j := by
  have harg :
      1 - (x + (n : ℝ) - (j : ℝ)) - (j : ℝ) =
        1 - x - (n : ℝ) := by
    ring
  simpa only [harg] using
    (pochhammer_reverse (x + (n : ℝ) - (j : ℝ)) j)

-- lem:falling-reversal: Problem1.fallingPochhammer_reversal
theorem fallingPochhammer_reversal (x : ℝ) (n k : ℕ) (hk : k ≤ n) :
    fallingPochhammer (-x) k = (-1 : ℝ) ^ k * pochhammer x k ∧ fallingPochhammer (x + (n : ℝ) - 1) (n - k) = pochhammer (x + (k : ℝ)) (n - k) := by
  constructor
  · rw [fallingPochhammer_eq_descPochhammer_int_smeval,
      Polynomial.descPochhammer_smeval_eq_ascPochhammer,
      Polynomial.ascPochhammer_smeval_eq_eval,
      ← pochhammer_eq_ascPochhammer_eval,
      show -x - (k : ℝ) + 1 = 1 - x - (k : ℝ) by ring,
      pochhammer_reverse]
  · rw [fallingPochhammer_eq_descPochhammer_int_smeval,
      Polynomial.descPochhammer_smeval_eq_ascPochhammer,
      Polynomial.ascPochhammer_smeval_eq_eval,
      ← pochhammer_eq_ascPochhammer_eval, Nat.cast_sub hk]
    congr 1
    ring

-- lem:pochhammer-shift-nonzero: Problem1.pochhammer_shift_ne_zero
theorem pochhammer_shift_ne_zero (C : ℝ) (n j r : ℕ) (hC : ∀ k : ℕ, k ≤ n → pochhammer C k ≠ 0) (hjr : j + r ≤ n) :
    pochhammer (C + (j : ℝ)) r ≠ 0 := by
  have hprod := hC (j + r) hjr
  rw [pochhammer_add C j r] at hprod
  exact right_ne_zero_of_mul hprod

-- lem:binomial-adapter: Problem1.pochhammer_neg_nat_div_factorial
theorem pochhammer_neg_nat_div_factorial (n k : ℕ) (hk : k ≤ n) :
    pochhammer (-(n : ℝ)) k / (k.factorial : ℝ) = (-1 : ℝ) ^ k * (n.choose k : ℝ) := by
  rw [pochhammer_neg_nat, if_pos hk, Nat.cast_choose ℝ hk]
  have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hnkfac : ((n - k).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hkfac, hnkfac] <;> ring

-- lem:binomial-adapter: Problem1.choose_add_div_factorial
theorem choose_add_div_factorial (j r : ℕ) :
    ((j + r).choose j : ℝ) / ((j + r).factorial : ℝ) = 1 / ((j.factorial : ℝ) * (r.factorial : ℝ)) := by
  rw [Nat.cast_add_choose ℝ]
  have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
  have hrfac : (r.factorial : ℝ) ≠ 0 := by positivity
  have hjrfac : ((j + r).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hjfac, hrfac, hjrfac]

-- lem:pochhammer-rules: Problem1.pochhammer_rules
theorem pochhammer_rules :
    (∀ (a : ℝ) (j k : ℕ), pochhammer a (j + k) = pochhammer a j * pochhammer (a + (j : ℝ)) k) ∧
    (∀ (a : ℝ) (k : ℕ), 0 < a → 0 < pochhammer a k) ∧
    (∀ n k : ℕ, pochhammer (-(n : ℝ)) k = if k ≤ n then (-1 : ℝ) ^ k * (n.factorial : ℝ) / ((n - k).factorial : ℝ) else 0) ∧
    (∀ (x : ℝ) (n j : ℕ), j ≤ n → pochhammer (1 - x - (n : ℝ)) j = (-1 : ℝ) ^ j * pochhammer (x + (n : ℝ) - (j : ℝ)) j) ∧
    (∀ (x : ℝ) (n : ℕ), pochhammer (1 - x - (n : ℝ)) n = (-1 : ℝ) ^ n * pochhammer x n) := by
  exact ⟨pochhammer_add, pochhammer_positive, pochhammer_neg_nat,
    pochhammer_reverse_prefix, pochhammer_reverse⟩

-- lem:polynomial-open-box: Problem1.polynomial_eq_of_eq_on_open_box
theorem polynomial_eq_of_eq_on_open_box (q : ℕ) (P Q : MvPolynomial (Fin q) ℝ) (a b : Fin q → ℝ) (hab : ∀ i, a i < b i) (heval : ∀ x : Fin q → ℝ, (∀ i, a i < x i ∧ x i < b i) → MvPolynomial.eval x P = MvPolynomial.eval x Q) :
    P = Q := by
  apply MvPolynomial.funext_set (fun i => Set.Ioo (a i) (b i))
    (fun i => Set.Ioo_infinite (hab i))
  intro x hx
  exact heval x (fun i => hx i (Set.mem_univ i))

-- def:beta: Problem1.betaRealDensity
noncomputable def betaRealDensity (a b t : ℝ) : ℝ := by
  classical
  exact (
    if 0 < t ∧ t < 1 then Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1) else 0
  )

-- def:beta: Problem1.betaComplexIntegrand
noncomputable def betaComplexIntegrand (a b t : ℝ) : ℂ := by
  classical
  exact (
    (t : ℂ) ^ ((a - 1 : ℝ) : ℂ) * ((1 - t : ℝ) : ℂ) ^ ((b - 1 : ℝ) : ℂ)
  )

-- lem:beta-measurable: Problem1.beta_measurable
theorem beta_measurable (a b : ℝ) :
    Measurable (betaRealDensity a b) := by
  unfold betaRealDensity
  refine Measurable.ite measurableSet_Ioo ?_ measurable_const
  exact (measurable_id.pow_const (a - 1)).mul
    ((measurable_const.sub measurable_id).pow_const (b - 1))

-- lem:beta-complex-integrand: Problem1.beta_complex_integrand
theorem beta_complex_integrand (a b t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    betaComplexIntegrand a b t = (betaRealDensity a b t : ℂ) ∧ ‖betaComplexIntegrand a b t‖ = betaRealDensity a b t := by
  have ht : 0 < t ∧ t < 1 := ⟨ht0, ht1⟩
  have ht01 : 0 < 1 - t := sub_pos.mpr ht1
  have heq : betaComplexIntegrand a b t = (betaRealDensity a b t : ℂ) := by
    simp only [betaComplexIntegrand, betaRealDensity, if_pos ht,
      Real.rpow_eq_pow, Complex.ofReal_mul,
      Complex.ofReal_cpow ht0.le (a - 1),
      Complex.ofReal_cpow ht01.le (b - 1)]
  have hnonneg : 0 ≤ betaRealDensity a b t := by
    rw [betaRealDensity, if_pos ht]
    exact (mul_pos (Real.rpow_pos_of_pos ht0 (a - 1))
      (Real.rpow_pos_of_pos ht01 (b - 1))).le
  refine ⟨heq, ?_⟩
  rw [heq]
  exact Complex.norm_of_nonneg hnonneg

-- lem:beta-integrable: Problem1.beta_complex_intervalIntegrable
theorem beta_complex_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (betaComplexIntegrand a b) volume 0 1 := by
  unfold betaComplexIntegrand
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
    (Complex.betaIntegral_convergent
      (u := (a : ℂ)) (v := (b : ℂ))
      (by simpa only [Complex.ofReal_re] using ha)
      (by simpa only [Complex.ofReal_re] using hb))

-- lem:beta-integrable: Problem1.beta_integrable
theorem beta_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Integrable (betaRealDensity a b) volume ∧ IntegrableOn (betaRealDensity a b) (Set.Icc 0 1) volume := by
  have hcomplexIoc : IntegrableOn (betaComplexIntegrand a b)
      (Set.Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (beta_complex_intervalIntegrable a b ha hb)
  have hnormIoo : IntegrableOn (fun t => ‖betaComplexIntegrand a b t‖)
      (Set.Ioo 0 1) volume :=
    (hcomplexIoc.mono_set Set.Ioo_subset_Ioc_self).norm
  have hdensityIoo : IntegrableOn (betaRealDensity a b)
      (Set.Ioo 0 1) volume :=
    hnormIoo.congr_fun
      (fun t ht => (beta_complex_integrand a b t ht.1 ht.2).2)
      measurableSet_Ioo
  have hind : Integrable
      ((Set.Ioo (0 : ℝ) 1).indicator (betaRealDensity a b)) volume :=
    hdensityIoo.integrable_indicator measurableSet_Ioo
  have heq : (Set.Ioo (0 : ℝ) 1).indicator (betaRealDensity a b) =
      betaRealDensity a b := by
    funext t
    by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
    · exact Set.indicator_of_mem ht _
    · rw [Set.indicator_of_notMem ht]
      change ¬(0 < t ∧ t < 1) at ht
      rw [betaRealDensity, if_neg ht]
  have hglobal : Integrable (betaRealDensity a b) volume := by
    rwa [heq] at hind
  exact ⟨hglobal, hglobal.integrableOn⟩

-- lem:beta-integral-value: Problem1.beta_integral_value
theorem beta_integral_value (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ, betaRealDensity a b t ∂volume) = ProbabilityTheory.beta a b := by
  have hcomplexIoc : IntegrableOn (betaComplexIntegrand a b)
      (Set.Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (beta_complex_intervalIntegrable a b ha hb)
  have hcomplexIoo : IntegrableOn (betaComplexIntegrand a b)
      (Set.Ioo 0 1) volume :=
    hcomplexIoc.mono_set Set.Ioo_subset_Ioc_self
  have hcomplexValue :
      (∫ t in Set.Ioo (0 : ℝ) 1, betaComplexIntegrand a b t ∂volume) =
        Complex.betaIntegral (a : ℂ) (b : ℂ) := by
    rw [Complex.betaIntegral,
      intervalIntegral.integral_of_le (by norm_num),
      integral_Ioc_eq_integral_Ioo]
    simp only [betaComplexIntegrand, Complex.ofReal_sub, Complex.ofReal_one]
  calc
    (∫ t : ℝ, betaRealDensity a b t ∂volume) =
        ∫ t in Set.Ioo (0 : ℝ) 1, betaRealDensity a b t ∂volume := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      change ¬(0 < t ∧ t < 1) at ht
      rw [betaRealDensity, if_neg ht]
    _ = ∫ t in Set.Ioo (0 : ℝ) 1,
        (betaComplexIntegrand a b t).re ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      change betaRealDensity a b t = (betaComplexIntegrand a b t).re
      rw [(beta_complex_integrand a b t ht.1 ht.2).1, Complex.ofReal_re]
    _ = (∫ t in Set.Ioo (0 : ℝ) 1,
        betaComplexIntegrand a b t ∂volume).re := by
      simpa only [RCLike.re_to_complex] using (integral_re hcomplexIoo)
    _ = (Complex.betaIntegral (a : ℂ) (b : ℂ)).re :=
      congrArg Complex.re hcomplexValue
    _ = ProbabilityTheory.beta a b :=
      (ProbabilityTheory.beta_eq_betaIntegralReal a b ha hb).symm

-- lem:beta-real-bridge: Problem1.beta_real_bridge
theorem beta_real_bridge (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Measurable (betaRealDensity a b) ∧ Integrable (betaRealDensity a b) volume ∧
    (∫ t : ℝ, betaRealDensity a b t ∂volume) = intervalIntegral (fun t : ℝ => Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1)) 0 1 volume ∧
    intervalIntegral (fun t : ℝ => Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1)) 0 1 volume = ProbabilityTheory.beta a b := by
  have hsupport : Function.support (betaRealDensity a b) ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro t ht
    by_cases ht01 : 0 < t ∧ t < 1
    · exact ⟨ht01.1, ht01.2.le⟩
    · have hz : betaRealDensity a b t = 0 := by
        rw [betaRealDensity, if_neg ht01]
      exact False.elim (ht hz)
  have hglobal : (∫ t : ℝ, betaRealDensity a b t ∂volume) =
      intervalIntegral (betaRealDensity a b) 0 1 volume :=
    (intervalIntegral.integral_eq_integral_of_support_subset hsupport).symm
  have hraw : intervalIntegral (betaRealDensity a b) 0 1 volume =
      intervalIntegral (fun t : ℝ =>
        Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1)) 0 1 volume := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    change betaRealDensity a b t = Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1)
    change 0 < t ∧ t < 1 at ht
    rw [betaRealDensity, if_pos ht]
  have hbridge := hglobal.trans hraw
  exact ⟨beta_measurable a b, (beta_integrable a b ha hb).1,
    hbridge, hbridge.symm.trans (beta_integral_value a b ha hb)⟩

-- lem:beta-real-bridge: Problem1.beta_interval_integral_endpoint_values
theorem beta_interval_integral_endpoint_values (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    intervalIntegral (fun t : ℝ => if t = 0 then u else if t = 1 then v else Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1)) 0 1 volume = ProbabilityTheory.beta a b := by
  calc
    _ = intervalIntegral (fun t : ℝ =>
        Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1)) 0 1 volume := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      simp only [if_neg ht.1.ne', if_neg ht.2.ne]
    _ = ProbabilityTheory.beta a b := (beta_real_bridge a b ha hb).2.2.2

-- lem:beta-positive: Problem1.beta_positive
theorem beta_positive (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < ProbabilityTheory.beta a b := by
  exact ProbabilityTheory.beta_pos ha hb

-- lem:beta-symmetry: Problem1.beta_symmetry
theorem beta_symmetry (a b : ℝ) :
    ProbabilityTheory.beta a b = ProbabilityTheory.beta b a := by
  simp [ProbabilityTheory.beta, add_comm, mul_comm]

-- lem:beta-recurrence-left: Problem1.beta_recurrence_left
theorem beta_recurrence_left (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ProbabilityTheory.beta (a + 1) b = a / (a + b) * ProbabilityTheory.beta a b := by
  change Real.Gamma (a + 1) * Real.Gamma b /
      Real.Gamma ((a + 1) + b) =
    (a / (a + b)) *
      (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b))
  rw [Real.Gamma_add_one ha.ne',
    show (a + 1) + b = (a + b) + 1 by ring,
    Real.Gamma_add_one (add_pos ha hb).ne']
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have hGab : Real.Gamma (a + b) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  field_simp [hab, hGab] <;> ring

-- lem:beta-recurrence-right: Problem1.beta_recurrence_right
theorem beta_recurrence_right (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ProbabilityTheory.beta a (b + 1) = b / (a + b) * ProbabilityTheory.beta a b := by
  rw [beta_symmetry a (b + 1), beta_recurrence_left b a hb ha,
    beta_symmetry b a, add_comm b a]

-- lem:beta-ratios: Problem1.beta_ratios
theorem beta_ratios (a b : ℝ) (k : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ProbabilityTheory.beta (a + (k : ℝ)) b / ProbabilityTheory.beta a b = pochhammer a k / pochhammer (a + b) k ∧
    ProbabilityTheory.beta a (b + (k : ℝ)) / ProbabilityTheory.beta a b = pochhammer b k / pochhammer (a + b) k := by
  have hbase : ProbabilityTheory.beta a b ≠ 0 :=
    (beta_positive a b ha hb).ne'
  have hstep (x : ℝ) (m : ℕ) :
      pochhammer x (m + 1) = pochhammer x m * (x + (m : ℝ)) := by
    rw [pochhammer_add x m 1]
    simp [pochhammer]
  induction k with
  | zero =>
      simp [pochhammer_zero, hbase]
  | succ k ih =>
      have hak : 0 < a + (k : ℝ) :=
        add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg k)
      have hbk : 0 < b + (k : ℝ) :=
        add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg k)
      have habk : a + b + (k : ℝ) ≠ 0 :=
        (add_pos_of_pos_of_nonneg (add_pos ha hb) (Nat.cast_nonneg k)).ne'
      have hp : pochhammer (a + b) k ≠ 0 :=
        (pochhammer_positive (a + b) k (add_pos ha hb)).ne'
      constructor
      · rw [Nat.cast_succ, ← add_assoc,
          beta_recurrence_left (a + (k : ℝ)) b hak hb,
          mul_div_assoc, ih.1,
          show (a + (k : ℝ)) + b = (a + b) + (k : ℝ) by ring,
          hstep a k, hstep (a + b) k]
        field_simp [hp, habk] <;> ring
      · rw [Nat.cast_succ, ← add_assoc,
          beta_recurrence_right a (b + (k : ℝ)) ha hbk,
          mul_div_assoc, ih.2,
          show a + (b + (k : ℝ)) = (a + b) + (k : ℝ) by ring,
          hstep b k, hstep (a + b) k]
        field_simp [hp, habk] <;> ring

-- lem:pochhammer-gamma: Problem1.pochhammer_gamma
theorem pochhammer_gamma (a : ℝ) (k : ℕ) (ha : 0 < a) :
    pochhammer a k = Real.Gamma (a + (k : ℝ)) / Real.Gamma a := by
  have hmul : Real.Gamma (a + (k : ℝ)) =
      Real.Gamma a * pochhammer a k := by
    induction k with
    | zero =>
        simp [pochhammer]
    | succ k ih =>
        rw [Nat.cast_succ, ← add_assoc,
          Real.Gamma_add_one (by positivity : a + (k : ℝ) ≠ 0), ih]
        simp only [pochhammer, Finset.prod_range_succ]
        ring
  symm
  rw [hmul]
  exact mul_div_cancel_left₀ _ (Real.Gamma_pos_of_pos ha).ne'

-- lem:beta-monomial: Problem1.beta_monomial_density
theorem beta_monomial_density (a b : ℝ) (k : ℕ) (t : ℝ) :
    t ^ k * betaRealDensity a b t = betaRealDensity (a + (k : ℝ)) b t ∧ (1 - t) ^ k * betaRealDensity a b t = betaRealDensity a (b + (k : ℝ)) t := by
  by_cases ht : 0 < t ∧ t < 1
  · have ht0 : t ≠ 0 := ne_of_gt ht.1
    have h1t0 : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
    have haShift : a + (k : ℝ) - 1 = (a - 1) + (k : ℝ) := by ring
    have hbShift : b + (k : ℝ) - 1 = (b - 1) + (k : ℝ) := by ring
    constructor
    · simp only [betaRealDensity, if_pos ht, haShift, Real.rpow_eq_pow,
        Real.rpow_add_natCast ht0 (a - 1) k]
      ring
    · simp only [betaRealDensity, if_pos ht, hbShift, Real.rpow_eq_pow,
        Real.rpow_add_natCast h1t0 (b - 1) k]
      ring
  · simp [betaRealDensity, ht]

-- lem:beta-monomial: Problem1.beta_monomial
theorem beta_monomial (a b : ℝ) (k : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun t : ℝ => t ^ k * betaRealDensity a b t) volume ∧
    (∫ t : ℝ, t ^ k * betaRealDensity a b t ∂volume) = ProbabilityTheory.beta (a + (k : ℝ)) b ∧
    Integrable (fun t : ℝ => (1 - t) ^ k * betaRealDensity a b t) volume ∧
    (∫ t : ℝ, (1 - t) ^ k * betaRealDensity a b t ∂volume) = ProbabilityTheory.beta a (b + (k : ℝ)) := by
  have hak : 0 < a + (k : ℝ) :=
    add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg k)
  have hbk : 0 < b + (k : ℝ) :=
    add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg k)
  have hleft : (fun t : ℝ => t ^ k * betaRealDensity a b t) =ᵐ[volume]
      betaRealDensity (a + (k : ℝ)) b :=
    Filter.Eventually.of_forall fun t => (beta_monomial_density a b k t).1
  have hright : (fun t : ℝ => (1 - t) ^ k * betaRealDensity a b t) =ᵐ[volume]
      betaRealDensity a (b + (k : ℝ)) :=
    Filter.Eventually.of_forall fun t => (beta_monomial_density a b k t).2
  exact ⟨
    (beta_integrable (a + (k : ℝ)) b hak hb).1.congr hleft.symm,
    (integral_congr_ae hleft).trans
      (beta_integral_value (a + (k : ℝ)) b hak hb),
    (beta_integrable a (b + (k : ℝ)) ha hbk).1.congr hright.symm,
    (integral_congr_ae hright).trans
      (beta_integral_value a (b + (k : ℝ)) ha hbk)⟩

-- lem:beta-basic: Problem1.beta_basic
theorem beta_basic :
    (∀ (a b : ℝ), 0 < a → 0 < b →
      Measurable (betaRealDensity a b) ∧ Integrable (betaRealDensity a b) volume ∧
      (∫ t : ℝ, betaRealDensity a b t ∂volume) = intervalIntegral (fun t : ℝ => Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1)) 0 1 volume ∧
      intervalIntegral (fun t : ℝ => Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1)) 0 1 volume = ProbabilityTheory.beta a b) ∧
    (∀ a b : ℝ, 0 < a → 0 < b → 0 < ProbabilityTheory.beta a b) ∧
    (∀ a b : ℝ, ProbabilityTheory.beta a b = ProbabilityTheory.beta b a) ∧
    (∀ a b : ℝ, 0 < a → 0 < b → ProbabilityTheory.beta (a + 1) b = a / (a + b) * ProbabilityTheory.beta a b) ∧
    (∀ a b : ℝ, 0 < a → 0 < b → ProbabilityTheory.beta a (b + 1) = b / (a + b) * ProbabilityTheory.beta a b) ∧
    (∀ (a b : ℝ) (k : ℕ), 0 < a → 0 < b →
      ProbabilityTheory.beta (a + (k : ℝ)) b / ProbabilityTheory.beta a b = pochhammer a k / pochhammer (a + b) k ∧
      ProbabilityTheory.beta a (b + (k : ℝ)) / ProbabilityTheory.beta a b = pochhammer b k / pochhammer (a + b) k) := by
  exact ⟨beta_real_bridge, beta_positive, beta_symmetry,
    beta_recurrence_left, beta_recurrence_right, beta_ratios⟩

-- lem:chu-cleared-library: Problem1.chuVandermonde_cleared
theorem chuVandermonde_cleared (n : ℕ) (A C : ℝ) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) * pochhammer A k * pochhammer (C + (k : ℝ)) (n - k)) = pochhammer (C - A) n := by
  have hCV :=
    Ring.descPochhammer_smeval_add (R := ℝ) (r := -A)
      (s := C + (n : ℝ) - 1) n (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hCV
  simp only [Nat.succ_eq_add_one] at hCV
  calc
    (∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * (n.choose k : ℝ) * pochhammer A k *
          pochhammer (C + (k : ℝ)) (n - k)) =
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) *
            ((descPochhammer ℤ k).smeval (-A) *
              (descPochhammer ℤ (n - k)).smeval
                (C + (n : ℝ) - 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by
        have hklt : k < n + 1 := Finset.mem_range.mp hk
        omega
      rw [← fallingPochhammer_eq_descPochhammer_int_smeval (-A) k,
        ← fallingPochhammer_eq_descPochhammer_int_smeval
          (C + (n : ℝ) - 1) (n - k),
        (fallingPochhammer_reversal A n k hkn).1,
        (fallingPochhammer_reversal C n k hkn).2]
      ring
    _ = (descPochhammer ℤ n).smeval
        (-A + (C + (n : ℝ) - 1)) := hCV.symm
    _ = pochhammer (C - A) n := by
      rw [← fallingPochhammer_eq_descPochhammer_int_smeval]
      have h :=
        (fallingPochhammer_reversal (C - A) n 0 (Nat.zero_le n)).2
      simp only [Nat.sub_zero, Nat.cast_zero, add_zero] at h
      rw [show -A + (C + (n : ℝ) - 1) =
        (C - A) + (n : ℝ) - 1 by ring]
      exact h

-- lem:chu-denominator-clearing: Problem1.chuVandermonde_denominator_clearing
theorem chuVandermonde_denominator_clearing (n : ℕ) (A C : ℝ) (hC : ∀ k : ℕ, k ≤ n → pochhammer C k ≠ 0) :
    pochhammer C n * (∑ k ∈ Finset.range (n + 1), pochhammer (-(n : ℝ)) k * pochhammer A k / ((k.factorial : ℝ) * pochhammer C k)) = (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) * pochhammer A k * pochhammer (C + (k : ℝ)) (n - k)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    have hklt : k < n + 1 := Finset.mem_range.mp hk
    omega
  have hCk : pochhammer C k ≠ 0 := hC k hkn
  have hkfac : (k.factorial : ℝ) ≠ 0 := by
    positivity
  have hsplit :
      pochhammer C n =
        pochhammer C k * pochhammer (C + (k : ℝ)) (n - k) := by
    simpa [Nat.add_sub_of_le hkn] using pochhammer_add C k (n - k)
  calc
    pochhammer C n *
        (pochhammer (-(n : ℝ)) k * pochhammer A k /
          ((k.factorial : ℝ) * pochhammer C k)) =
        (pochhammer (-(n : ℝ)) k / (k.factorial : ℝ)) *
          pochhammer A k * pochhammer (C + (k : ℝ)) (n - k) := by
      rw [hsplit]
      field_simp [hCk, hkfac] <;> ring
    _ = (-1 : ℝ) ^ k * (n.choose k : ℝ) * pochhammer A k *
        pochhammer (C + (k : ℝ)) (n - k) := by
      rw [pochhammer_neg_nat_div_factorial n k hkn]

-- lem:chu-vandermonde: Problem1.chuVandermonde
theorem chuVandermonde (n : ℕ) (A C : ℝ) (hC : ∀ k : ℕ, k ≤ n → pochhammer C k ≠ 0) :
    (∑ k ∈ Finset.range (n + 1), pochhammer (-(n : ℝ)) k * pochhammer A k / ((k.factorial : ℝ) * pochhammer C k)) = pochhammer (C - A) n / pochhammer C n := by
  apply (eq_div_iff (hC n le_rfl)).2
  exact (mul_comm _ _).trans
    ((chuVandermonde_denominator_clearing n A C hC).trans
      (chuVandermonde_cleared n A C))

-- def:terminating-polynomial: Problem1.terminatingCoeff
noncomputable def terminatingCoeff (n : ℕ) (A C : ℝ) (k : ℕ) : ℝ := by
  classical
  exact (
    pochhammer (-(n : ℝ)) k * pochhammer A k / (pochhammer C k * (k.factorial : ℝ))
  )

-- def:terminating-polynomial: Problem1.terminatingPolynomial
noncomputable def terminatingPolynomial (n : ℕ) (A C : ℝ) : Polynomial ℝ := by
  classical
  exact (
    ∑ k ∈ Finset.range (n + 1), Polynomial.C (terminatingCoeff n A C k) * Polynomial.X ^ k
  )

-- def:terminating-polynomial: Problem1.terminatingPolynomial_eval
theorem terminatingPolynomial_eval (n : ℕ) (A C t : ℝ) :
    (terminatingPolynomial n A C).eval t = ∑ k ∈ Finset.range (n + 1), terminatingCoeff n A C k * t ^ k := by
  simp only [terminatingPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]

-- lem:terminating-degree: Problem1.terminatingPolynomial_coeff
theorem terminatingPolynomial_coeff (n : ℕ) (A C : ℝ) (j : ℕ) :
    (terminatingPolynomial n A C).coeff j = if j ≤ n then terminatingCoeff n A C j else 0 := by
  simp [terminatingPolynomial, Polynomial.finsetSum_coeff, Finset.mem_range]

-- lem:terminating-degree: Problem1.coeff_one_sub_X_pow
theorem coeff_one_sub_X_pow (k j : ℕ) :
    ((1 - Polynomial.X : Polynomial ℝ) ^ k).coeff j = (-1 : ℝ) ^ j * (k.choose j : ℝ) := by
  have hsub : (1 - Polynomial.X : Polynomial ℝ) =
      (1 + Polynomial.X).comp
        (Polynomial.C (-1 : ℝ) * Polynomial.X) := by
    simp [sub_eq_add_neg]
  rw [hsub, ← Polynomial.pow_comp, Polynomial.comp_C_mul_X_coeff,
    Polynomial.coeff_one_add_X_pow]
  exact mul_comm _ _

-- lem:terminating-degree: Problem1.terminatingPolynomial_comp_coeff
theorem terminatingPolynomial_comp_coeff (n : ℕ) (A C : ℝ) (j : ℕ) :
    ((terminatingPolynomial n A C).comp (1 - Polynomial.X : Polynomial ℝ)).coeff j = ∑ k ∈ Finset.range (n + 1), terminatingCoeff n A C k * ((-1 : ℝ) ^ j * (k.choose j : ℝ)) := by
  simp [terminatingPolynomial, coeff_one_sub_X_pow, Polynomial.finsetSum_coeff]

-- lem:terminating-degree: Problem1.terminatingPolynomial_degree_bound
theorem terminatingPolynomial_degree_bound (n : ℕ) (A C : ℝ) (j : ℕ) (hj : n < j) :
    (terminatingPolynomial n A C).coeff j = 0 ∧ ((terminatingPolynomial n A C).comp (1 - Polynomial.X : Polynomial ℝ)).coeff j = 0 := by
  constructor
  · rw [terminatingPolynomial_coeff, if_neg (not_le_of_gt hj)]
  · rw [terminatingPolynomial_comp_coeff]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hkj : k < j := lt_of_le_of_lt hkn hj
    simp [Nat.choose_eq_zero_of_lt hkj]

-- lem:connection-coefficient: Problem1.sum_choose_reindex
theorem sum_choose_reindex (n j : ℕ) (hj : j ≤ n) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 1), f k * (k.choose j : ℝ)) = ∑ r ∈ Finset.range (n - j + 1), f (j + r) * ((j + r).choose j : ℝ) := by
  have hlength : n + 1 = j + (n - j + 1) := by omega
  rw [hlength, Finset.sum_range_add]
  have hzero : (∑ k ∈ Finset.range j, f k * (k.choose j : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k < j := Finset.mem_range.mp hk
    rw [Nat.choose_eq_zero_of_lt hkj, Nat.cast_zero, mul_zero]
  rw [hzero, zero_add]

-- lem:connection-coefficient: Problem1.terminatingCoeff_add
theorem terminatingCoeff_add (n j r : ℕ) (A C : ℝ) (hj : j ≤ n) (hr : r ≤ n - j) (hC : ∀ k : ℕ, k ≤ n → pochhammer C k ≠ 0) :
    terminatingCoeff n A C (j + r) * ((-1 : ℝ) ^ j * ((j + r).choose j : ℝ)) = ((-1 : ℝ) ^ j * terminatingCoeff n A C j) * terminatingCoeff (n - j) (A + (j : ℝ)) (C + (j : ℝ)) r := by
  have hneg : pochhammer (-(n : ℝ)) (j + r) =
      pochhammer (-(n : ℝ)) j * pochhammer (-((n - j : ℕ) : ℝ)) r := by
    rw [pochhammer_add]
    congr 2
    rw [Nat.cast_sub hj]
    ring
  have hA : pochhammer A (j + r) =
      pochhammer A j * pochhammer (A + (j : ℝ)) r := pochhammer_add A j r
  have hCsplit : pochhammer C (j + r) =
      pochhammer C j * pochhammer (C + (j : ℝ)) r := pochhammer_add C j r
  have hCj : pochhammer C j ≠ 0 := hC j hj
  have hjr : j + r ≤ n := by omega
  have hCshift : pochhammer (C + (j : ℝ)) r ≠ 0 :=
    pochhammer_shift_ne_zero C n j r hC hjr
  have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
  have hrfac : (r.factorial : ℝ) ≠ 0 := by positivity
  have hjrfac : ((j + r).factorial : ℝ) ≠ 0 := by positivity
  have hchoose : ((j + r).choose j : ℝ) =
      ((j + r).factorial : ℝ) / ((j.factorial : ℝ) * (r.factorial : ℝ)) := by
    calc
      ((j + r).choose j : ℝ) =
          (((j + r).choose j : ℝ) / ((j + r).factorial : ℝ)) *
            ((j + r).factorial : ℝ) := (div_mul_cancel₀ _ hjrfac).symm
      _ = ((j + r).factorial : ℝ) / ((j.factorial : ℝ) * (r.factorial : ℝ)) := by
        rw [choose_add_div_factorial j r]
        ring
  unfold terminatingCoeff
  rw [hneg, hA, hCsplit, hchoose]
  field_simp [hCj, hCshift, hjfac, hrfac, hjrfac] <;> ring

-- lem:connection-coefficient: Problem1.connection_coefficient
theorem connection_coefficient (n : ℕ) (A C : ℝ) (hC : ∀ k : ℕ, k ≤ n → pochhammer C k ≠ 0) (j : ℕ) (hj : j ≤ n) :
    ((terminatingPolynomial n A C).comp (1 - Polynomial.X : Polynomial ℝ)).coeff j =
      ((-1 : ℝ) ^ j * pochhammer (-(n : ℝ)) j * pochhammer A j / (pochhammer C j * (j.factorial : ℝ))) *
      (∑ r ∈ Finset.range (n - j + 1), pochhammer (-((n - j : ℕ) : ℝ)) r * pochhammer (A + (j : ℝ)) r / (pochhammer (C + (j : ℝ)) r * (r.factorial : ℝ))) := by
  rw [terminatingPolynomial_comp_coeff]
  calc
    (∑ k ∈ Finset.range (n + 1),
        terminatingCoeff n A C k * ((-1 : ℝ) ^ j * (k.choose j : ℝ))) =
        ∑ k ∈ Finset.range (n + 1),
          ((-1 : ℝ) ^ j * terminatingCoeff n A C k) * (k.choose j : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ r ∈ Finset.range (n - j + 1),
          ((-1 : ℝ) ^ j * terminatingCoeff n A C (j + r)) *
            ((j + r).choose j : ℝ) :=
      sum_choose_reindex n j hj (fun k => (-1 : ℝ) ^ j * terminatingCoeff n A C k)
    _ = ∑ r ∈ Finset.range (n - j + 1),
          ((-1 : ℝ) ^ j * terminatingCoeff n A C j) *
            terminatingCoeff (n - j) (A + (j : ℝ)) (C + (j : ℝ)) r := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrle : r ≤ n - j := by
        have hrlt : r < n - j + 1 := Finset.mem_range.mp hr
        omega
      calc
        ((-1 : ℝ) ^ j * terminatingCoeff n A C (j + r)) *
            ((j + r).choose j : ℝ) =
            terminatingCoeff n A C (j + r) *
              ((-1 : ℝ) ^ j * ((j + r).choose j : ℝ)) := by ring
        _ = ((-1 : ℝ) ^ j * terminatingCoeff n A C j) *
            terminatingCoeff (n - j) (A + (j : ℝ)) (C + (j : ℝ)) r :=
          terminatingCoeff_add n j r A C hj hrle hC
    _ = ((-1 : ℝ) ^ j * terminatingCoeff n A C j) *
          (∑ r ∈ Finset.range (n - j + 1),
            terminatingCoeff (n - j) (A + (j : ℝ)) (C + (j : ℝ)) r) := by
      rw [Finset.mul_sum]
    _ = ((-1 : ℝ) ^ j * pochhammer (-(n : ℝ)) j * pochhammer A j /
          (pochhammer C j * (j.factorial : ℝ))) *
          (∑ r ∈ Finset.range (n - j + 1),
            pochhammer (-((n - j : ℕ) : ℝ)) r *
              pochhammer (A + (j : ℝ)) r /
              (pochhammer (C + (j : ℝ)) r * (r.factorial : ℝ))) := by
      unfold terminatingCoeff
      ring

-- lem:connection-coefficient-summed: Problem1.connection_coefficient_summed
theorem connection_coefficient_summed (n : ℕ) (A C : ℝ) (hC : ∀ k : ℕ, k ≤ n → pochhammer C k ≠ 0) (j : ℕ) (hj : j ≤ n) :
    ((terminatingPolynomial n A C).comp (1 - Polynomial.X : Polynomial ℝ)).coeff j =
      (-1 : ℝ) ^ j * pochhammer (-(n : ℝ)) j * pochhammer A j * pochhammer (C - A) (n - j) / (pochhammer C n * (j.factorial : ℝ)) := by
  have hCshift : ∀ r : ℕ, r ≤ n - j → pochhammer (C + (j : ℝ)) r ≠ 0 := by
    intro r hr
    exact pochhammer_shift_ne_zero C n j r hC (by omega)
  have harg : (C + (j : ℝ)) - (A + (j : ℝ)) = C - A := by ring
  have hsum :
      (∑ r ∈ Finset.range (n - j + 1),
        pochhammer (-((n - j : ℕ) : ℝ)) r * pochhammer (A + (j : ℝ)) r /
          (pochhammer (C + (j : ℝ)) r * (r.factorial : ℝ))) =
        pochhammer (C - A) (n - j) / pochhammer (C + (j : ℝ)) (n - j) := by
    simpa only [harg, mul_comm] using
      chuVandermonde (n - j) (A + (j : ℝ)) (C + (j : ℝ)) hCshift
  have hCsplit : pochhammer C n =
      pochhammer C j * pochhammer (C + (j : ℝ)) (n - j) := by
    simpa only [Nat.add_sub_of_le hj] using pochhammer_add C j (n - j)
  rw [connection_coefficient n A C hC j hj, hsum, hCsplit, div_mul_div_comm]
  congr 1 <;> ring

-- lem:connection-reversal-quotient: Problem1.connection_reversal_quotient
theorem connection_reversal_quotient (n j : ℕ) (hj : j ≤ n) (A C : ℝ) (hHj : pochhammer (A + 1 - C - (n : ℝ)) j ≠ 0) :
    (-1 : ℝ) ^ j * pochhammer (C - A) (n - j) = pochhammer (C - A) n / pochhammer (A + 1 - C - (n : ℝ)) j := by
  have harg : 1 - (C - A) - (n : ℝ) = A + 1 - C - (n : ℝ) := by ring
  have hshift : C - A + (n : ℝ) - (j : ℝ) = C - A + ((n - j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hj]
    ring
  have hreverse : pochhammer (A + 1 - C - (n : ℝ)) j =
      (-1 : ℝ) ^ j * pochhammer (C - A + ((n - j : ℕ) : ℝ)) j := by
    simpa only [harg, hshift] using pochhammer_reverse_prefix (C - A) n j hj
  have hsplit : pochhammer (C - A) n =
      pochhammer (C - A) (n - j) * pochhammer (C - A + ((n - j : ℕ) : ℝ)) j := by
    simpa only [Nat.sub_add_cancel hj] using pochhammer_add (C - A) (n - j) j
  have hsign : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  apply (eq_div_iff hHj).2
  rw [hreverse, hsplit]
  calc
    _ = ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) *
        (pochhammer (C - A) (n - j) *
          pochhammer (C - A + ((n - j : ℕ) : ℝ)) j) := by ring
    _ = _ := by rw [hsign, one_mul]

-- lem:connection: Problem1.terminating_connection_polynomial
theorem terminating_connection_polynomial (n : ℕ) (A C : ℝ) (hC : ∀ k : ℕ, k ≤ n → pochhammer C k ≠ 0) (hH : ∀ k : ℕ, k ≤ n → pochhammer (A + 1 - C - (n : ℝ)) k ≠ 0) :
    (terminatingPolynomial n A C).comp (1 - Polynomial.X : Polynomial ℝ) = Polynomial.C (pochhammer (C - A) n / pochhammer C n) * terminatingPolynomial n A (A + 1 - C - (n : ℝ)) := by
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ n
  · have hquot := connection_reversal_quotient n j hj A C (hH j hj)
    rw [connection_coefficient_summed n A C hC j hj,
      Polynomial.coeff_C_mul, terminatingPolynomial_coeff, if_pos hj, terminatingCoeff]
    calc
      _ = (pochhammer (-(n : ℝ)) j * pochhammer A j) *
          ((-1 : ℝ) ^ j * pochhammer (C - A) (n - j)) /
          (pochhammer C n * (j.factorial : ℝ)) := by congr 1 <;> ring
      _ = (pochhammer (-(n : ℝ)) j * pochhammer A j) *
          (pochhammer (C - A) n / pochhammer (A + 1 - C - (n : ℝ)) j) /
          (pochhammer C n * (j.factorial : ℝ)) := by rw [hquot]
      _ = _ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  · have hnj : n < j := Nat.lt_of_not_ge hj
    rw [(terminatingPolynomial_degree_bound n A C j hnj).2,
      Polynomial.coeff_C_mul, terminatingPolynomial_coeff, if_neg hj, mul_zero]

-- lem:connection: Problem1.terminatingConnection
theorem terminatingConnection (n : ℕ) (A C : ℝ) (hC : ∀ k : ℕ, k ≤ n → pochhammer C k ≠ 0) (hH : ∀ k : ℕ, k ≤ n → pochhammer (A + 1 - C - (n : ℝ)) k ≠ 0) (t : ℝ) :
    (terminatingPolynomial n A C).eval t = (pochhammer (C - A) n / pochhammer C n) * (terminatingPolynomial n A (A + 1 - C - (n : ℝ))).eval (1 - t) := by
  have heval := congrArg (Polynomial.eval (1 - t))
    (terminating_connection_polynomial n A C hC hH)
  have hsub : (1 : ℝ) - (1 - t) = t := by ring
  simpa only [Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_C, hsub] using heval

-- def:saalschuetz-data: Problem1.saalschuetzD
noncomputable def saalschuetzD (n : ℕ) (A B C : ℝ) : ℝ := by
  classical
  exact (
    1 + A + B - C - (n : ℝ)
  )

-- def:saalschuetz-data: Problem1.saalschuetzSum
noncomputable def saalschuetzSum (n : ℕ) (A B C : ℝ) : ℝ := by
  classical
  exact (
    ∑ k ∈ Finset.range (n + 1), pochhammer (-(n : ℝ)) k * pochhammer A k * pochhammer B k / ((k.factorial : ℝ) * pochhammer C k * pochhammer (saalschuetzD n A B C) k)
  )

-- def:saalschuetz-data: Problem1.saalschuetzRegion
noncomputable def saalschuetzRegion (n : ℕ) : Set (Fin 3 → ℝ) := by
  classical
  exact (
    {v | 0 < v 1 ∧ 0 < v 2 ∧ v 2 + (n : ℝ) - 1 < v 0}
  )

-- def:saalschuetz-data: Problem1.saalschuetzQ
noncomputable def saalschuetzQ (n : ℕ) (A B C : ℝ) : ℝ := by
  classical
  exact (
    pochhammer C n * pochhammer (saalschuetzD n A B C) n * pochhammer (C - A - B) n
  )

-- lem:saalschuetz-signs: Problem1.saalschuetz_signs
theorem saalschuetz_signs (n : ℕ) (A B C : ℝ) (hU : ![A, B, C] ∈ saalschuetzRegion n) :
    0 < saalschuetzD n A B C - B ∧ 0 < saalschuetzD n A B C ∧
    (∀ k : ℕ, k ≤ n → 0 < pochhammer C k ∧ 0 < pochhammer (saalschuetzD n A B C) k ∧ 0 < pochhammer (saalschuetzD n A B C - B) k) ∧
    pochhammer (C - A - B) n ≠ 0 := by
  have hregion : 0 < B ∧ 0 < C ∧ C + (n : ℝ) - 1 < A := by
    simpa [saalschuetzRegion] using hU
  have hDB : 0 < saalschuetzD n A B C - B := by
    dsimp [saalschuetzD]
    linarith [hregion.2.2]
  have hD : 0 < saalschuetzD n A B C := by linarith [hregion.1]
  refine ⟨hDB, hD, ?_, ?_⟩
  · intro k _hk
    exact ⟨pochhammer_positive C k hregion.2.1,
      pochhammer_positive _ k hD, pochhammer_positive _ k hDB⟩
  · unfold pochhammer
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hjn : j + 1 ≤ n := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
    have hjnR : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hjn
    have hnegative : C - A - B + (j : ℝ) < 0 := by
      linarith [hregion.1, hregion.2.2]
    exact ne_of_lt hnegative

-- lem:saalschuetz-integral: Problem1.saalschuetz_integral
theorem saalschuetz_integral (n : ℕ) (A B C : ℝ) (hU : ![A, B, C] ∈ saalschuetzRegion n) :
    Integrable (fun t : ℝ => betaRealDensity B (saalschuetzD n A B C - B) t * (terminatingPolynomial n A C).eval t) volume ∧
    saalschuetzSum n A B C = (1 / ProbabilityTheory.beta B (saalschuetzD n A B C - B)) *
      (∫ t : ℝ, betaRealDensity B (saalschuetzD n A B C - B) t * (terminatingPolynomial n A C).eval t ∂volume) := by
  let D : ℝ := saalschuetzD n A B C
  let E : ℝ := D - B
  let Z : ℝ := ProbabilityTheory.beta B E
  have hregion : 0 < B ∧ 0 < C ∧ C + (n : ℝ) - 1 < A := by
    simpa [saalschuetzRegion] using hU
  have hB : 0 < B := hregion.1
  have hE : 0 < E := (saalschuetz_signs n A B C hU).1
  have hBE : B + E = D := by dsimp [E]; ring
  let f : ℕ → ℝ → ℝ := fun k t =>
    terminatingCoeff n A C k * (t ^ k * betaRealDensity B E t)
  have hf (k : ℕ) : Integrable (f k) volume :=
    (beta_monomial B E k hB hE).1.const_mul (terminatingCoeff n A C k)
  have hfun : (fun t : ℝ =>
      betaRealDensity B E t * (terminatingPolynomial n A C).eval t) =
      (fun t : ℝ => ∑ k ∈ Finset.range (n + 1), f k t) := by
    funext t
    rw [terminatingPolynomial_eval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    dsimp [f]
    ring
  constructor
  · change Integrable (fun t : ℝ =>
      betaRealDensity B E t * (terminatingPolynomial n A C).eval t) volume
    rw [hfun]
    exact integrable_finsetSum _ (fun k _hk => hf k)
  · change saalschuetzSum n A B C = (1 / Z) *
      (∫ t : ℝ, betaRealDensity B E t *
        (terminatingPolynomial n A C).eval t ∂volume)
    rw [hfun, integral_finsetSum _ (fun k _hk => hf k), Finset.mul_sum]
    change (∑ k ∈ Finset.range (n + 1),
      pochhammer (-(n : ℝ)) k * pochhammer A k * pochhammer B k /
        ((k.factorial : ℝ) * pochhammer C k * pochhammer D k)) =
      ∑ k ∈ Finset.range (n + 1), (1 / Z) * (∫ t : ℝ, f k t ∂volume)
    apply Finset.sum_congr rfl
    intro k _hk
    have hvalue : (∫ t : ℝ, f k t ∂volume) =
        terminatingCoeff n A C k * ProbabilityTheory.beta (B + (k : ℝ)) E := by
      dsimp only [f]
      rw [integral_const_mul, (beta_monomial B E k hB hE).2.1]
    have hratio : ProbabilityTheory.beta (B + (k : ℝ)) E / Z =
        pochhammer B k / pochhammer D k := by
      simpa only [hBE] using (beta_ratios B E k hB hE).1
    rw [hvalue]
    calc
      pochhammer (-(n : ℝ)) k * pochhammer A k * pochhammer B k /
          ((k.factorial : ℝ) * pochhammer C k * pochhammer D k) =
          terminatingCoeff n A C k * (pochhammer B k / pochhammer D k) := by
        simp only [terminatingCoeff, div_eq_mul_inv, mul_inv_rev]
        ring
      _ = terminatingCoeff n A C k *
          (ProbabilityTheory.beta (B + (k : ℝ)) E / Z) := by rw [hratio]
      _ = (1 / Z) *
          (terminatingCoeff n A C k * ProbabilityTheory.beta (B + (k : ℝ)) E) := by
        simp only [div_eq_mul_inv]
        ring

-- lem:saalschuetz-after-connection: Problem1.saalschuetz_after_connection
theorem saalschuetz_after_connection (n : ℕ) (A B C : ℝ) (hU : ![A, B, C] ∈ saalschuetzRegion n) :
    saalschuetzSum n A B C = (pochhammer (C - A) n / pochhammer C n) * (pochhammer (saalschuetzD n A B C - A) n / pochhammer (saalschuetzD n A B C) n) := by
  let D : ℝ := saalschuetzD n A B C
  let E : ℝ := D - B
  let Z : ℝ := ProbabilityTheory.beta B E
  let L : ℝ := pochhammer (C - A) n / pochhammer C n
  have hregion : 0 < B ∧ 0 < C ∧ C + (n : ℝ) - 1 < A := by
    simpa [saalschuetzRegion] using hU
  have hB : 0 < B := hregion.1
  have hsign := saalschuetz_signs n A B C hU
  have hEpos : 0 < E := hsign.1
  have hCden : ∀ k : ℕ, k ≤ n → pochhammer C k ≠ 0 := by
    intro k hk
    exact ne_of_gt (hsign.2.2.1 k hk).1
  have hDden : ∀ k : ℕ, k ≤ n → pochhammer D k ≠ 0 := by
    intro k hk
    exact ne_of_gt (hsign.2.2.1 k hk).2.1
  have hEden : ∀ k : ℕ, k ≤ n → pochhammer E k ≠ 0 := by
    intro k hk
    exact ne_of_gt (hsign.2.2.1 k hk).2.2
  have hBE : B + E = D := by dsimp [E]; ring
  have hHE : A + 1 - C - (n : ℝ) = E := by
    dsimp [E, D, saalschuetzD]
    ring
  have hHden : ∀ k : ℕ, k ≤ n →
      pochhammer (A + 1 - C - (n : ℝ)) k ≠ 0 := by
    intro k hk
    rw [hHE]
    exact hEden k hk
  have hconn (t : ℝ) : (terminatingPolynomial n A C).eval t =
      L * (terminatingPolynomial n A E).eval (1 - t) := by
    simpa only [hHE] using (terminatingConnection n A C hCden hHden t)
  let f : ℕ → ℝ → ℝ := fun k t =>
    terminatingCoeff n A E k * ((1 - t) ^ k * betaRealDensity B E t)
  have hf (k : ℕ) : Integrable (f k) volume :=
    (beta_monomial B E k hB hEpos).2.2.1.const_mul (terminatingCoeff n A E k)
  have hfun : (fun t : ℝ =>
      betaRealDensity B E t * (terminatingPolynomial n A C).eval t) =
      (fun t : ℝ => L * (∑ k ∈ Finset.range (n + 1), f k t)) := by
    funext t
    rw [hconn t, terminatingPolynomial_eval]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    dsimp [f]
    ring
  have hsum : (1 / Z) *
      (∫ t : ℝ, ∑ k ∈ Finset.range (n + 1), f k t ∂volume) =
      pochhammer (D - A) n / pochhammer D n := by
    rw [integral_finsetSum _ (fun k _hk => hf k), Finset.mul_sum]
    calc
      (∑ k ∈ Finset.range (n + 1), (1 / Z) * (∫ t : ℝ, f k t ∂volume)) =
          ∑ k ∈ Finset.range (n + 1),
            pochhammer (-(n : ℝ)) k * pochhammer A k /
              ((k.factorial : ℝ) * pochhammer D k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hEk : pochhammer E k ≠ 0 := hEden k hkn
        have hDk : pochhammer D k ≠ 0 := hDden k hkn
        have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
        have hvalue : (∫ t : ℝ, f k t ∂volume) =
            terminatingCoeff n A E k * ProbabilityTheory.beta B (E + (k : ℝ)) := by
          dsimp only [f]
          rw [integral_const_mul, (beta_monomial B E k hB hEpos).2.2.2]
        have hratio : ProbabilityTheory.beta B (E + (k : ℝ)) / Z =
            pochhammer E k / pochhammer D k := by
          simpa only [hBE] using (beta_ratios B E k hB hEpos).2
        rw [hvalue]
        calc
          (1 / Z) *
              (terminatingCoeff n A E k * ProbabilityTheory.beta B (E + (k : ℝ))) =
              terminatingCoeff n A E k *
                (ProbabilityTheory.beta B (E + (k : ℝ)) / Z) := by
            simp only [div_eq_mul_inv]
            ring
          _ = terminatingCoeff n A E k * (pochhammer E k / pochhammer D k) := by
            rw [hratio]
          _ = pochhammer (-(n : ℝ)) k * pochhammer A k /
              ((k.factorial : ℝ) * pochhammer D k) := by
            dsimp only [terminatingCoeff]
            field_simp [hEk, hDk, hkfac] <;> ring
      _ = pochhammer (D - A) n / pochhammer D n :=
        chuVandermonde n A D hDden
  have hrep : saalschuetzSum n A B C = (1 / Z) *
      (∫ t : ℝ, betaRealDensity B E t *
        (terminatingPolynomial n A C).eval t ∂volume) :=
    (saalschuetz_integral n A B C hU).2
  rw [hfun, integral_const_mul] at hrep
  calc
    saalschuetzSum n A B C = (1 / Z) *
        (L * (∫ t : ℝ, ∑ k ∈ Finset.range (n + 1), f k t ∂volume)) := hrep
    _ = L * ((1 / Z) *
        (∫ t : ℝ, ∑ k ∈ Finset.range (n + 1), f k t ∂volume)) := by ring
    _ = L * (pochhammer (D - A) n / pochhammer D n) := by rw [hsum]

-- lem:saalschuetz-positive: Problem1.saalschuetz_positive
theorem saalschuetz_positive (n : ℕ) (A B C : ℝ) (hU : ![A, B, C] ∈ saalschuetzRegion n) :
    saalschuetzSum n A B C = pochhammer (C - A) n * pochhammer (C - B) n / (pochhammer C n * pochhammer (C - A - B) n) := by
  have hargDA : 1 - (C - B) - (n : ℝ) = saalschuetzD n A B C - A := by
    unfold saalschuetzD
    ring
  have hDA : pochhammer (saalschuetzD n A B C - A) n =
      (-1 : ℝ) ^ n * pochhammer (C - B) n := by
    simpa only [hargDA] using pochhammer_reverse (C - B) n
  have hargD : 1 - (C - A - B) - (n : ℝ) = saalschuetzD n A B C := by
    unfold saalschuetzD
    ring
  have hDreverse : pochhammer (saalschuetzD n A B C) n =
      (-1 : ℝ) ^ n * pochhammer (C - A - B) n := by
    simpa only [hargD] using pochhammer_reverse (C - A - B) n
  have hsign : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  rw [saalschuetz_after_connection n A B C hU, hDA, hDreverse,
    mul_div_mul_left _ _ hsign, div_mul_div_comm]

-- def:saalschuetz-polynomials: Problem1.polynomialPochhammer3
noncomputable def polynomialPochhammer3 (P : MvPolynomial (Fin 3) ℝ) (k : ℕ) : MvPolynomial (Fin 3) ℝ := by
  classical
  exact (
    ∏ j ∈ Finset.range k, (P + MvPolynomial.C (j : ℝ))
  )

-- def:saalschuetz-polynomials: Problem1.saalschuetzDPolynomial
noncomputable def saalschuetzDPolynomial (n : ℕ) : MvPolynomial (Fin 3) ℝ := by
  classical
  exact (
    1 + MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 2 - MvPolynomial.C (n : ℝ)
  )

-- def:saalschuetz-polynomials: Problem1.saalschuetzLeftPolynomial
noncomputable def saalschuetzLeftPolynomial (n : ℕ) : MvPolynomial (Fin 3) ℝ := by
  classical
  exact (
    ∑ k ∈ Finset.range (n + 1),
        MvPolynomial.C (pochhammer (-(n : ℝ)) k / (k.factorial : ℝ)) *
        polynomialPochhammer3 (MvPolynomial.X 0) k * polynomialPochhammer3 (MvPolynomial.X 1) k *
        polynomialPochhammer3 (MvPolynomial.X 2 + MvPolynomial.C (k : ℝ)) (n - k) *
        polynomialPochhammer3 (saalschuetzDPolynomial n + MvPolynomial.C (k : ℝ)) (n - k) *
        polynomialPochhammer3 (MvPolynomial.X 2 - MvPolynomial.X 0 - MvPolynomial.X 1) n
  )

-- def:saalschuetz-polynomials: Problem1.saalschuetzRightPolynomial
noncomputable def saalschuetzRightPolynomial (n : ℕ) : MvPolynomial (Fin 3) ℝ := by
  classical
  exact (
    polynomialPochhammer3 (MvPolynomial.X 2 - MvPolynomial.X 0) n *
        polynomialPochhammer3 (MvPolynomial.X 2 - MvPolynomial.X 1) n *
        polynomialPochhammer3 (saalschuetzDPolynomial n) n
  )

-- lem:saalschuetz-polynomial-eval: Problem1.polynomialPochhammer3_eval
theorem polynomialPochhammer3_eval (v : Fin 3 → ℝ) (P : MvPolynomial (Fin 3) ℝ) (k : ℕ) :
    MvPolynomial.eval v (polynomialPochhammer3 P k) = pochhammer (MvPolynomial.eval v P) k := by
  simp only [polynomialPochhammer3, pochhammer, MvPolynomial.eval_prod,
    MvPolynomial.eval_add, MvPolynomial.eval_C]

-- lem:saalschuetz-polynomial-eval: Problem1.saalschuetzDPolynomial_eval
theorem saalschuetzDPolynomial_eval (n : ℕ) (A B C : ℝ) :
    MvPolynomial.eval ![A, B, C] (saalschuetzDPolynomial n) = saalschuetzD n A B C := by
  simp [saalschuetzDPolynomial, saalschuetzD]

-- lem:saalschuetz-polynomial-eval: Problem1.saalschuetz_polynomial_eval
theorem saalschuetz_polynomial_eval (n : ℕ) (A B C : ℝ) :
    MvPolynomial.eval ![A, B, C] (saalschuetzLeftPolynomial n) =
      (∑ k ∈ Finset.range (n + 1), (pochhammer (-(n : ℝ)) k * pochhammer A k * pochhammer B k / (k.factorial : ℝ)) *
        pochhammer (C + (k : ℝ)) (n - k) * pochhammer (saalschuetzD n A B C + (k : ℝ)) (n - k) * pochhammer (C - A - B) n) ∧
    MvPolynomial.eval ![A, B, C] (saalschuetzRightPolynomial n) = pochhammer (C - A) n * pochhammer (C - B) n * pochhammer (saalschuetzD n A B C) n := by
  constructor
  · unfold saalschuetzLeftPolynomial
    rw [MvPolynomial.eval_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp [polynomialPochhammer3_eval, saalschuetzDPolynomial_eval,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  · simp [saalschuetzRightPolynomial, polynomialPochhammer3_eval,
      saalschuetzDPolynomial_eval]

-- lem:saalschuetz-clearing: Problem1.saalschuetz_clearing
theorem saalschuetz_clearing (n : ℕ) (A B C : ℝ) (hC : ∀ k : ℕ, k ≤ n → pochhammer C k ≠ 0) (hD : ∀ k : ℕ, k ≤ n → pochhammer (saalschuetzD n A B C) k ≠ 0) (hCAB : pochhammer (C - A - B) n ≠ 0) :
    saalschuetzQ n A B C ≠ 0 ∧
    saalschuetzQ n A B C * saalschuetzSum n A B C = MvPolynomial.eval ![A, B, C] (saalschuetzLeftPolynomial n) ∧
    saalschuetzQ n A B C * (pochhammer (C - A) n * pochhammer (C - B) n / (pochhammer C n * pochhammer (C - A - B) n)) = MvPolynomial.eval ![A, B, C] (saalschuetzRightPolynomial n) := by
  have hCn : pochhammer C n ≠ 0 := hC n le_rfl
  have hDn : pochhammer (saalschuetzD n A B C) n ≠ 0 := hD n le_rfl
  have hleft := (saalschuetz_polynomial_eval n A B C).1
  have hright := (saalschuetz_polynomial_eval n A B C).2
  refine ⟨mul_ne_zero (mul_ne_zero hCn hDn) hCAB, ?_, ?_⟩
  · rw [hleft, saalschuetzQ, saalschuetzSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hCk : pochhammer C k ≠ 0 := hC k hkn
    have hDk : pochhammer (saalschuetzD n A B C) k ≠ 0 := hD k hkn
    have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have hCsplit : pochhammer C n =
        pochhammer C k * pochhammer (C + (k : ℝ)) (n - k) := by
      simpa only [Nat.add_sub_of_le hkn] using pochhammer_add C k (n - k)
    have hDsplit : pochhammer (saalschuetzD n A B C) n =
        pochhammer (saalschuetzD n A B C) k *
          pochhammer (saalschuetzD n A B C + (k : ℝ)) (n - k) := by
      simpa only [Nat.add_sub_of_le hkn] using
        pochhammer_add (saalschuetzD n A B C) k (n - k)
    rw [hCsplit, hDsplit]
    field_simp [hCk, hDk, hkfac] <;> ring
  · rw [hright, saalschuetzQ]
    field_simp [hCn, hCAB] <;> ring

-- lem:saalschuetz-polynomial-identity: Problem1.saalschuetz_polynomial_identity
theorem saalschuetz_polynomial_identity (n : ℕ) :
    saalschuetzLeftPolynomial n = saalschuetzRightPolynomial n := by
  let lower : Fin 3 → ℝ := ![(n : ℝ) + 4, 1, 2]
  let upper : Fin 3 → ℝ := ![(n : ℝ) + 5, 2, 3]
  have hlowerUpper : ∀ i : Fin 3, lower i < upper i := by
    intro i
    fin_cases i <;> norm_num [lower, upper]
  apply polynomial_eq_of_eq_on_open_box 3
    (saalschuetzLeftPolynomial n) (saalschuetzRightPolynomial n)
    lower upper hlowerUpper
  intro x hx
  have hAlower : (n : ℝ) + 4 < x 0 := by
    simpa [lower] using (hx (0 : Fin 3)).1
  have hBlower : (1 : ℝ) < x 1 := by
    simpa [lower] using (hx (1 : Fin 3)).1
  have hClower : (2 : ℝ) < x 2 := by
    simpa [lower] using (hx (2 : Fin 3)).1
  have hCupper : x 2 < (3 : ℝ) := by
    simpa [upper] using (hx (2 : Fin 3)).2
  have hregion : 0 < x 1 ∧ 0 < x 2 ∧ x 2 + (n : ℝ) - 1 < x 0 := by
    exact ⟨by linarith, by linarith, by linarith⟩
  have hU : ![x 0, x 1, x 2] ∈ saalschuetzRegion n := by
    simpa [saalschuetzRegion] using hregion
  have hsign := saalschuetz_signs n (x 0) (x 1) (x 2) hU
  have hCden : ∀ k : ℕ, k ≤ n → pochhammer (x 2) k ≠ 0 := by
    intro k hk
    exact ne_of_gt (hsign.2.2.1 k hk).1
  have hDden : ∀ k : ℕ, k ≤ n →
      pochhammer (saalschuetzD n (x 0) (x 1) (x 2)) k ≠ 0 := by
    intro k hk
    exact ne_of_gt (hsign.2.2.1 k hk).2.1
  have hclear := saalschuetz_clearing n (x 0) (x 1) (x 2)
    hCden hDden hsign.2.2.2
  rw [saalschuetz_positive n (x 0) (x 1) (x 2) hU] at hclear
  have heval := hclear.2.1.symm.trans hclear.2.2
  have hxvec : ![x 0, x 1, x 2] = x := by
    funext i
    fin_cases i <;> rfl
  simpa only [hxvec] using heval

-- lem:saalschuetz: Problem1.pfaffSaalschuetz
theorem pfaffSaalschuetz (n : ℕ) (A B C : ℝ) (hC : ∀ k : ℕ, k ≤ n → pochhammer C k ≠ 0) (hD : ∀ k : ℕ, k ≤ n → pochhammer (saalschuetzD n A B C) k ≠ 0) (hCAB : pochhammer (C - A - B) n ≠ 0) :
    (∑ k ∈ Finset.range (n + 1), pochhammer (-(n : ℝ)) k * pochhammer A k * pochhammer B k / ((k.factorial : ℝ) * pochhammer C k * pochhammer (saalschuetzD n A B C) k)) = pochhammer (C - A) n * pochhammer (C - B) n / (pochhammer C n * pochhammer (C - A - B) n) := by
  have hclear := saalschuetz_clearing n A B C hC hD hCAB
  have heval := congrArg (MvPolynomial.eval ![A, B, C])
    (saalschuetz_polynomial_identity n)
  change saalschuetzSum n A B C =
    pochhammer (C - A) n * pochhammer (C - B) n /
      (pochhammer C n * pochhammer (C - A - B) n)
  exact mul_left_cancel₀ hclear.1
    (hclear.2.1.trans (heval.trans hclear.2.2.symm))

-- lem:orthogonal-group: Problem1.orthogonalN_nonempty
theorem orthogonalN_nonempty (m : ℕ) : Nonempty (OrthogonalN m) := by
  exact ⟨1⟩

-- lem:orthogonal-group: Problem1.orthogonalN_t2Space
theorem orthogonalN_t2Space (m : ℕ) : T2Space (OrthogonalN m) := by
  infer_instance

-- lem:orthogonal-group: Problem1.orthogonalN_isTopologicalGroup
theorem orthogonalN_isTopologicalGroup (m : ℕ) : IsTopologicalGroup (OrthogonalN m) := by
  infer_instance

-- lem:orthogonal-group: Problem1.orthogonalN_coe_one
theorem orthogonalN_coe_one (m : ℕ) : ((1 : OrthogonalN m) : Matrix (Fin m) (Fin m) ℝ) = 1 := by
  rfl

-- lem:orthogonal-group: Problem1.orthogonalN_coe_mul
theorem orthogonalN_coe_mul {m : ℕ} (R T : OrthogonalN m) : ((R * T : OrthogonalN m) : Matrix (Fin m) (Fin m) ℝ) = (R : Matrix (Fin m) (Fin m) ℝ) * (T : Matrix (Fin m) (Fin m) ℝ) := by
  rfl

-- lem:orthogonal-group: Problem1.orthogonalN_coe_inv
theorem orthogonalN_coe_inv {m : ℕ} (R : OrthogonalN m) : ((R⁻¹ : OrthogonalN m) : Matrix (Fin m) (Fin m) ℝ) = (R : Matrix (Fin m) (Fin m) ℝ).transpose := by
  rw [← Unitary.star_eq_inv R, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

-- lem:orthogonal-group: Problem1.orthogonalN_transpose_mul
theorem orthogonalN_transpose_mul {m : ℕ} (R : OrthogonalN m) : (R : Matrix (Fin m) (Fin m) ℝ).transpose * (R : Matrix (Fin m) (Fin m) ℝ) = 1 := by
  exact (Matrix.mem_orthogonalGroup_iff' (n := Fin m) (R := ℝ)).mp R.property

-- lem:orthogonal-group: Problem1.orthogonalN_mul_transpose
theorem orthogonalN_mul_transpose {m : ℕ} (R : OrthogonalN m) : (R : Matrix (Fin m) (Fin m) ℝ) * (R : Matrix (Fin m) (Fin m) ℝ).transpose = 1 := by
  exact (Matrix.mem_orthogonalGroup_iff (n := Fin m) (R := ℝ)).mp R.property

-- lem:orthogonal-closed: Problem1.orthogonalN_isClosed
theorem orthogonalN_isClosed (m : ℕ) : IsClosed (Matrix.orthogonalGroup (Fin m) ℝ : Set (Matrix (Fin m) (Fin m) ℝ)) := by
  exact isClosed_unitary

-- lem:orthogonal-entry-bound: Problem1.orthogonalN_entry_bound
theorem orthogonalN_entry_bound {m : ℕ} (R : OrthogonalN m) (i j : Fin m) : |(R : Matrix (Fin m) (Fin m) ℝ) i j| ≤ (1 : ℝ) := by
  simpa only [Real.norm_eq_abs] using
    (entry_norm_bound_of_unitary
      (U := (R : Matrix (Fin m) (Fin m) ℝ)) R.property i j)

-- lem:orthogonal-compact-transitive: Problem1.orthogonalN_univ_isCompact
theorem orthogonalN_univ_isCompact (m : ℕ) : IsCompact (Set.univ : Set (OrthogonalN m)) := by
  let box : Set (Matrix (Fin m) (Fin m) ℝ) :=
    {A | ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1}
  have hbox : IsCompact box := by
    change IsCompact {A : Fin m → Fin m → ℝ | ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1}
    exact isCompact_pi_infinite (fun _ : Fin m =>
      isCompact_pi_infinite (fun _ : Fin m => isCompact_Icc))
  have hcompact : IsCompact (Matrix.orthogonalGroup (Fin m) ℝ :
      Set (Matrix (Fin m) (Fin m) ℝ)) :=
    hbox.of_isClosed_subset (orthogonalN_isClosed m) (by
      intro A hA
      change ∀ i j : Fin m, A i j ∈ Set.Icc (-1 : ℝ) 1
      intro i j
      exact abs_le.mp (orthogonalN_entry_bound (⟨A, hA⟩ : OrthogonalN m) i j))
  letI : CompactSpace (OrthogonalN m) := isCompact_iff_compactSpace.mp hcompact
  exact isCompact_univ

-- lem:orthogonal-compact-transitive: Problem1.orthogonalNCompactSpace
instance orthogonalNCompactSpace (m : ℕ) : CompactSpace (OrthogonalN m) := by
  exact isCompact_univ_iff.mp (orthogonalN_univ_isCompact m)

-- def:ambient-action: Problem1.orthogonalLin
noncomputable def orthogonalLin {m : ℕ} (R : OrthogonalN m) : EuclideanN m →ₗ[ℝ] EuclideanN m := by
  classical
  exact (
    Matrix.toEuclideanLin (R : Matrix (Fin m) (Fin m) ℝ)
  )

-- def:ambient-action: Problem1.orthogonalLin_apply_coordinate
theorem orthogonalLin_apply_coordinate {m : ℕ} (R : OrthogonalN m) (z : EuclideanN m) (i : Fin m) : orthogonalLin R z i = ∑ j : Fin m, (R : Matrix (Fin m) (Fin m) ℝ) i j * z j := by
  rfl

-- lem:orthogonal-inner: Problem1.orthogonalLin_inner
theorem orthogonalLin_inner {m : ℕ} (R : OrthogonalN m) (z w : EuclideanN m) : inner ℝ (orthogonalLin R z) (orthogonalLin R w) = inner ℝ z w := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change dotProduct
      (Matrix.mulVec (R : Matrix (Fin m) (Fin m) ℝ) (fun i : Fin m => w i))
      (Matrix.mulVec (R : Matrix (Fin m) (Fin m) ℝ) (fun i : Fin m => z i)) =
    dotProduct (fun i : Fin m => w i) (fun i : Fin m => z i)
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    orthogonalN_transpose_mul R, Matrix.vecMul_one]

-- lem:orthogonal-euclidean-norm: Problem1.orthogonalLin_norm
theorem orthogonalLin_norm {m : ℕ} (R : OrthogonalN m) (z : EuclideanN m) : ‖orthogonalLin R z‖ = ‖z‖ := by
  have hsq := orthogonalLin_inner R z z
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

-- cor:orthogonal-unit-sphere-mem: Problem1.orthogonal_unitSphere_mem
theorem orthogonal_unitSphere_mem {m : ℕ} (R : OrthogonalN m) (x : UnitSphereN m) : orthogonalLin R (x : EuclideanN m) ∈ UnitSphereN m := by
  change orthogonalLin R (x : EuclideanN m) ∈ Metric.sphere (0 : EuclideanN m) 1
  rw [Metric.mem_sphere, dist_zero_right, orthogonalLin_norm]
  exact unitSphereN_norm x

-- def:sphere-action-equiv: Problem1.sphereActionN
noncomputable def sphereActionN {m : ℕ} (R : OrthogonalN m) : UnitSphereN m → UnitSphereN m := by
  classical
  exact (
    fun x => ⟨orthogonalLin R (x : EuclideanN m), orthogonal_unitSphere_mem R x⟩
  )

-- def:sphere-action-equiv: Problem1.sphereActionN_coe
theorem sphereActionN_coe {m : ℕ} (R : OrthogonalN m) (x : UnitSphereN m) : (sphereActionN R x : EuclideanN m) = orthogonalLin R (x : EuclideanN m) := by
  rfl

-- def:sphere-action-equiv: Problem1.sphereAction
noncomputable abbrev sphereAction {d : ℕ} (R : Orthogonal d) : Sphere d → Sphere d := by
  classical
  exact (
    sphereActionN R
  )

-- lem:sphere-action-continuous: Problem1.sphereActionN_joint_continuous
theorem sphereActionN_joint_continuous (m : ℕ) : Continuous (fun p : OrthogonalN m × UnitSphereN m => sphereActionN p.1 p.2) := by
  have hR : Continuous (fun p : OrthogonalN m × UnitSphereN m =>
      (p.1 : Matrix (Fin m) (Fin m) ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : OrthogonalN m × UnitSphereN m =>
      WithLp.ofLp (p.2 : EuclideanN m)) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ)).comp
      (continuous_subtype_val.comp continuous_snd)
  have hV : Continuous (fun p : OrthogonalN m × UnitSphereN m =>
      WithLp.toLp 2
        (Matrix.mulVec (p.1 : Matrix (Fin m) (Fin m) ℝ)
          (WithLp.ofLp (p.2 : EuclideanN m)))) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
      (hR.matrix_mulVec hx)
  unfold sphereActionN
  apply Continuous.subtype_mk
  simpa only [orthogonalLin, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hV

-- lem:sphere-action-continuous: Problem1.sphereActionN_continuous
theorem sphereActionN_continuous {m : ℕ} (R : OrthogonalN m) : Continuous (sphereActionN R) := by
  exact (sphereActionN_joint_continuous m).comp
    (continuous_const.prodMk continuous_id)

-- lem:sphere-action-one: Problem1.sphereActionN_one
theorem sphereActionN_one {m : ℕ} (x : UnitSphereN m) : sphereActionN (1 : OrthogonalN m) x = x := by
  apply Subtype.ext
  simp only [sphereActionN_coe, orthogonalLin, orthogonalN_coe_one,
    Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.one_mulVec, WithLp.toLp_ofLp]

-- lem:sphere-action-mul: Problem1.sphereActionN_mul
theorem sphereActionN_mul {m : ℕ} (R T : OrthogonalN m) (x : UnitSphereN m) : sphereActionN (R * T) x = sphereActionN R (sphereActionN T x) := by
  apply Subtype.ext
  simp only [sphereActionN_coe, orthogonalLin, orthogonalN_coe_mul,
    Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, Matrix.mulVec_mulVec]

-- lem:sphere-action-inv: Problem1.sphereActionN_inv_left
theorem sphereActionN_inv_left {m : ℕ} (R : OrthogonalN m) (x : UnitSphereN m) : sphereActionN R⁻¹ (sphereActionN R x) = x := by
  rw [← sphereActionN_mul, inv_mul_cancel, sphereActionN_one]

-- lem:sphere-action-inv: Problem1.sphereActionN_inv_right
theorem sphereActionN_inv_right {m : ℕ} (R : OrthogonalN m) (x : UnitSphereN m) : sphereActionN R (sphereActionN R⁻¹ x) = x := by
  rw [← sphereActionN_mul, mul_inv_cancel, sphereActionN_one]

-- lem:sphere-action-inv: Problem1.sphereActionN_inv
theorem sphereActionN_inv {m : ℕ} (R : OrthogonalN m) (x : UnitSphereN m) : sphereActionN R⁻¹ (sphereActionN R x) = x ∧ sphereActionN R (sphereActionN R⁻¹ x) = x := by
  exact ⟨sphereActionN_inv_left R x, sphereActionN_inv_right R x⟩

-- lem:sphere-action-homeomorph: Problem1.sphereActionEquivN
noncomputable def sphereActionEquivN {m : ℕ} (R : OrthogonalN m) : UnitSphereN m ≃ₜ UnitSphereN m := by
  classical
  exact (
    { toFun := sphereActionN R
      invFun := sphereActionN (R⁻¹)
      left_inv := sphereActionN_inv_left R
      right_inv := sphereActionN_inv_right R
      continuous_toFun := sphereActionN_continuous R
      continuous_invFun := sphereActionN_continuous (R⁻¹) }
  )

-- lem:sphere-action-homeomorph: Problem1.sphereActionEquivN_apply
theorem sphereActionEquivN_apply {m : ℕ} (R : OrthogonalN m) (x : UnitSphereN m) : sphereActionEquivN R x = sphereActionN R x := by
  rfl

-- lem:sphere-action-homeomorph: Problem1.sphereActionEquivN_symm_apply
theorem sphereActionEquivN_symm_apply {m : ℕ} (R : OrthogonalN m) (x : UnitSphereN m) : (sphereActionEquivN R).symm x = sphereActionN R⁻¹ x := by
  rfl

-- lem:sphere-action-homeomorph: Problem1.sphereActionN_measurableEmbedding
theorem sphereActionN_measurableEmbedding {m : ℕ} (R : OrthogonalN m) : MeasurableEmbedding (sphereActionN R) := by
  exact (sphereActionEquivN R).measurableEmbedding

-- lem:sphere-action-homeomorph: Problem1.sphereActionEquiv
noncomputable abbrev sphereActionEquiv {d : ℕ} (R : Orthogonal d) : Sphere d ≃ₜ Sphere d := by
  classical
  exact (
    sphereActionEquivN R
  )

-- lem:sphere-action-distance: Problem1.sphereActionN_norm_sub
theorem sphereActionN_norm_sub {m : ℕ} (R : OrthogonalN m) (x y : UnitSphereN m) : ‖(sphereActionN R x : EuclideanN m) - (sphereActionN R y : EuclideanN m)‖ = ‖(x : EuclideanN m) - (y : EuclideanN m)‖ := by
  rw [sphereActionN_coe, sphereActionN_coe, ← map_sub]
  exact orthogonalLin_norm R ((x : EuclideanN m) - (y : EuclideanN m))

-- lem:sphere-action-distance: Problem1.sphereActionN_dist
theorem sphereActionN_dist {m : ℕ} (R : OrthogonalN m) (x y : UnitSphereN m) : dist (sphereActionN R x) (sphereActionN R y) = dist x y := by
  simpa only [unitSphereN_dist_eq] using sphereActionN_norm_sub R x y

-- lem:sphere-action-distance: Problem1.sphereActionN_isometry
theorem sphereActionN_isometry {m : ℕ} (R : OrthogonalN m) : Isometry (sphereActionN R) := by
  exact isometry_iff_dist_eq.mpr (sphereActionN_dist R)

-- cor:kernel-action-invariance: Problem1.kernel_sphereAction
theorem kernel_sphereAction {d : ℕ} (s : ℝ) (R : Orthogonal d) (x y : Sphere d) : kernel d s (sphereAction R x) (sphereAction R y) = kernel d s x y := by
  exact kernel_isometry d s (sphereAction R) (sphereActionN_dist R) x y

-- def:householder: Problem1.householder_denominator_pos
theorem householder_denominator_pos {m : ℕ} (v : EuclideanN m) (hv : v ≠ 0) : inner ℝ v v = ‖v‖ ^ 2 ∧ 0 < inner ℝ v v := by
  exact ⟨real_inner_self_eq_norm_sq v, real_inner_self_pos.mpr hv⟩

-- def:householder: Problem1.householder
noncomputable def householder {m : ℕ} (v : EuclideanN m) (hv : v ≠ 0) : EuclideanN m →ₗ[ℝ] EuclideanN m := by
  classical
  exact (
    LinearMap.id - (2 / inner ℝ v v) • ((innerSL ℝ v).toLinearMap.smulRight v)
  )

-- def:householder: Problem1.householder_apply
theorem householder_apply {m : ℕ} (v : EuclideanN m) (hv : v ≠ 0) (z : EuclideanN m) : householder v hv z = z - ((2 * inner ℝ z v) / inner ℝ v v) • v := by
  have hcoeff : (2 / inner ℝ v v) * inner ℝ v z =
      (2 * inner ℝ z v) / inner ℝ v v := by
    rw [real_inner_comm z v]
    ring
  change z - (2 / inner ℝ v v) • (inner ℝ v z • v) =
    z - ((2 * inner ℝ z v) / inner ℝ v v) • v
  rw [smul_smul, hcoeff]

-- lem:householder-inner: Problem1.householder_inner
theorem householder_inner {m : ℕ} (v : EuclideanN m) (hv : v ≠ 0) (z w : EuclideanN m) : inner ℝ (householder v hv z) (householder v hv w) = inner ℝ z w := by
  have hq : inner ℝ v v ≠ 0 := ne_of_gt (householder_denominator_pos v hv).2
  rw [householder_apply, householder_apply]
  simp only [inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm w v]
  field_simp [hq] <;> ring

-- lem:householder-matrix: Problem1.householderMatrix
noncomputable def householderMatrix {m : ℕ} (v : EuclideanN m) : Matrix (Fin m) (Fin m) ℝ := by
  classical
  exact (
    fun i j => (if i = j then (1 : ℝ) else 0) - (2 * v i * v j) / inner ℝ v v
  )

-- lem:householder-matrix: Problem1.householderMatrix_mem
theorem householderMatrix_mem {m : ℕ} (v : EuclideanN m) (hv : v ≠ 0) : householderMatrix v ∈ Matrix.orthogonalGroup (Fin m) ℝ := by
  classical
  have hcol (i j : Fin m) :
      (householder v hv (EuclideanSpace.basisFun (Fin m) ℝ j)) i =
        householderMatrix v i j := by
    rw [householder_apply, EuclideanSpace.basisFun_inner]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      EuclideanSpace.basisFun_apply, PiLp.single_apply, householderMatrix]
    simp only [div_eq_mul_inv]
    ring
  apply (Matrix.mem_orthogonalGroup_iff' (n := Fin m) (R := ℝ)).mpr
  apply Matrix.ext
  intro i j
  have hstandard : inner ℝ (EuclideanSpace.basisFun (Fin m) ℝ j)
      (EuclideanSpace.basisFun (Fin m) ℝ i) =
        (if i = j then (1 : ℝ) else 0) := by
    rw [EuclideanSpace.basisFun_inner]
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]
  have hip := householder_inner v hv
    (EuclideanSpace.basisFun (Fin m) ℝ j) (EuclideanSpace.basisFun (Fin m) ℝ i)
  rw [hstandard] at hip
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hip
  change (∑ k : Fin m,
    (householder v hv (EuclideanSpace.basisFun (Fin m) ℝ i)) k *
    (householder v hv (EuclideanSpace.basisFun (Fin m) ℝ j)) k) =
      (if i = j then (1 : ℝ) else 0) at hip
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, hcol] using hip

-- lem:householder-matrix: Problem1.householderOrthogonal
noncomputable def householderOrthogonal {m : ℕ} (v : EuclideanN m) (hv : v ≠ 0) : OrthogonalN m := by
  classical
  exact (
    ⟨householderMatrix v, householderMatrix_mem v hv⟩
  )

-- lem:householder-matrix: Problem1.householderOrthogonal_lin
theorem householderOrthogonal_lin {m : ℕ} (v : EuclideanN m) (hv : v ≠ 0) : orthogonalLin (householderOrthogonal v hv) = householder v hv := by
  classical
  apply LinearMap.ext
  intro z
  apply WithLp.ofLp_injective 2
  funext i
  change orthogonalLin (householderOrthogonal v hv) z i = householder v hv z i
  rw [orthogonalLin_apply_coordinate, householder_apply]
  change (∑ j : Fin m,
    ((if i = j then (1 : ℝ) else 0) - (2 * v i * v j) / inner ℝ v v) * z j) =
      z i - ((2 * inner ℝ z v) / inner ℝ v v) * v i
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hdelta : (∑ j : Fin m, (if i = j then (1 : ℝ) else 0) * z j) = z i := by simp
  rw [hdelta]
  apply congrArg (fun a : ℝ => z i - a)
  have hin : inner ℝ z v = ∑ j : Fin m, v j * z j := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  rw [hin]
  calc
    (∑ j : Fin m, ((2 * v i * v j) / inner ℝ v v) * z j) =
        (∑ j : Fin m, v j * z j) * (2 * v i / inner ℝ v v) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [div_eq_mul_inv]
      ring
    _ = ((2 * (∑ j : Fin m, v j * z j)) / inner ℝ v v) * v i := by
      simp only [div_eq_mul_inv]
      ring

-- lem:householder-matrix: Problem1.householder_matrix
theorem householder_matrix {m : ℕ} (v : EuclideanN m) (hv : v ≠ 0) : ∃ R : OrthogonalN m, orthogonalLin R = householder v hv := by
  exact ⟨householderOrthogonal v hv, householderOrthogonal_lin v hv⟩

-- lem:householder-north: Problem1.householder_north_sub_ne_zero
theorem householder_north_sub_ne_zero (m : ℕ) (hm : 1 ≤ m) (x : UnitSphereN m) (hx : x ≠ northPoleN m hm) : (northPoleVector m hm - (x : EuclideanN m)) ≠ 0 := by
  intro h
  apply hx
  apply Subtype.ext
  simpa only [northPoleN_coe] using (sub_eq_zero.mp h).symm

-- lem:householder-north: Problem1.householder_north_norm_sq
theorem householder_north_norm_sq (m : ℕ) (hm : 1 ≤ m) (x : UnitSphereN m) (hx : x ≠ northPoleN m hm) : ‖northPoleVector m hm - (x : EuclideanN m)‖ ^ 2 = 2 * (1 - (x : EuclideanN m) ⟨0, hm⟩) := by
  have hinner :
      inner ℝ (northPoleVector m hm) (x : EuclideanN m) =
        (x : EuclideanN m) ⟨0, hm⟩ := by
    simpa only [northPoleVector, map_one, one_mul] using
      (EuclideanSpace.inner_single_left (𝕜 := ℝ)
        (⟨0, hm⟩ : Fin m) 1 (x : EuclideanN m))
  rw [norm_sub_sq_real, northPoleVector_norm, unitSphereN_norm, hinner]
  ring

-- lem:householder-north: Problem1.householder_north_inner
theorem householder_north_inner (m : ℕ) (hm : 1 ≤ m) (x : UnitSphereN m) (hx : x ≠ northPoleN m hm) : inner ℝ (northPoleVector m hm) (northPoleVector m hm - (x : EuclideanN m)) = 1 - (x : EuclideanN m) ⟨0, hm⟩ := by
  have hinner :
      inner ℝ (northPoleVector m hm) (x : EuclideanN m) =
        (x : EuclideanN m) ⟨0, hm⟩ := by
    simpa only [northPoleVector, map_one, one_mul] using
      (EuclideanSpace.inner_single_left (𝕜 := ℝ)
        (⟨0, hm⟩ : Fin m) 1 (x : EuclideanN m))
  rw [inner_sub_right, real_inner_self_eq_norm_sq,
    northPoleVector_norm, hinner]
  norm_num

-- lem:householder-north: Problem1.householder_north
theorem householder_north (m : ℕ) (hm : 1 ≤ m) (x : UnitSphereN m) (hx : x ≠ northPoleN m hm) : householder (northPoleVector m hm - (x : EuclideanN m)) (householder_north_sub_ne_zero m hm x hx) (northPoleVector m hm) = (x : EuclideanN m) := by
  have hden := householder_denominator_pos
    (northPoleVector m hm - (x : EuclideanN m))
    (householder_north_sub_ne_zero m hm x hx)
  have hq :
      inner ℝ (northPoleVector m hm - (x : EuclideanN m))
        (northPoleVector m hm - (x : EuclideanN m)) =
          2 * (1 - (x : EuclideanN m) ⟨0, hm⟩) :=
    hden.1.trans (householder_north_norm_sq m hm x hx)
  rw [householder_apply, householder_north_inner m hm x hx, ← hq,
    div_self (ne_of_gt hden.2), one_smul]
  abel

-- lem:orthogonal-transitive: Problem1.orthogonal_north_transitive
theorem orthogonal_north_transitive (m : ℕ) (hm : 1 ≤ m) (x : UnitSphereN m) : ∃ R : OrthogonalN m, sphereActionN R (northPoleN m hm) = x := by
  classical
  by_cases hx : x = northPoleN m hm
  · refine ⟨1, ?_⟩
    simpa only [sphereActionN_one] using hx.symm
  · obtain ⟨R, hR⟩ := householder_matrix
      (northPoleVector m hm - (x : EuclideanN m))
      (householder_north_sub_ne_zero m hm x hx)
    refine ⟨R, ?_⟩
    apply Subtype.ext
    rw [sphereActionN_coe, northPoleN_coe, hR]
    exact householder_north m hm x hx

-- lem:sphere-transitive: Problem1.sphere_transitive
theorem sphere_transitive (m : ℕ) (hm : 1 ≤ m) (x y : UnitSphereN m) : ∃ R : OrthogonalN m, sphereActionN R x = y := by
  obtain ⟨Rx, hRx⟩ := orthogonal_north_transitive m hm x
  obtain ⟨Ry, hRy⟩ := orthogonal_north_transitive m hm y
  refine ⟨Ry * Rx⁻¹, ?_⟩
  rw [sphereActionN_mul, ← hRx, sphereActionN_inv_left, hRy]

-- def:orthogonal-haar: Problem1.orthogonalPositive
noncomputable def orthogonalPositive (m : ℕ) : TopologicalSpace.PositiveCompacts (OrthogonalN m) := by
  classical
  exact (
    { carrier := Set.univ
      isCompact' := orthogonalN_univ_isCompact m
      interior_nonempty' :=
        Eq.mpr
          (congrArg Set.Nonempty
            (interior_univ :
              interior (Set.univ : Set (OrthogonalN m)) = Set.univ))
          ⟨(1 : OrthogonalN m), Set.mem_univ 1⟩ }
  )

-- def:orthogonal-haar: Problem1.orthogonalPositive_coe
theorem orthogonalPositive_coe (m : ℕ) : (orthogonalPositive m : Set (OrthogonalN m)) = Set.univ := by
  rfl

-- def:orthogonal-haar: Problem1.orthogonalHaar
noncomputable def orthogonalHaar (m : ℕ) : Measure (OrthogonalN m) := by
  classical
  exact (
    Measure.haarMeasure (orthogonalPositive m)
  )

-- def:orthogonal-haar: Problem1.orthogonalHaarIsHaarMeasure
instance orthogonalHaarIsHaarMeasure (m : ℕ) : Measure.IsHaarMeasure (orthogonalHaar m) := by
  change Measure.IsHaarMeasure (Measure.haarMeasure (orthogonalPositive m))
  exact Measure.isHaarMeasure_haarMeasure (orthogonalPositive m)

-- lem:haar-mass-one: Problem1.orthogonalHaar_univ
theorem orthogonalHaar_univ (m : ℕ) : orthogonalHaar m Set.univ = 1 := by
  change Measure.haarMeasure (orthogonalPositive m)
    (orthogonalPositive m : Set (OrthogonalN m)) = 1
  exact Measure.haarMeasure_self

-- lem:haar-mass-one: Problem1.orthogonalHaarIsProbabilityMeasure
instance orthogonalHaarIsProbabilityMeasure (m : ℕ) : IsProbabilityMeasure (orthogonalHaar m) := by
  exact ⟨orthogonalHaar_univ m⟩

-- lem:haar-left-invariance: Problem1.orthogonalHaar_map_mul_left
theorem orthogonalHaar_map_mul_left {m : ℕ} (U : OrthogonalN m) : Measure.map (fun R : OrthogonalN m => U * R) (orthogonalHaar m) = orthogonalHaar m := by
  exact MeasureTheory.map_mul_left_eq_self (orthogonalHaar m) U

-- lem:haar-open-positive: Problem1.orthogonalHaar_pos_of_isOpen_nonempty
theorem orthogonalHaar_pos_of_isOpen_nonempty {m : ℕ} {V : Set (OrthogonalN m)} (hVopen : IsOpen V) (hV : V.Nonempty) : 0 < orthogonalHaar m V := by
  exact hVopen.measure_pos (orthogonalHaar m) hV

-- def:orbit-map: Problem1.orbitMap
noncomputable def orbitMap (m : ℕ) (hm : 1 ≤ m) : OrthogonalN m → UnitSphereN m := by
  classical
  exact (
    fun R => sphereActionN R (northPoleN m hm)
  )

-- def:orbit-map: Problem1.orbitMap_apply
theorem orbitMap_apply (m : ℕ) (hm : 1 ≤ m) (R : OrthogonalN m) : orbitMap m hm R = sphereActionN R (northPoleN m hm) := by
  rfl

-- def:orbit-map: Problem1.orbitMap_apply_coe
theorem orbitMap_apply_coe (m : ℕ) (hm : 1 ≤ m) (R : OrthogonalN m) : (orbitMap m hm R : EuclideanN m) = Matrix.toEuclideanLin (R : Matrix (Fin m) (Fin m) ℝ) (northPoleVector m hm) := by
  rw [orbitMap_apply, sphereActionN_coe, northPoleN_coe]
  rfl

-- lem:orbit-continuous: Problem1.orbitMap_continuous
theorem orbitMap_continuous (m : ℕ) (hm : 1 ≤ m) : Continuous (orbitMap m hm) := by
  exact (sphereActionN_joint_continuous m).comp (continuous_id.prodMk continuous_const)

-- lem:orbit-continuous: Problem1.orbitMap_measurable
theorem orbitMap_measurable (m : ℕ) (hm : 1 ≤ m) : Measurable (orbitMap m hm) := by
  exact (orbitMap_continuous m hm).measurable

-- lem:orbit-surjective: Problem1.orbitMap_surjective
theorem orbitMap_surjective (m : ℕ) (hm : 1 ≤ m) : Function.Surjective (orbitMap m hm) := by
  intro x
  simpa only [orbitMap_apply] using orthogonal_north_transitive m hm x

-- lem:orbit-map-action: Problem1.orbitMap_action
theorem orbitMap_action (m : ℕ) (hm : 1 ≤ m) (U : OrthogonalN m) : sphereActionN U ∘ orbitMap m hm = orbitMap m hm ∘ (fun R : OrthogonalN m => U * R) := by
  funext R
  simp only [Function.comp_apply, orbitMap_apply]
  exact (sphereActionN_mul U R (northPoleN m hm)).symm

-- def:spherical-measure: Problem1.sigmaGeneric
noncomputable def sigmaGeneric (m : ℕ) (hm : 1 ≤ m) : Measure (UnitSphereN m) := by
  classical
  exact (
    Measure.map (orbitMap m hm) (orthogonalHaar m)
  )

-- def:spherical-measure: Problem1.sigma
noncomputable def sigma (d : ℕ) : Measure (Sphere d) := by
  classical
  exact (
    sigmaGeneric (d + 1) (Nat.succ_pos d)
  )

-- lem:spherical-measure-construction: Problem1.sigmaGeneric_univ
theorem sigmaGeneric_univ (m : ℕ) (hm : 1 ≤ m) : sigmaGeneric m hm Set.univ = 1 := by
  rw [sigmaGeneric, Measure.map_apply (orbitMap_measurable m hm)
    MeasurableSet.univ]
  simpa only [Set.preimage_univ] using orthogonalHaar_univ m

-- lem:spherical-measure-construction: Problem1.sigmaGenericIsProbabilityMeasure
instance sigmaGenericIsProbabilityMeasure (m : ℕ) (hm : 1 ≤ m) : IsProbabilityMeasure (sigmaGeneric m hm) := by
  exact ⟨sigmaGeneric_univ m hm⟩

-- lem:spherical-measure-construction: Problem1.sigmaGeneric_isFiniteMeasure
theorem sigmaGeneric_isFiniteMeasure (m : ℕ) (hm : 1 ≤ m) : IsFiniteMeasure (sigmaGeneric m hm) := by
  exact MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure
    (sigmaGeneric m hm)

-- cor:sphere-mass-one: Problem1.sphere_mass_one
theorem sphere_mass_one (d : ℕ) : sigma d Set.univ = 1 := by
  exact sigmaGeneric_univ (d + 1) (Nat.succ_pos d)

-- cor:sphere-mass-one: Problem1.sphereIsProbabilityMeasure
instance sphereIsProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (sigma d) := by
  exact ⟨sphere_mass_one d⟩

-- cor:sphere-mass-one: Problem1.sphere_isFiniteMeasure
theorem sphere_isFiniteMeasure (d : ℕ) : IsFiniteMeasure (sigma d) := by
  exact MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure (sigma d)

-- lem:sphere-map-invariance: Problem1.sigmaGeneric_map_sphereActionN
theorem sigmaGeneric_map_sphereActionN (m : ℕ) (hm : 1 ≤ m) (U : OrthogonalN m) : Measure.map (sphereActionN U) (sigmaGeneric m hm) = sigmaGeneric m hm := by
  unfold sigmaGeneric
  rw [Measure.map_map (sphereActionN_continuous U).measurable
      (orbitMap_measurable m hm), orbitMap_action m hm U,
    ← Measure.map_map (orbitMap_measurable m hm) (measurable_const_mul U),
    orthogonalHaar_map_mul_left U]

-- lem:sphere-action-measure-preserving: Problem1.sphereActionN_measurePreserving
theorem sphereActionN_measurePreserving (m : ℕ) (hm : 1 ≤ m) (U : OrthogonalN m) : MeasurePreserving (sphereActionN U) (sigmaGeneric m hm) (sigmaGeneric m hm) := by
  exact ⟨(sphereActionN_continuous U).measurable,
    sigmaGeneric_map_sphereActionN m hm U⟩

-- lem:sphere-action-measure-preserving: Problem1.sphereActionN_measure_preserving_and_embedding
theorem sphereActionN_measure_preserving_and_embedding (m : ℕ) (hm : 1 ≤ m) (U : OrthogonalN m) : MeasurePreserving (sphereActionN U) (sigmaGeneric m hm) (sigmaGeneric m hm) ∧ MeasurableEmbedding (sphereActionN U) := by
  exact ⟨sphereActionN_measurePreserving m hm U, sphereActionN_measurableEmbedding U⟩

-- lem:sphere-integrable-transport: Problem1.integrable_sphereActionN_iff
theorem integrable_sphereActionN_iff (m : ℕ) (hm : 1 ≤ m) (U : OrthogonalN m) (f : UnitSphereN m → ℝ) : Integrable (f ∘ sphereActionN U) (sigmaGeneric m hm) ↔ Integrable f (sigmaGeneric m hm) := by
  exact (sphereActionN_measurePreserving m hm U).integrable_comp_emb
    (sphereActionN_measurableEmbedding U)

-- lem:sphere-lintegral-transport: Problem1.sigmaGeneric_lintegral_sphereActionN
theorem sigmaGeneric_lintegral_sphereActionN (m : ℕ) (hm : 1 ≤ m) (U : OrthogonalN m) (f : UnitSphereN m → ENNReal) (hf : Measurable f) : (∫⁻ x, f (sphereActionN U x) ∂sigmaGeneric m hm) = ∫⁻ x, f x ∂sigmaGeneric m hm := by
  exact (sphereActionN_measurePreserving m hm U).lintegral_comp hf

-- lem:sphere-integral-transport: Problem1.sigmaGeneric_integral_sphereActionN
theorem sigmaGeneric_integral_sphereActionN (m : ℕ) (hm : 1 ≤ m) (U : OrthogonalN m) (f : UnitSphereN m → ℝ) (hf : Integrable f (sigmaGeneric m hm)) : (∫ x, f (sphereActionN U x) ∂sigmaGeneric m hm) = ∫ x, f x ∂sigmaGeneric m hm := by
  have _hcomp : Integrable (f ∘ sphereActionN U) (sigmaGeneric m hm) :=
    (integrable_sphereActionN_iff m hm U f).2 hf
  exact (sphereActionN_measurePreserving m hm U).integral_comp
    (sphereActionN_measurableEmbedding U) f

-- lem:sphere-open-positive: Problem1.sigmaGeneric_pos_of_isOpen_nonempty
theorem sigmaGeneric_pos_of_isOpen_nonempty (m : ℕ) (hm : 1 ≤ m) {V : Set (UnitSphereN m)} (hVopen : IsOpen V) (hV : V.Nonempty) : 0 < sigmaGeneric m hm V := by
  have hpreimage : (orbitMap m hm ⁻¹' V).Nonempty := by
    obtain ⟨x, hx⟩ := hV
    obtain ⟨R, hR⟩ := orbitMap_surjective m hm x
    refine ⟨R, ?_⟩
    simpa only [Set.mem_preimage, hR] using hx
  rw [sigmaGeneric,
    Measure.map_apply (orbitMap_measurable m hm) hVopen.measurableSet]
  exact orthogonalHaar_pos_of_isOpen_nonempty
    (hVopen.preimage (orbitMap_continuous m hm)) hpreimage

-- lem:sphere-open-positive: Problem1.sigmaGenericIsOpenPosMeasure
instance sigmaGenericIsOpenPosMeasure (m : ℕ) (hm : 1 ≤ m) : Measure.IsOpenPosMeasure (sigmaGeneric m hm) := by
  refine ⟨?_⟩
  intro V hVopen hV
  exact ne_of_gt (sigmaGeneric_pos_of_isOpen_nonempty m hm hVopen hV)

-- lem:sigma-basic: Problem1.sigma_map_sphereAction
theorem sigma_map_sphereAction {d : ℕ} (U : Orthogonal d) : Measure.map (sphereAction U) (sigma d) = sigma d := by
  exact sigmaGeneric_map_sphereActionN (d + 1) (Nat.succ_pos d) U

-- lem:sigma-basic: Problem1.sphereAction_measurePreserving
theorem sphereAction_measurePreserving {d : ℕ} (U : Orthogonal d) : MeasurePreserving (sphereAction U) (sigma d) (sigma d) := by
  exact sphereActionN_measurePreserving (d + 1) (Nat.succ_pos d) U

-- lem:sigma-basic: Problem1.integrable_sphereAction_iff
theorem integrable_sphereAction_iff {d : ℕ} (U : Orthogonal d) (f : Sphere d → ℝ) : Integrable (f ∘ sphereAction U) (sigma d) ↔ Integrable f (sigma d) := by
  exact integrable_sphereActionN_iff (d + 1) (Nat.succ_pos d) U f

-- lem:sigma-basic: Problem1.sigma_lintegral_sphereAction
theorem sigma_lintegral_sphereAction {d : ℕ} (U : Orthogonal d) (f : Sphere d → ENNReal) (hf : Measurable f) : (∫⁻ x, f (sphereAction U x) ∂sigma d) = ∫⁻ x, f x ∂sigma d := by
  exact sigmaGeneric_lintegral_sphereActionN (d + 1) (Nat.succ_pos d) U f hf

-- lem:sigma-basic: Problem1.sigma_integral_sphereAction
theorem sigma_integral_sphereAction {d : ℕ} (U : Orthogonal d) (f : Sphere d → ℝ) (hf : Integrable f (sigma d)) : (∫ x, f (sphereAction U x) ∂sigma d) = ∫ x, f x ∂sigma d := by
  exact sigmaGeneric_integral_sphereActionN (d + 1) (Nat.succ_pos d) U f hf

-- lem:sigma-basic: Problem1.sigma_pos_of_isOpen_nonempty
theorem sigma_pos_of_isOpen_nonempty {d : ℕ} {V : Set (Sphere d)} (hVopen : IsOpen V) (hV : V.Nonempty) : 0 < sigma d V := by
  exact sigmaGeneric_pos_of_isOpen_nonempty (d + 1) (Nat.succ_pos d) hVopen hV

-- lem:sigma-basic: Problem1.sphereIsOpenPosMeasure
instance sphereIsOpenPosMeasure (d : ℕ) : Measure.IsOpenPosMeasure (sigma d) := by
  refine ⟨?_⟩
  intro V hVopen hV
  exact ne_of_gt (sigma_pos_of_isOpen_nonempty hVopen hV)

-- lem:sigma-basic: Problem1.sigma_basic
theorem sigma_basic (d : ℕ) : BorelSpace (Sphere d) ∧ IsProbabilityMeasure (sigma d) ∧ sigma d Set.univ = 1 ∧ IsFiniteMeasure (sigma d) ∧ (∀ U : Orthogonal d, Measure.map (sphereAction U) (sigma d) = sigma d) ∧ (∀ (U : Orthogonal d) (f : Sphere d → ℝ), Integrable (f ∘ sphereAction U) (sigma d) ↔ Integrable f (sigma d)) ∧ (∀ (U : Orthogonal d) (f : Sphere d → ENNReal), Measurable f → (∫⁻ x, f (sphereAction U x) ∂sigma d) = ∫⁻ x, f x ∂sigma d) ∧ (∀ (U : Orthogonal d) (f : Sphere d → ℝ), Integrable f (sigma d) → (∫ x, f (sphereAction U x) ∂sigma d) = ∫ x, f x ∂sigma d) ∧ (∀ V : Set (Sphere d), IsOpen V → V.Nonempty → 0 < sigma d V) := by
  exact ⟨inferInstance, sphereIsProbabilityMeasure d, sphere_mass_one d,
    sphere_isFiniteMeasure d, sigma_map_sphereAction, integrable_sphereAction_iff,
    sigma_lintegral_sphereAction, sigma_integral_sphereAction,
    fun _ hVopen hV => sigma_pos_of_isOpen_nonempty hVopen hV⟩

-- def:continuous-energy-constant: Problem1.continuousEnergy
noncomputable def continuousEnergy (d : ℕ) (s : ℝ) : ℝ := by
  classical
  exact (
    ∫ y, kernel d s (northPole d) y ∂sigma d
  )

-- def:coordinate-weight: Problem1.coordinateExponent
noncomputable def coordinateExponent (d : ℕ) :
  ℝ := by
  classical
  exact (
    ((d : ℝ) - 2) / 2
  )

-- def:coordinate-weight: Problem1.coordinateWeight
noncomputable def coordinateWeight (d : ℕ) (t : ℝ) :
  ℝ := by
  classical
  exact (
    if t ∈ Set.Icc (-1 : ℝ) 1 then Real.rpow (1 - t ^ 2) (coordinateExponent d) else 0
  )

-- def:coordinate-weight: Problem1.coordinateNormalizer
noncomputable def coordinateNormalizer (d : ℕ) :
  ℝ := by
  classical
  exact (
    ∫ t in Set.Icc (-1 : ℝ) 1, coordinateWeight d t ∂volume
  )

-- def:coordinate-weight: Problem1.coordinateNormConst
noncomputable def coordinateNormConst (d : ℕ) :
  ℝ := by
  classical
  exact (
    (coordinateNormalizer d)⁻¹
  )

-- lem:coordinate-parameters: Problem1.coordinate_parameters
theorem coordinate_parameters (d r : ℕ) (hd : 2 ≤ d) :
  0 ≤ coordinateExponent d ∧
  0 < (r : ℝ) + 1 / 2 ∧
  0 < (d : ℝ) / 2 ∧
  ∀ t : ℝ, t ∈ Set.Ioo 0 1 →
    0 < t ^ 2 ∧ t ^ 2 < 1 ∧ 0 < 1 - t ^ 2 := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [coordinateExponent]
    linarith
  · positivity
  · linarith
  · intro t ht
    have hsqpos : 0 < t ^ 2 := pow_pos ht.1 2
    have hsqlt : t ^ 2 < 1 := by
      nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
    exact ⟨hsqpos, hsqlt, sub_pos.mpr hsqlt⟩

-- lem:coordinate-weight-measurable: Problem1.coordinate_weight_measurable
theorem coordinate_weight_measurable (d : ℕ) (hd : 2 ≤ d) :
  Measurable (coordinateWeight d) ∧ ∀ t : ℝ, 0 ≤ coordinateWeight d t := by
  classical
  constructor
  · have hrpow : Measurable (fun x : ℝ => Real.rpow x (coordinateExponent d)) := by
      refine measurable_of_continuousOn_compl_singleton 0 ?_
      intro x hx
      exact (Real.continuousAt_rpow_const x (coordinateExponent d)
        (Or.inl (by simpa using hx))).continuousWithinAt
    unfold coordinateWeight
    exact (hrpow.comp (measurable_const.sub (measurable_id.pow_const 2))).ite
      measurableSet_Icc measurable_const
  · intro t
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
    · rw [coordinateWeight, if_pos ht]
      apply Real.rpow_nonneg
      have hbase : 0 ≤ (1 - t) * (1 + t) :=
        mul_nonneg (sub_nonneg.mpr ht.2) (by linarith [ht.1])
      nlinarith
    · simp [coordinateWeight, ht]

-- lem:coordinate-even: Problem1.coordinate_even
theorem coordinate_even (d r : ℕ) (t : ℝ) :
  coordinateWeight d (-t) = coordinateWeight d t ∧
  (-t) ^ (2 * r) * coordinateWeight d (-t) = t ^ (2 * r) * coordinateWeight d t := by
  classical
  have hmem : -t ∈ Set.Icc (-1 : ℝ) 1 ↔ t ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hw : coordinateWeight d (-t) = coordinateWeight d t := by
    simp only [coordinateWeight, hmem, neg_sq]
  refine ⟨hw, ?_⟩
  rw [hw]
  simp only [pow_mul, neg_sq]

-- lem:square-map-calculus: Problem1.square_map_calculus
theorem square_map_calculus :
  ContinuousOn (fun t : ℝ => t ^ 2) (Set.Icc 0 1) ∧
  (0 : ℝ) ^ 2 = 0 ∧
  (1 : ℝ) ^ 2 = 1 ∧
  ∀ t : ℝ, t ∈ Set.Ioo 0 1 →
    HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t ∧ 0 ≤ 2 * t := by
  refine ⟨(continuous_pow 2).continuousOn, by norm_num, by norm_num, ?_⟩
  intro t ht
  constructor
  · simpa using hasDerivAt_pow 2 t
  · exact le_of_lt (mul_pos (by norm_num) ht.1)

-- lem:square-substitution-integrable: Problem1.square_substitution_integrable
theorem square_substitution_integrable (d r : ℕ) (hd : 2 ≤ d) :
  IntegrableOn (fun t : ℝ => betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) (t ^ 2) * (2 * t)) (Set.Icc 0 1) volume := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hparameters := coordinate_parameters d r hd
  have hcalculus := square_map_calculus
  have hbeta : IntervalIntegrable
      (betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2)) volume (0 : ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le h01).mpr
      (beta_integrable _ _ hparameters.2.1 hparameters.2.2.1).2
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun t : ℝ => t ^ 2) (f' := fun t : ℝ => 2 * t)
    (g := betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2))
    (by simpa only [Set.uIcc_of_le h01] using hcalculus.1)
    (by
      intro t ht
      exact (hcalculus.2.2.2 t
        (by simpa only [min_eq_left h01, max_eq_right h01] using ht)).1)
    (by
      intro t ht
      exact (hcalculus.2.2.2 t
        (by simpa only [min_eq_left h01, max_eq_right h01] using ht)).2)
  have htransformed := hiff.mpr
    (by simpa only [hcalculus.2.1, hcalculus.2.2.1] using hbeta)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le h01).mp htransformed

-- lem:square-substitution-value: Problem1.square_substitution_value
theorem square_substitution_value (d r : ℕ) (hd : 2 ≤ d) :
  (∫ t in Set.Icc (0 : ℝ) 1, betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) (t ^ 2) * (2 * t) ∂volume) = ProbabilityTheory.beta ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hparameters := coordinate_parameters d r hd
  have hcalculus := square_map_calculus
  have hsub :
      intervalIntegral
        (fun t : ℝ => betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2)
          (t ^ 2) * (2 * t)) 0 1 volume =
      intervalIntegral
        (betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2)) 0 1 volume := by
    have hraw := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun t : ℝ => t ^ 2) (f' := fun t : ℝ => 2 * t)
        (g := betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2))
        (by simpa only [Set.uIcc_of_le h01] using hcalculus.1)
        (by
          intro t ht
          exact (hcalculus.2.2.2 t
            (by simpa only [min_eq_left h01, max_eq_right h01] using ht)).1)
        (by
          intro t ht
          exact (hcalculus.2.2.2 t
            (by simpa only [min_eq_left h01, max_eq_right h01] using ht)).2)
    simpa only [Function.comp_apply, pow_two, mul_zero, mul_one] using hraw
  calc
    (∫ t in Set.Icc (0 : ℝ) 1,
        betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) (t ^ 2) * (2 * t) ∂volume) =
        intervalIntegral
          (fun t : ℝ => betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2)
            (t ^ 2) * (2 * t)) 0 1 volume := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le h01]
    _ = intervalIntegral
        (betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2)) 0 1 volume := hsub
    _ = ∫ t in Set.Icc (0 : ℝ) 1,
        betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) t ∂volume := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le h01]
    _ = ∫ t : ℝ, betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) t ∂volume := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hnot : ¬ (0 < t ∧ t < 1) := by
        intro ht01
        exact ht ⟨ht01.1.le, ht01.2.le⟩
      rw [betaRealDensity, if_neg hnot]
    _ = ProbabilityTheory.beta ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) :=
      beta_integral_value _ _ hparameters.2.1 hparameters.2.2.1

-- lem:coordinate-square-algebra: Problem1.coordinate_square_algebra
theorem coordinate_square_algebra (d r : ℕ) (hd : 2 ≤ d) (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
  betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) (t ^ 2) * (2 * t) = 2 * (t ^ (2 * r) * coordinateWeight d t) := by
  have hsqrange := (coordinate_parameters d r hd).2.2.2 t ht
  have hbeta : 0 < t ^ 2 ∧ t ^ 2 < 1 :=
    ⟨hsqrange.1, hsqrange.2.1⟩
  have htmem : t ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · linarith [ht.1]
    · exact ht.2.le
  have hxp :
      Real.rpow (t ^ 2) (((r : ℝ) + 1 / 2) - 1) * t =
        t ^ (2 * r) := by
    have hsq : t ^ (2 : ℕ) = Real.rpow t (2 : ℝ) :=
      (Real.rpow_two t).symm
    have hmul :
        Real.rpow (Real.rpow t (2 : ℝ)) (((r : ℝ) + 1 / 2) - 1) =
          Real.rpow t ((2 : ℝ) * (((r : ℝ) + 1 / 2) - 1)) :=
      (Real.rpow_mul ht.1.le (2 : ℝ) (((r : ℝ) + 1 / 2) - 1)).symm
    rw [hsq, hmul]
    have hadd :
        Real.rpow t ((2 : ℝ) * (((r : ℝ) + 1 / 2) - 1)) * t =
          Real.rpow t ((2 : ℝ) * (((r : ℝ) + 1 / 2) - 1) + 1) :=
      (Real.rpow_add_one ht.1.ne' _).symm
    rw [hadd]
    have hnat : t ^ (2 * r) = Real.rpow t ((2 * r : ℕ) : ℝ) :=
      (Real.rpow_natCast t (2 * r)).symm
    rw [hnat]
    congr 1
    push_cast
    ring
  have hbexp : (d : ℝ) / 2 - 1 = coordinateExponent d := by
    unfold coordinateExponent
    ring
  rw [betaRealDensity, if_pos hbeta, coordinateWeight, if_pos htmem, hbexp]
  calc
    Real.rpow (t ^ 2) (((r : ℝ) + 1 / 2) - 1) *
          Real.rpow (1 - t ^ 2) (coordinateExponent d) * (2 * t) =
        2 * (Real.rpow (t ^ 2) (((r : ℝ) + 1 / 2) - 1) * t) *
          Real.rpow (1 - t ^ 2) (coordinateExponent d) := by ring
    _ = 2 * (t ^ (2 * r) *
          Real.rpow (1 - t ^ 2) (coordinateExponent d)) := by
      rw [hxp]
      ring

-- lem:coordinate-square-ae: Problem1.coordinate_square_ae
theorem coordinate_square_ae (d r : ℕ) (hd : 2 ≤ d) :
  (fun t : ℝ => betaRealDensity ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) (t ^ 2) * (2 * t)) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
    (fun t : ℝ => 2 * (t ^ (2 * r) * coordinateWeight d t)) := by
  rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem (μ := volume)
    (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))] with t ht
  exact coordinate_square_algebra d r hd t ht

-- lem:coordinate-half-integrable: Problem1.coordinate_half_integrable
theorem coordinate_half_integrable (d r : ℕ) (hd : 2 ≤ d) :
  IntegrableOn (fun t : ℝ => t ^ (2 * r) * coordinateWeight d t) (Set.Icc 0 1) volume := by
  unfold IntegrableOn
  have hmul := MeasureTheory.Integrable.congr
    (square_substitution_integrable d r hd) (coordinate_square_ae d r hd)
  simpa only [← mul_assoc,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul]
    using hmul.const_mul (1 / 2 : ℝ)

-- lem:coordinate-square-substitution: Problem1.coordinate_square_substitution
theorem coordinate_square_substitution (d r : ℕ) (hd : 2 ≤ d) :
  2 * (∫ t in Set.Icc (0 : ℝ) 1, t ^ (2 * r) * coordinateWeight d t ∂volume) = ProbabilityTheory.beta ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) := by
  have hv := square_substitution_value d r hd
  rw [integral_congr_ae (coordinate_square_ae d r hd), integral_const_mul] at hv
  exact hv

-- lem:coordinate-negative-half: Problem1.coordinate_negative_half
theorem coordinate_negative_half (d r : ℕ) (hd : 2 ≤ d) :
  IntegrableOn (fun t : ℝ => t ^ (2 * r) * coordinateWeight d t) (Set.Icc (-1) 0) volume ∧
  (∫ t in Set.Icc (-1 : ℝ) 0, t ^ (2 * r) * coordinateWeight d t ∂volume) = (∫ t in Set.Icc (0 : ℝ) 1, t ^ (2 * r) * coordinateWeight d t ∂volume) := by
  let h : ℝ → ℝ := fun t => t ^ (2 * r) * coordinateWeight d t
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hn10 : (-1 : ℝ) ≤ 0 := by norm_num
  have heven : (fun t : ℝ => h (-t)) = h := by
    funext t
    exact (coordinate_even d r t).2
  have hp : IntervalIntegrable h volume (0 : ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le h01).2
      (coordinate_half_integrable d r hd)
  have hn : IntervalIntegrable h volume (-1 : ℝ) 0 := by
    have hflip :=
      (IntervalIntegrable.iff_comp_neg (f := h) (a := (0 : ℝ)) (b := (1 : ℝ))).mp hp
    rw [heven] at hflip
    simpa only [neg_zero] using hflip.symm
  constructor
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hn10).1 hn
  · change (∫ t in Set.Icc (-1 : ℝ) 0, h t ∂volume) =
      ∫ t in Set.Icc (0 : ℝ) 1, h t ∂volume
    have href :=
      (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := (1 : ℝ)) h).symm
    rw [heven] at href
    have href' : (∫ t in (-1 : ℝ)..0, h t) = ∫ t in (0 : ℝ)..1, h t := by
      simpa only [neg_zero] using href
    simpa only [intervalIntegral.integral_of_le hn10,
      intervalIntegral.integral_of_le h01, integral_Icc_eq_integral_Ioc] using href'

-- lem:coordinate-moment: Problem1.coordinate_moment
theorem coordinate_moment (d r : ℕ) (hd : 2 ≤ d) :
  IntegrableOn (fun t : ℝ => t ^ (2 * r) * coordinateWeight d t) (Set.Icc (-1) 1) volume ∧
  (∫ t in Set.Icc (-1 : ℝ) 1, t ^ (2 * r) * coordinateWeight d t ∂volume) = ProbabilityTheory.beta ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) := by
  let h : ℝ → ℝ := fun t => t ^ (2 * r) * coordinateWeight d t
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hn10 : (-1 : ℝ) ≤ 0 := by norm_num
  have hp : IntegrableOn h (Set.Icc (0 : ℝ) 1) volume :=
    coordinate_half_integrable d r hd
  have hn : IntegrableOn h (Set.Icc (-1 : ℝ) 0) volume :=
    (coordinate_negative_half d r hd).1
  have hnegative : (∫ t in Set.Icc (-1 : ℝ) 0, h t ∂volume) =
      ∫ t in Set.Icc (0 : ℝ) 1, h t ∂volume :=
    (coordinate_negative_half d r hd).2
  constructor
  · simpa only [Set.Icc_union_Icc_eq_Icc hn10 h01] using hn.union hp
  · have hnI : IntervalIntegrable h volume (-1 : ℝ) 0 :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hn10).2 hn
    have hpI : IntervalIntegrable h volume (0 : ℝ) 1 :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le h01).2 hp
    have hadd :
        (∫ t in Set.Icc (-1 : ℝ) 0, h t ∂volume) +
          (∫ t in Set.Icc (0 : ℝ) 1, h t ∂volume) =
        ∫ t in Set.Icc (-1 : ℝ) 1, h t ∂volume := by
      simpa only [intervalIntegral.integral_of_le hn10,
        intervalIntegral.integral_of_le h01,
        intervalIntegral.integral_of_le (hn10.trans h01),
        integral_Icc_eq_integral_Ioc]
        using intervalIntegral.integral_add_adjacent_intervals hnI hpI
    change (∫ t in Set.Icc (-1 : ℝ) 1, h t ∂volume) =
      ProbabilityTheory.beta ((r : ℝ) + 1 / 2) ((d : ℝ) / 2)
    calc
      (∫ t in Set.Icc (-1 : ℝ) 1, h t ∂volume) =
          (∫ t in Set.Icc (-1 : ℝ) 0, h t ∂volume) +
            (∫ t in Set.Icc (0 : ℝ) 1, h t ∂volume) := hadd.symm
      _ = 2 * (∫ t in Set.Icc (0 : ℝ) 1, h t ∂volume) := by
        rw [hnegative]
        ring
      _ = ProbabilityTheory.beta ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) :=
        coordinate_square_substitution d r hd

-- lem:coordinate-normalizer-positive: Problem1.coordinate_normalizer_positive
theorem coordinate_normalizer_positive (d : ℕ) (hd : 2 ≤ d) :
  coordinateNormalizer d = ProbabilityTheory.beta (1 / 2) ((d : ℝ) / 2) ∧
  0 < coordinateNormalizer d := by
  have hz : coordinateNormalizer d =
      ProbabilityTheory.beta (1 / 2) ((d : ℝ) / 2) := by
    simpa [coordinateNormalizer] using (coordinate_moment d 0 hd).2
  refine ⟨hz, ?_⟩
  rw [hz]
  apply beta_positive
  · norm_num
  · have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith

-- lem:coordinate-normalizer-gamma: Problem1.coordinate_normalizer_gamma
theorem coordinate_normalizer_gamma (d : ℕ) (hd : 2 ≤ d) :
  coordinateNormConst d = Real.Gamma (((d : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((d : ℝ) / 2)) ∧
  0 < coordinateNormConst d ∧
  coordinateNormConst d * coordinateNormalizer d = 1 := by
  have hz := coordinate_normalizer_positive d hd
  have hsum : (1 / 2 : ℝ) + (d : ℝ) / 2 = ((d : ℝ) + 1) / 2 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [coordinateNormConst, hz.1]
    change
      (Real.Gamma (1 / 2) * Real.Gamma ((d : ℝ) / 2) /
        Real.Gamma ((1 / 2 : ℝ) + (d : ℝ) / 2))⁻¹ = _
    rw [Real.Gamma_one_half_eq, hsum, inv_div]
  · rw [coordinateNormConst]
    exact inv_pos.mpr hz.2
  · rw [coordinateNormConst]
    exact inv_mul_cancel₀ (ne_of_gt hz.2)

-- lem:coordinate-weight-beta: Problem1.coordinate_weight_beta
theorem coordinate_weight_beta (d r : ℕ) (hd : 2 ≤ d) :
  IntegrableOn (fun t : ℝ => t ^ (2 * r) * coordinateWeight d t) (Set.Icc (-1) 1) volume ∧
  (∫ t in Set.Icc (-1 : ℝ) 1, t ^ (2 * r) * coordinateWeight d t ∂volume) = ProbabilityTheory.beta ((r : ℝ) + 1 / 2) ((d : ℝ) / 2) ∧
  coordinateNormalizer d = ProbabilityTheory.beta (1 / 2) ((d : ℝ) / 2) ∧
  0 < coordinateNormalizer d ∧
  coordinateNormConst d = Real.Gamma (((d : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((d : ℝ) / 2)) ∧
  0 < coordinateNormConst d := by
  exact ⟨(coordinate_moment d r hd).1, (coordinate_moment d r hd).2,
    (coordinate_normalizer_positive d hd).1, (coordinate_normalizer_positive d hd).2,
    (coordinate_normalizer_gamma d hd).1, (coordinate_normalizer_gamma d hd).2.1⟩

end

end Problem1
