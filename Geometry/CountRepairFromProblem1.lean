import Riesz.Geometry.SphereFromProblem1
import Riesz.Asymptotics.PositiveUpperCount

/-!
# Deterministic positive spherical count repair

The seven Problem1 declarations below are verbatim extractions from
Problem 1 - Part 1/Problem1/Part5_Polarization_and_Energy.lean,
source SHA256 885B370DDCE4361B065166097D2CB9BFFE0E1B36826AAD572BA58F7A76A4D0C4.
Retained source line intervals: 2336-2354, 2357-2362, 2372-2374, 2376-2381,
2383-2388, 2402-2407, 2456-2509. The original project clean build and
all-declaration axiom audit are recorded in its Assembly/evidence directory.
Only the imports and enclosing namespace wrapper are new.

The scalar repair below uses these identities and the exact Showcase energy.
It requires no probability law of selected subsets or repaired configurations.
-/

noncomputable section
open MeasureTheory RieszShowcase
open scoped Classical

namespace Problem1

theorem part5_energy_reindexing (d : ℕ) (hd : 2 ≤ d) {ι κ : Type*} [Fintype ι] [Fintype κ] (s : ℝ) (e : κ ≃ ι) (z : ι → Sphere d) : finiteEnergy s (z ∘ e) = finiteEnergy s z ∧ (Function.Injective z → Function.Injective (z ∘ e)) := by
  classical
  refine ⟨?_, fun hz => hz.comp e.injective⟩
  unfold finiteEnergy
  calc
    _ = Finset.sum Finset.univ (fun p : κ × κ =>
        if p.1 = p.2 then 0 else kernel d s (z (e p.1)) (z (e p.2))) :=
      (Fintype.sum_prod_type'
        (fun i j : κ =>
          if i = j then 0 else kernel d s (z (e i)) (z (e j)))).symm
    _ = Finset.sum Finset.univ (fun p : ι × ι =>
        if p.1 = p.2 then 0 else kernel d s (z p.1) (z p.2)) := by
      simpa [e.injective.eq_iff] using
        (e.prodCongr e).sum_comp
          (fun p : ι × ι =>
            if p.1 = p.2 then 0 else kernel d s (z p.1) (z p.2))
    _ = _ := Fintype.sum_prod_type'
      (fun i j : ι =>
        if i = j then 0 else kernel d s (z i) (z j))

noncomputable def part5_adjoined_configuration {d N : ℕ} (x : Sphere d) (ω : Config d N) : Config d (N + 1) := by
  classical
  exact (
    Fin.cases x ω
  )


theorem part5_adjoining_injective (d : ℕ) (hd : 2 ≤ d) (N : ℕ) (ω : Config d N) (hω : Function.Injective ω) (x : Sphere d) (hx : x ∉ siteSet ω) : Function.Injective (part5_adjoined_configuration x ω) := by
  exact Fin.cons_injective_of_injective hx hω


theorem part5_energy_adjoining (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (N : ℕ) (x : Sphere d) (ω : Config d N) : finiteEnergy s (part5_adjoined_configuration x ω) = finiteEnergy s ω + 2 * potential s ω x := by
  simp [finiteEnergy, part5_adjoined_configuration, Fin.sum_univ_succ,
    potential, kernel_symmetry, Finset.sum_add_distrib]
  simp_rw [if_neg (Fin.succ_ne_zero _).symm]
  ring


noncomputable def part5_succAbove_equivalence (N : ℕ) (k : Fin (N + 1)) : Fin N ≃ {j : Fin (N + 1) // j ≠ k} := by
  classical
  exact (
    finSuccAboveEquiv k
  )


noncomputable def part5_erase_configuration {d N : ℕ} (y : Config d (N + 1)) (k : Fin (N + 1)) : Config d N := by
  classical
  exact (
    fun i => y (part5_succAbove_equivalence N k i).val
  )


theorem part5_energy_deletion_sum (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (N : ℕ) (hN : 2 ≤ N) (y : Config d (N + 1)) : (∑ k : Fin (N + 1), finiteEnergy s (part5_erase_configuration y k)) = ((N : ℝ) - 1) * finiteEnergy s y := by
  classical
  let F : Fin (N + 1) → Fin (N + 1) → ℝ :=
    fun i j => if i = j then 0 else kernel d s (y i) (y j)
  have hdiag (i : Fin (N + 1)) : F i i = 0 := by
    simp [F]
  have hdel (k : Fin (N + 1)) :
      finiteEnergy s (part5_erase_configuration y k) =
        ∑ i ∈ Finset.univ.erase k, ∑ j ∈ Finset.univ.erase k, F i j := by
    calc
      finiteEnergy s (part5_erase_configuration y k) =
          finiteEnergy s
            (fun i : {i : Fin (N + 1) // i ≠ k} => y i) := by
        exact (part5_energy_reindexing d hd s
          (part5_succAbove_equivalence N k)
          (fun i : {i : Fin (N + 1) // i ≠ k} => y i.val)).1
      _ = ∑ i ∈ Finset.univ.erase k, ∑ j ∈ Finset.univ.erase k, F i j := by
        symm
        unfold finiteEnergy
        rw [Finset.sum_subtype (p := fun i => i ≠ k)
          (Finset.univ.erase k) (by simp)]
        apply Fintype.sum_congr
        intro i
        rw [Finset.sum_subtype (p := fun j => j ≠ k)
          (Finset.univ.erase k) (by simp)]
        apply Fintype.sum_congr
        intro j
        simp [F, Subtype.ext_iff]
  have herase (k : Fin (N + 1)) :
      (∑ i ∈ Finset.univ.erase k, ∑ j ∈ Finset.univ.erase k, F i j) =
        (∑ i, ∑ j, F i j) - (∑ j, F k j) - (∑ i, F i k) := by
    have hrow (i : Fin (N + 1)) :
        (∑ j ∈ Finset.univ.erase k, F i j) = (∑ j, F i j) - F i k := by
      linarith [Finset.sum_erase_add Finset.univ (F i) (Finset.mem_univ k)]
    simp_rw [hrow]
    rw [Finset.sum_sub_distrib]
    have houter := Finset.sum_erase_add Finset.univ
      (fun i => ∑ j, F i j) (Finset.mem_univ k)
    have hcol := Finset.sum_erase_add Finset.univ
      (fun i => F i k) (Finset.mem_univ k)
    rw [hdiag k] at hcol
    simp only [add_zero] at hcol
    linarith
  simp_rw [hdel, herase]
  unfold finiteEnergy
  simp only [F]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Finset.sum_comm]
  norm_num
  ring_nf
  rw [Finset.sum_comm]


end Problem1

namespace Riesz.Geometry

/- The public repair interfaces are proved below. -/

/-- One of the one-point deletions has energy at most their exact average.
The energy may have either sign. -/
theorem problem1_exists_energy_deletion (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (n : ℕ) (hn : 2 ≤ n) (x : Problem1.Config d (n + 1)) :
    ∃ k : Fin (n + 1),
      Problem1.finiteEnergy s (Problem1.part5_erase_configuration x k) ≤
        ((n : ℝ) - 1) / ((n : ℝ) + 1) * Problem1.finiteEnergy s x := by
  have hsum := Problem1.part5_energy_deletion_sum d hd s n hn x
  have hmean :
      (∑ _k : Fin (n + 1),
        ((n : ℝ) - 1) / ((n : ℝ) + 1) * Problem1.finiteEnergy s x) =
          ((n : ℝ) - 1) * Problem1.finiteEnergy s x := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  obtain ⟨k, _, hk⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + 1))).Nonempty)
    (hsum.le.trans hmean.ge)
  exact ⟨k, hk⟩

/-- Repeated deterministic deletion gives the exact ordered-pair survival
factor, with no sign hypothesis on the raw energy. -/
theorem problem1_exists_energy_subset (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (N : ℕ) (hN : 2 ≤ N) (M : ℕ) (hNM : N ≤ M)
    (x : Problem1.Config d M) (hx : Function.Injective x) :
    ∃ y : Problem1.Config d N, Function.Injective y ∧
      Problem1.finiteEnergy s y ≤
        Riesz.Asymptotics.pairSurvivalFactor N M * Problem1.finiteEnergy s x := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    by_cases hEq : N = M
    · subst M
      have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
      refine ⟨x, hx, ?_⟩
      simp [Riesz.Asymptotics.pairSurvivalFactor,
        show (N : ℝ) ≠ 0 by linarith, show (N : ℝ) - 1 ≠ 0 by linarith]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show M ≠ 0 by omega)
      obtain ⟨k, hk⟩ := problem1_exists_energy_deletion d hd s m (by omega) x
      obtain ⟨y, hy, hEy⟩ := ih m (Nat.lt_succ_self m) (by omega)
        (Problem1.part5_erase_configuration x k) (hx.comp k.succAbove_right_injective)
      have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
      have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have hnonneg : 0 ≤ Riesz.Asymptotics.pairSurvivalFactor N m := by
        exact div_nonneg (mul_nonneg (by positivity) (by linarith))
          (mul_nonneg (by positivity) (by linarith))
      refine ⟨y, hy, hEy.trans ((mul_le_mul_of_nonneg_left hk hnonneg).trans_eq ?_)⟩
      simp only [Riesz.Asymptotics.pairSurvivalFactor, Nat.cast_succ, add_sub_cancel_right]
      field_simp [show (m : ℝ) - 1 ≠ 0 by linarith]

/-- Greedy adjoining preserves simplicity and achieves the uniform-potential
addition cost up to any prescribed positive error. -/
theorem problem1_exists_energy_extension (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs_lower : -2 < s) (hsd : s < (d : ℝ)) (M k : ℕ)
    (x : Problem1.Config d M) (hx : Function.Injective x) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : Problem1.Config d (M + k), Function.Injective y ∧
      Problem1.finiteEnergy s y < Problem1.finiteEnergy s x +
        Problem1.continuousEnergy d s *
          (((M + k : ℕ) : ℝ) * (((M + k : ℕ) : ℝ) - 1) -
            (M : ℝ) * ((M : ℝ) - 1)) + ε := by
  induction k generalizing ε with
  | zero => exact ⟨x, hx, by simpa using lt_add_of_pos_right (Problem1.finiteEnergy s x) hε⟩
  | succ k ih =>
      obtain ⟨y, hy, hEy⟩ := ih (ε / 2) (by linarith)
      obtain ⟨z, hz, hUz⟩ := Problem1.part5_potential_near_minimizer d hd s (M + k) y
        (ε / 4) (by linarith)
      have hP := Problem1.part5_polarization_average d hd s hs_lower hsd (M + k) y
      refine ⟨Problem1.part5_adjoined_configuration z y,
        Problem1.part5_adjoining_injective d hd (M + k) y hy z hz, ?_⟩
      rw [Problem1.part5_energy_adjoining d hd s (M + k) z y]
      simp only [Nat.cast_add, Nat.cast_one] at hEy hP ⊢
      nlinarith only [hEy, hUz, hP]

/-- The exact Showcase infimum is bounded above by every configuration energy. -/
theorem positive_sphere_optimalEnergy_le (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (N : ℕ) (x : SphereConfiguration d N) :
    E_K d s N ≤ Riesz.Energy.kernelEnergy d s N x := by
  refine csInf_le ⟨V_K d s * (N : ℝ) ^ 2 - Problem1.part5_energy_constants_positive d s *
    (N : ℝ) ^ (1 + s / (d : ℝ)), ?_⟩ ⟨x, rfl⟩
  rintro _ ⟨y, rfl⟩
  exact positive_sphere_kernelEnergy_lower d hd s hs hsd N y

/-- Transport a retained configuration directly into the exact Showcase infimum. -/
theorem positive_sphere_optimalEnergy_le_problem1 (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (N : ℕ) (x : Problem1.Config d N)
    (hx : Function.Injective x) : E_K d s N ≤ Problem1.finiteEnergy s x := by
  let y : SphereConfiguration d N := ⟨fun i => (problem1SphereEquiv d).symm (x i),
    (problem1SphereEquiv d).symm.injective.comp hx⟩
  simpa only [y, Equiv.apply_symm_apply] using
    (positive_sphere_optimalEnergy_le d hd s hs hsd N y).trans_eq
      (problem1FiniteEnergy_eq d N s hs.ne' y).symm

/-- Underfull inputs admit the exact uniform-potential addition bound on the
Showcase optimal value, without a measurable choice of added points. -/
theorem positive_sphere_underCount_bound (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (N M : ℕ) (hMN : M ≤ N)
    (x : SphereConfiguration d M) :
    E_K d s N ≤ Riesz.Energy.kernelEnergy d s M x + V_K d s *
      ((N : ℝ) * ((N : ℝ) - 1) - (M : ℝ) * ((M : ℝ) - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hMN
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨y, hy, hEy⟩ := problem1_exists_energy_extension d hd s (by linarith) hsd M k
    (fun i => problem1SphereEquiv d (x.val i))
    ((problem1SphereEquiv d).injective.comp x.property) ε hε
  simpa only [problem1ContinuousEnergy_eq d hd s hsd hs.ne',
    problem1FiniteEnergy_eq d M s hs.ne' x] using
    (positive_sphere_optimalEnergy_le_problem1 d hd s hs hsd (M + k) y hy).trans_lt hEy

/-- Centering the greedy undercount bound gives the favorable linear correction. -/
theorem positive_sphere_underCount_centered_bound (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (N M : ℕ) (hMN : M ≤ N)
    (x : SphereConfiguration d M) :
    E_K d s N - V_K d s * (N : ℝ) ^ 2 ≤
      (Riesz.Energy.kernelEnergy d s M x - V_K d s * (M : ℝ) ^ 2) -
        V_K d s * ((N : ℝ) - (M : ℝ)) := by
  nlinarith only [positive_sphere_underCount_bound d hd s hs hsd N M hMN x]

/-- Deterministic deletion bounds the exact Showcase optimum by the ordered-pair
survival factor of any overfull input. -/
theorem positive_sphere_overCount_bound (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (x : SphereConfiguration d M) :
    E_K d s N ≤ Riesz.Asymptotics.pairSurvivalFactor N M *
      Riesz.Energy.kernelEnergy d s M x := by
  obtain ⟨y, hy, hEy⟩ := problem1_exists_energy_subset d hd s N hN M hNM
    (fun i => problem1SphereEquiv d (x.val i))
    ((problem1SphereEquiv d).injective.comp x.property)
  simpa only [problem1FiniteEnergy_eq d M s hs.ne' x] using
    (positive_sphere_optimalEnergy_le_problem1 d hd s hs hsd N y hy).trans hEy

/-- The adverse centered-energy cost of deleting excess points is controlled
by the already verified universal spherical lower bound. -/
theorem positive_sphere_overCount_centered_bound (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (N M : ℕ) (hN : 2 ≤ N) (hNM : N < M)
    (x : SphereConfiguration d M) :
    E_K d s N - V_K d s * (N : ℝ) ^ 2 ≤
      Riesz.Energy.kernelEnergy d s M x - V_K d s * (M : ℝ) ^ 2 +
        2 * Problem1.part5_energy_constants_positive d s *
          ((M : ℝ) - (N : ℝ)) * (M : ℝ) ^ (s / (d : ℝ)) := by
  have hfirst := sub_le_sub_right
    (positive_sphere_overCount_bound d hd s hs hsd N M hN hNM.le x)
    (V_K d s * (N : ℝ) ^ 2)
  rw [Riesz.Asymptotics.overCount_centered_identity N M (V_K d s)
    (Riesz.Energy.kernelEnergy d s M x) (by omega)] at hfirst
  have hD : -Problem1.part5_energy_constants_positive d s *
      (M : ℝ) ^ (1 + s / (d : ℝ)) ≤
        Riesz.Energy.kernelEnergy d s M x - V_K d s * (M : ℝ) ^ 2 := by
    linarith only [positive_sphere_kernelEnergy_lower d hd s hs hsd M x]
  have hbound := Riesz.Asymptotics.overCount_adverse_bound N M (1 + s / (d : ℝ))
    (Problem1.part5_energy_constants_positive d s) (V_K d s)
    (Riesz.Energy.kernelEnergy d s M x - V_K d s * (M : ℝ) ^ 2) (by omega) hNM
    ((Problem1.part5_energy_constant_signs d hd).1 s hs hsd).le
    (Riesz.Asymptotics.positiveExponent_background_pos d s (by omega) hs hsd).le hD
  simpa only [add_sub_cancel_left] using hfirst.trans hbound

/-- Main-facing count repair: the exact optimal `N`-point centered energy is
bounded pointwise by the input energy and a scalar count error. This can be
integrated without constructing a law of repaired configurations. -/
theorem positive_sphere_count_repair_bound (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (N M : ℕ) (hN : 2 ≤ N)
    (x : SphereConfiguration d M) :
    E_K d s N - V_K d s * (N : ℝ) ^ 2 ≤
      Riesz.Energy.kernelEnergy d s M x - V_K d s * (M : ℝ) ^ 2 +
        2 * Problem1.part5_energy_constants_positive d s *
          max ((M : ℝ) - (N : ℝ)) 0 * (M : ℝ) ^ (s / (d : ℝ)) := by
  by_cases hNM : N < M
  · simpa only [max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr hNM.le))] using
      positive_sphere_overCount_centered_bound d hd s hs hsd N M hN hNM x
  · have hunder := positive_sphere_underCount_centered_bound d hd s hs hsd N M
      (Nat.le_of_not_gt hNM) x
    have hcorrection : 0 ≤ V_K d s * ((N : ℝ) - (M : ℝ)) :=
      mul_nonneg (Riesz.Asymptotics.positiveExponent_background_pos d s (by omega) hs hsd).le
        (sub_nonneg.mpr (Nat.cast_le.mpr (Nat.le_of_not_gt hNM)))
    simpa only [max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr (Nat.le_of_not_gt hNM))),
      mul_zero, zero_mul, add_zero] using hunder.trans (sub_le_self _ hcorrection)

/-- The same pointwise bound in the radius-`R` normalization used by the
positive patch construction. In particular take `R = sphericalRadius d N`. -/
theorem positive_sphere_scaled_count_repair_bound (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (N M : ℕ) (hN : 2 ≤ N)
    (R : ℝ) (hR : 0 < R) (x : SphereConfiguration d M) :
    R ^ (-s) * (E_K d s N - V_K d s * (N : ℝ) ^ 2) ≤
      R ^ (-s) * Riesz.Energy.kernelEnergy d s M x -
        (R ^ (-s) * V_K d s) * (M : ℝ) ^ 2 +
          2 * Problem1.part5_energy_constants_positive d s * R ^ (-s) *
            max ((M : ℝ) - (N : ℝ)) 0 * (M : ℝ) ^ (s / (d : ℝ)) := by
  nlinarith only [mul_le_mul_of_nonneg_left
    (positive_sphere_count_repair_bound d hd s hs hsd N M hN x)
    (Real.rpow_nonneg hR.le (-s))]

end Riesz.Geometry
