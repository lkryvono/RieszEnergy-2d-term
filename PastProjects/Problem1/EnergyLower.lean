import Riesz.PastProjects.Problem1.Gamma

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators Topology

universe u

namespace Problem1

/- lem:unequal-pair-count -/
theorem part5_unequal_pair_count (M : ℕ) :
  ((Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.1 ≠ p.2)).card = M * (M - 1) ∧
  ((((Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.1 ≠ p.2)).card : ℕ) : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
  have hset : (Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.1 ≠ p.2) =
      (Finset.univ : Finset (Fin M)).offDiag :=
    Finset.ext (fun p => by simp)
  cases M
  all_goals simp only [hset, offDiagonal_card]
  all_goals simp

/- lem:near-infimum -/
theorem part5_near_infimum (A : Set ℝ) (hA : A.Nonempty) (hB : BddBelow A) (ε : ℝ) (hε : 0 < ε) :
  ∃ a ∈ A, a < sInf A + ε := by
  exact Real.lt_sInf_add_pos hA hε

/- lem:potential-near-minimizer -/
theorem part5_potential_near_minimizer (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (N : ℕ) (ω : Config d N) (ε : ℝ) (hε : 0 < ε) :
  ∃ x : Sphere d, x ∉ siteSet ω ∧ potential s ω x < configPolarization s ω + ε := by
  obtain ⟨a, ⟨x, hx, rfl⟩, ha⟩ := part5_near_infimum (potentialValueSet s ω)
    (potentialValueSet_nonempty d hd N s ω) (potentialValueSet_bddBelow d N s ω).2 ε hε
  exact ⟨x, hx, ha⟩

/- lem:energy-order-interface -/
theorem part5_energy_order_interface (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (M : ℕ) :
  (energyValueSet d s M).Nonempty ∧ BddBelow (energyValueSet d s M) ∧
  (∀ z : Config d M, Function.Injective z → minEnergy d s M ≤ finiteEnergy s z) ∧
  (∀ ε : ℝ, 0 < ε → ∃ z : Config d M, Function.Injective z ∧ finiteEnergy s z < minEnergy d s M + ε) := by
  refine ⟨energyValueSet_nonempty d hd M s, (energyValueSet_bddBelow d M s).2, ?_, ?_⟩
  · exact fun z hz => csInf_le (energyValueSet_bddBelow d M s).2 ⟨⟨z, hz⟩, rfl⟩
  · intro ε hε
    obtain ⟨a, ⟨z, rfl⟩, ha⟩ := part5_near_infimum (energyValueSet d s M)
      (energyValueSet_nonempty d hd M s) (energyValueSet_bddBelow d M s).2 ε hε
    exact ⟨z.1, z.2, ha⟩

/- lem:null-sites -/
theorem part5_null_sites (d : ℕ) (hd : 2 ≤ d) (N : ℕ) (ω : Config d N) :
  sigma d (siteSet ω) = 0 := by
  letI : NullSingletonClass (sigma d) := sphere_nullSingletonClass d hd
  exact (Set.finite_range ω).measure_zero (sigma d)

/- lem:potential-integral -/
theorem part5_potential_integral (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hsLower : -2 < s) (hsUpper : s < (d : ℝ)) (N : ℕ) (ω : Config d N) :
  Integrable (potential s ω) (sigma d) ∧ (∫ x, potential s ω x ∂sigma d) = (N : ℝ) * continuousEnergy d s := by
  have hsym : potential s ω = (fun x => ∑ j : Fin N, kernel d s (ω j) x) :=
    funext (fun x => Finset.sum_congr rfl (fun j _ => kernel_symmetry d s x (ω j)))
  have hi (j : Fin N) : Integrable (kernel d s (ω j)) (sigma d) :=
    kernel_section_integrable d hd s hsUpper (ω j)
  rw [hsym]
  refine ⟨integrable_finsetSum Finset.univ (fun j _ => hi j), ?_⟩
  rw [integral_finsetSum Finset.univ (fun j _ => hi j)]
  simp [continuous_energy_center d hd s hsUpper, nsmul_eq_mul]

/- lem:polarization-average -/
theorem part5_polarization_average (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hsLower : -2 < s) (hsUpper : s < (d : ℝ)) (N : ℕ) (ω : Config d N) :
  configPolarization s ω ≤ (N : ℝ) * continuousEnergy d s := by
  have hsites : ∀ᵐ x ∂sigma d, x ∉ siteSet ω :=
    measure_eq_zero_iff_ae_notMem.1 (part5_null_sites d hd N ω)
  have hle : ∀ᵐ x ∂sigma d, configPolarization s ω ≤ potential s ω x :=
    hsites.mono (fun x hx => (potential_infimum d hd N s ω).2 x hx)
  have hIntegral := integral_mono_ae
    (integrable_const (μ := sigma d) (configPolarization s ω))
    (part5_potential_integral d hd s hsLower hsUpper N ω).1 hle
  simpa [(part5_potential_integral d hd s hsLower hsUpper N ω).2] using hIntegral

/- cor:polarization-value-set-bddAbove -/
theorem part5_polarization_value_set_bddAbove (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hsLower : -2 < s) (hsUpper : s < (d : ℝ)) (N : ℕ) :
  (polarizationValueSet d s N).Nonempty ∧
  ((N : ℝ) * continuousEnergy d s ∈ upperBounds (polarizationValueSet d s N)) ∧
  BddAbove (polarizationValueSet d s N) ∧
  (∀ ω : Config d N, configPolarization s ω ≤ maxPolarization d s N) ∧
  (∀ B : ℝ, (∀ ω : Config d N, configPolarization s ω ≤ B) → maxPolarization d s N ≤ B) := by
  have hupper : (N : ℝ) * continuousEnergy d s ∈ upperBounds (polarizationValueSet d s N) :=
    fun a ⟨ω, hω⟩ => hω.trans_le (part5_polarization_average d hd s hsLower hsUpper N ω)
  exact ⟨polarizationValueSet_nonempty d N s, hupper, ⟨_, hupper⟩,
    fun ω => le_csSup ⟨_, hupper⟩ ⟨ω, rfl⟩,
    fun B hB => csSup_le (polarizationValueSet_nonempty d N s)
      (fun a ⟨ω, hω⟩ => hω.trans_le (hB ω))⟩

/- lem:energy-small -/
theorem part5_energy_small (d : ℕ) (hd : 2 ≤ d) (s : ℝ) :
  minEnergy d s 0 = 0 ∧ minEnergy d s 1 = 0 ∧
  (∀ ω : Config d 0, configPolarization s ω = 0) ∧ maxPolarization d s 0 = 0 := by
  have hpotential (ω : Config d 0) : potentialValueSet s ω = {0} :=
    Set.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨potentialValueSet_nonempty d hd 0 s ω,
        fun a ⟨x, hx, ha⟩ => ha.trans (by simp [potential])⟩
  have hconfig (ω : Config d 0) : configPolarization s ω = 0 := by
    simp [configPolarization, hpotential ω]
  have hvalues : polarizationValueSet d s 0 = {0} :=
    Set.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨polarizationValueSet_nonempty d 0 s, fun a ⟨ω, ha⟩ => ha.trans (hconfig ω)⟩
  exact ⟨(minEnergy_small d s).1, (minEnergy_small d s).2, hconfig,
    by simp [maxPolarization, hvalues]⟩

/- lem:Pi-multiplication -/
/- def:multi-index -/
abbrev part5_multi_index (d : ℕ) :
  Type := by
  classical
  exact (
    Fin (d + 1) → ℕ
  )

/- def:multi-index -/
def part5_multi_index_degree {d : ℕ} (α : part5_multi_index d) :
  ℕ := by
  classical
  exact (
    ∑ r : Fin (d + 1), α r
  )

/- def:multi-index -/
def part5_multi_index_factorial {d : ℕ} (α : part5_multi_index d) :
  ℕ := by
  classical
  exact (
    ∏ r : Fin (d + 1), Nat.factorial (α r)
  )

/- def:multi-index -/
noncomputable def part5_multi_index_monomial {d : ℕ} (α : part5_multi_index d) (x : Sphere d) :
  ℝ := by
  classical
  exact (
    ∏ r : Fin (d + 1), (x : Euclidean d) r ^ α r
  )

/- def:multi-index -/
noncomputable def part5_multi_index_shell (d n : ℕ) :
  Finset (part5_multi_index d) := by
  classical
  exact (
    Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n
  )

/- def:multi-index -/
theorem part5_multi_index_shell_mem (d n : ℕ) (α : part5_multi_index d) :
  α ∈ part5_multi_index_shell d n ↔ part5_multi_index_degree α = n := by
  simp [part5_multi_index_shell, Finset.mem_piAntidiag, part5_multi_index_degree]

/- lem:shell-finite -/
theorem part5_shell_finite (d n : ℕ) :
  Set.Finite {α : part5_multi_index d | part5_multi_index_degree α = n} ∧ (∀ α : part5_multi_index d, 0 < (part5_multi_index_factorial α : ℝ)) ∧ ∀ t : ℝ, 0 ≤ t → ∀ α : part5_multi_index d, 0 ≤ (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) := by
  have hfac (α : part5_multi_index d) : 0 < (part5_multi_index_factorial α : ℝ) :=
    Nat.cast_pos.mpr (Nat.prod_factorial_pos Finset.univ α)
  refine ⟨?_, hfac, fun t ht α => div_nonneg
    (pow_nonneg (mul_nonneg (by norm_num) ht) n) (hfac α).le⟩
  exact (part5_multi_index_shell d n).finite_toSet.subset
    (fun α hα => (part5_multi_index_shell_mem d n α).mpr hα)

/- lem:monomial-bound -/
theorem part5_monomial_bound (d : ℕ) (hd : 2 ≤ d) (α : part5_multi_index d) :
  Continuous (part5_multi_index_monomial α) ∧ (∀ x : Sphere d, |part5_multi_index_monomial α x| ≤ 1) ∧ Integrable (part5_multi_index_monomial α) (sigma d) := by
  have hcont : Continuous (part5_multi_index_monomial α) :=
    continuous_finsetProd Finset.univ (fun r _ =>
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin (d + 1) => ℝ) r).comp
        continuous_subtype_val).pow (α r))
  refine ⟨hcont, ?_, continuous_sphere_integrable d ⟨_, hcont⟩⟩
  intro x
  have hcoord (r : Fin (d + 1)) : |(x : Euclidean d) r| ≤ 1 := by
    simpa only [Real.norm_eq_abs, unitSphereN_norm] using PiLp.norm_apply_le (x : Euclidean d) r
  simp only [part5_multi_index_monomial, Finset.abs_prod, abs_pow]
  exact Finset.prod_le_one (fun r _ => pow_nonneg (abs_nonneg _) (α r))
    (fun r _ => pow_le_one₀ (abs_nonneg _) (hcoord r))

/- lem:multinomial-shell -/
theorem part5_multinomial_shell (d n : ℕ) (z : Fin (d + 1) → ℝ) :
  (∑ α ∈ part5_multi_index_shell d n, (∏ r : Fin (d + 1), z r ^ α r) / (part5_multi_index_factorial α : ℝ)) = (∑ r : Fin (d + 1), z r) ^ n / (Nat.factorial n : ℝ) := by
  have hn : (Nat.factorial n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos n))
  rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro α hα
  have hdegree := (part5_multi_index_shell_mem d n α).mp hα
  have hspec : (part5_multi_index_factorial α : ℝ) * (Nat.multinomial Finset.univ α : ℝ) =
      (Nat.factorial n : ℝ) := by
    exact_mod_cast (Nat.multinomial_spec Finset.univ α).trans (congrArg Nat.factorial hdegree)
  apply (div_eq_div_iff ((part5_shell_finite d n).2.1 α).ne' hn).mpr
  rw [← hspec]
  ring

/- def:gaussian-shell -/
noncomputable def part5_gaussian_shell {d : ℕ} (t : ℝ) (n : ℕ) (x y : Sphere d) :
  ℝ := by
  classical
  exact (
    ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n * part5_multi_index_monomial α x * part5_multi_index_monomial α y / (part5_multi_index_factorial α : ℝ)
  )

/- def:gaussian-shell -/
def part5_gaussian_shell_scalar_majorant (t : ℝ) (n : ℕ) :
  ℝ := by
  classical
  exact (
    (2 * t) ^ n / (Nat.factorial n : ℝ)
  )

/- lem:gaussian-shell-finite -/
theorem part5_gaussian_shell_finite (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (n : ℕ) (x y : Sphere d) :
  part5_gaussian_shell t n x y = (2 * t) ^ n * (inner ℝ (x : Euclidean d) (y : Euclidean d)) ^ n / (Nat.factorial n : ℝ) := by
  have h := congrArg (fun a : ℝ => (2 * t) ^ n * a)
    (part5_multinomial_shell d n (fun r => (x : Euclidean d) r * (y : Euclidean d) r))
  simpa only [part5_gaussian_shell, part5_multi_index_monomial,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, mul_pow,
    Finset.prod_mul_distrib, Finset.mul_sum, mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using h

/- lem:gaussian-shell-majorant -/
theorem part5_gaussian_shell_majorant (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (x y : Sphere d) :
  (∑ α ∈ part5_multi_index_shell d n, |(2 * t) ^ n * part5_multi_index_monomial α x * part5_multi_index_monomial α y / (part5_multi_index_factorial α : ℝ)|) ≤ part5_gaussian_shell_scalar_majorant t n ∧ |part5_gaussian_shell t n x y| ≤ part5_gaussian_shell_scalar_majorant t n := by
  have ht2 : 0 ≤ 2 * t := mul_nonneg (by norm_num) ht
  have hcs : (∑ r : Fin (d + 1), |(x : Euclidean d) r| * |(y : Euclidean d) r|) ^ 2 ≤ 1 := by
    simpa only [sq_abs, ← EuclideanSpace.real_norm_sq_eq, unitSphereN_norm, one_pow, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun r => |(x : Euclidean d) r|)
        (fun r => |(y : Euclidean d) r|)
  have hsum : 0 ≤ (∑ r : Fin (d + 1), |(x : Euclidean d) r| * |(y : Euclidean d) r|) ∧
      (∑ r : Fin (d + 1), |(x : Euclidean d) r| * |(y : Euclidean d) r|) ≤ 1 :=
    ⟨Finset.sum_nonneg (fun r _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)), by nlinarith [hcs]⟩
  have hcoef : 0 ≤ part5_gaussian_shell_scalar_majorant t n :=
    div_nonneg (pow_nonneg ht2 n) (Nat.cast_nonneg _)
  have habs : (∑ α ∈ part5_multi_index_shell d n,
      |(2 * t) ^ n * part5_multi_index_monomial α x * part5_multi_index_monomial α y /
        (part5_multi_index_factorial α : ℝ)|) = part5_gaussian_shell_scalar_majorant t n *
      (∑ r : Fin (d + 1), |(x : Euclidean d) r| * |(y : Euclidean d) r|) ^ n := by
    simpa only [part5_multi_index_monomial, part5_gaussian_shell_scalar_majorant,
      abs_div, abs_inv, abs_mul, abs_pow, Finset.abs_prod, Nat.abs_cast, abs_of_nonneg ht2,
      abs_of_nonneg ht, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_pow,
      Finset.prod_mul_distrib, Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun a : ℝ => (2 * t) ^ n * a)
        (part5_multinomial_shell d n (fun r => |(x : Euclidean d) r| * |(y : Euclidean d) r|))
  have hbound := habs.trans_le ((mul_le_mul_of_nonneg_left
    (pow_le_one₀ (n := n) hsum.1 hsum.2) hcoef).trans_eq (mul_one _))
  exact ⟨hbound, (Finset.abs_sum_le_sum_abs _ _).trans hbound⟩

/- lem:gaussian-shell-hasSum -/
theorem part5_gaussian_shell_hasSum (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (ht : 0 ≤ t) :
  HasSum (part5_gaussian_shell_scalar_majorant t) (Real.exp (2 * t)) ∧ (∀ x y : Sphere d, HasSum (fun n : ℕ => part5_gaussian_shell t n x y) (Real.exp (2 * t * inner ℝ (x : Euclidean d) (y : Euclidean d))) ∧ Summable (fun n : ℕ => |part5_gaussian_shell t n x y|)) ∧ HasSumUniformlyOn (fun (n : ℕ) (p : Sphere d × Sphere d) => part5_gaussian_shell t n p.1 p.2) (fun p => Real.exp (2 * t * inner ℝ (p.1 : Euclidean d) (p.2 : Euclidean d))) Set.univ ∧ HasSumUniformlyOn (fun (n : ℕ) (p : Sphere d × Sphere d) => |part5_gaussian_shell t n p.1 p.2|) (fun p => ∑' n : ℕ, |part5_gaussian_shell t n p.1 p.2|) Set.univ ∧ (∀ (R : ℕ) (x y : Sphere d), |Real.exp (2 * t * inner ℝ (x : Euclidean d) (y : Euclidean d)) - ∑ n ∈ Finset.range (R + 1), part5_gaussian_shell t n x y| ≤ (∑' n : ℕ, if R < n then part5_gaussian_shell_scalar_majorant t n else 0)) ∧ Filter.Tendsto (fun R : ℕ => (∑' n : ℕ, if R < n then part5_gaussian_shell_scalar_majorant t n else 0)) Filter.atTop (nhds (0 : ℝ)) := by
  have ha : HasSum (part5_gaussian_shell_scalar_majorant t) (Real.exp (2 * t)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (2 * t)
  have hp (x y : Sphere d) : HasSum (fun n : ℕ => part5_gaussian_shell t n x y)
      (Real.exp (2 * t * inner ℝ (x : Euclidean d) (y : Euclidean d))) := by
    simp only [part5_gaussian_shell_finite d hd t, Real.exp_eq_exp_ℝ, ← mul_pow]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have habs (x y : Sphere d) : Summable (fun n : ℕ => |part5_gaussian_shell t n x y|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _)
      (fun n => (part5_gaussian_shell_majorant d hd t ht n x y).2) ha.summable
  have hb (n : ℕ) (p : Sphere d × Sphere d) : ‖part5_gaussian_shell t n p.1 p.2‖ ≤
      part5_gaussian_shell_scalar_majorant t n :=
    (part5_gaussian_shell_majorant d hd t ht n p.1 p.2).2
  have hu : HasSumUniformlyOn (fun (n : ℕ) (p : Sphere d × Sphere d) => part5_gaussian_shell t n p.1 p.2)
      (fun p => Real.exp (2 * t * inner ℝ (p.1 : Euclidean d) (p.2 : Euclidean d))) Set.univ :=
    (HasSumUniformlyOn.of_norm_le_summable ha.summable (fun n p _ => hb n p)).congr_right
      (fun p _ => (hp p.1 p.2).tsum_eq)
  have hua : HasSumUniformlyOn (fun (n : ℕ) (p : Sphere d × Sphere d) => |part5_gaussian_shell t n p.1 p.2|)
      (fun p => ∑' n : ℕ, |part5_gaussian_shell t n p.1 p.2|) Set.univ :=
    HasSumUniformlyOn.of_norm_le_summable ha.summable (fun n p _ => by
      simpa only [Real.norm_eq_abs, abs_abs] using hb n p)
  refine ⟨ha, fun x y => ⟨hp x y, habs x y⟩, hu, hua, ?_⟩
  have htailEq (R : ℕ) : (∑' n : {n : ℕ // n ∉ Finset.range (R + 1)},
      part5_gaussian_shell_scalar_majorant t n) =
      ∑' n : ℕ, if R < n then part5_gaussian_shell_scalar_majorant t n else 0 := by
    refine (tsum_subtype {n : ℕ | n ∉ Finset.range (R + 1)}
      (part5_gaussian_shell_scalar_majorant t)).trans ?_
    simp only [Set.indicator, Set.mem_setOf_eq, Finset.mem_range, not_lt, Nat.add_one_le_iff]
  have hlim : Tendsto (fun R : ℕ => ∑' n : ℕ,
      if R < n then part5_gaussian_shell_scalar_majorant t n else 0) atTop (nhds (0 : ℝ)) := by
    simp only [← htailEq]
    exact (tendsto_tsum_compl_atTop_zero (part5_gaussian_shell_scalar_majorant t)).comp
      (Filter.tendsto_finset_range.comp (Filter.tendsto_add_atTop_nat 1))
  refine ⟨?_, hlim⟩
  intro R x y
  have hsplit := (hp x y).summable.sum_add_tsum_subtype_compl (Finset.range (R + 1))
  have hrest : Real.exp (2 * t * inner ℝ (x : Euclidean d) (y : Euclidean d)) -
      ∑ n ∈ Finset.range (R + 1), part5_gaussian_shell t n x y =
      ∑' n : {n : ℕ // n ∉ Finset.range (R + 1)}, part5_gaussian_shell t n x y := by
    linarith [(hp x y).tsum_eq]
  rw [hrest, ← htailEq R]
  exact tsum_of_norm_bounded (ha.summable.subtype (fun n => n ∉ Finset.range (R + 1))).hasSum
    (fun n => hb n.1 (x, y))

/- def:gaussian-moment-coefficients -/
noncomputable def part5_gaussian_moment_coefficients_continuum {d : ℕ} (α : part5_multi_index d) :
  ℝ := by
  classical
  exact (
    ∫ y : Sphere d, part5_multi_index_monomial α y ∂sigma d
  )

/- def:gaussian-moment-coefficients -/
noncomputable def part5_gaussian_moment_coefficients_empirical {d M : ℕ} (x : Config d M) (α : part5_multi_index d) :
  ℝ := by
  classical
  exact (
    ∑ i : Fin M, part5_multi_index_monomial α (x i)
  )

/- lem:gaussian-coefficient-bounds -/
theorem part5_gaussian_coefficient_bounds (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (x : Config d M) (α : part5_multi_index d) :
  |part5_gaussian_moment_coefficients_continuum α| ≤ 1 ∧ |part5_gaussian_moment_coefficients_empirical x α| ≤ (M : ℝ) ∧ |part5_gaussian_moment_coefficients_empirical x α - (M : ℝ) * part5_gaussian_moment_coefficients_continuum α| ≤ 2 * (M : ℝ) := by
  have hmon := (part5_monomial_bound d hd α).2.1
  have hm : |part5_gaussian_moment_coefficients_continuum α| ≤ 1 := by
    simpa [part5_gaussian_moment_coefficients_continuum, Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const (μ := sigma d) (f := part5_multi_index_monomial α)
        (C := (1 : ℝ)) (Filter.Eventually.of_forall hmon))
  have hsum : (∑ i : Fin M, |part5_multi_index_monomial α (x i)|) ≤ (M : ℝ) := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) (g := fun _ : Fin M => (1 : ℝ))
      (fun i _ => hmon (x i)))
  have he : |part5_gaussian_moment_coefficients_empirical x α| ≤ (M : ℝ) :=
    (Finset.abs_sum_le_sum_abs _ _).trans hsum
  have hc : |(M : ℝ) * part5_gaussian_moment_coefficients_continuum α| ≤ (M : ℝ) := by
    simpa [abs_mul, Nat.abs_cast] using (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg M : (0 : ℝ) ≤ M))
  refine ⟨hm, he, abs_le.mpr ⟨?_, ?_⟩⟩
  all_goals linarith [(abs_le.mp he).1, (abs_le.mp he).2, (abs_le.mp hc).1, (abs_le.mp hc).2]

/- lem:gaussian-factorization -/
theorem part5_gaussian_factorization (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (x y : Sphere d) :
  Real.exp (-t * dist x y ^ 2) = Real.exp (-2 * t) * Real.exp (2 * t * inner ℝ (x : Euclidean d) (y : Euclidean d)) := by
  rw [sphere_dist_sq, sphereCoordinate, ← Real.exp_add]
  congr 1 <;> ring

/- lem:integrate-shell-series -/
theorem part5_integrate_shell_series {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ) (b : ℕ → ℝ) (hf : ∀ n : ℕ, Integrable (f n) μ) (hb : ∀ n : ℕ, 0 ≤ b n) (hsum : Summable b) (hbound : ∀ n : ℕ, ∀ᵐ x ∂μ, |f n x| ≤ b n) :
  Summable (fun n : ℕ => ∫ x, |f n x| ∂μ) ∧ Summable (fun n : ℕ => |∫ x, f n x ∂μ|) ∧ (∀ᵐ x ∂μ, Summable (fun n : ℕ => |f n x|)) ∧ Integrable (fun x => ∑' n : ℕ, f n x) μ ∧ (∫ x, (∑' n : ℕ, f n x) ∂μ) = ∑' n : ℕ, ∫ x, f n x ∂μ := by
  have hIbound (n : ℕ) : (∫ x, |f n x| ∂μ) ≤ b n := by
    simpa using (integral_mono_ae (hf n).abs (integrable_const (b n)) (hbound n))
  have hIabs : Summable (fun n : ℕ => ∫ x, |f n x| ∂μ) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => abs_nonneg (f n x))) hIbound hsum
  have hAbsI : Summable (fun n : ℕ => |∫ x, f n x ∂μ|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => abs_integral_le_integral_abs) hIabs
  have hcommon : ∀ᵐ x ∂μ, ∀ n : ℕ, |f n x| ≤ b n := ae_all_iff.mpr hbound
  have hpoint : ∀ᵐ x ∂μ, Summable (fun n : ℕ => |f n x|) :=
    hcommon.mono (fun x hx => Summable.of_nonneg_of_le (fun n => abs_nonneg _) hx hsum)
  have hmeas : AEStronglyMeasurable (fun x => ∑' n : ℕ, f n x) μ :=
    AEStronglyMeasurable.tsum (fun n => (hf n).aestronglyMeasurable)
  have hint : Integrable (fun x => ∑' n : ℕ, f n x) μ :=
    (integrable_const (∑' n : ℕ, b n)).mono' hmeas
      (hcommon.mono (fun x hx => tsum_of_norm_bounded hsum.hasSum hx))
  exact ⟨hIabs, hAbsI, hpoint, hint,
    (hasSum_integral_of_summable_integral_norm hf hIabs).tsum_eq.symm⟩

/- lem:gaussian-empirical-series -/
theorem part5_gaussian_empirical_series (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (x : Config d M) (t : ℝ) (ht : 0 ≤ t) :
  (∑ i : Fin M, ∑ j : Fin M, Real.exp (-t * dist (x i) (x j) ^ 2)) = Real.exp (-2 * t) * (∑' n : ℕ, ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * (part5_gaussian_moment_coefficients_empirical x α) ^ 2) ∧ Summable (fun n : ℕ => |∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * (part5_gaussian_moment_coefficients_empirical x α) ^ 2|) := by
  have hshell := part5_gaussian_shell_hasSum d hd t ht
  have hrow (n : ℕ) (i : Fin M) : |∑ j : Fin M, part5_gaussian_shell t n (x i) (x j)| ≤
      (M : ℝ) * part5_gaussian_shell_scalar_majorant t n := by
    calc
      _ ≤ ∑ j : Fin M, |part5_gaussian_shell t n (x i) (x j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin M, part5_gaussian_shell_scalar_majorant t n :=
        Finset.sum_le_sum (fun j _ => (part5_gaussian_shell_majorant d hd t ht n (x i) (x j)).2)
      _ = _ := by simp
  have hpairbound (n : ℕ) : |∑ i : Fin M, ∑ j : Fin M, part5_gaussian_shell t n (x i) (x j)| ≤
      (M : ℝ) ^ 2 * part5_gaussian_shell_scalar_majorant t n := by
    calc
      _ ≤ ∑ i : Fin M, |∑ j : Fin M, part5_gaussian_shell t n (x i) (x j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin M, (M : ℝ) * part5_gaussian_shell_scalar_majorant t n :=
        Finset.sum_le_sum (fun i _ => hrow n i)
      _ = _ := by simp [pow_two, mul_assoc]
  have habs : Summable (fun n : ℕ => |∑ i : Fin M, ∑ j : Fin M, part5_gaussian_shell t n (x i) (x j)|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpairbound (hshell.1.summable.mul_left ((M : ℝ) ^ 2))
  have hpairs : HasSum (fun n : ℕ => ∑ i : Fin M, ∑ j : Fin M, part5_gaussian_shell t n (x i) (x j))
      (∑ i : Fin M, ∑ j : Fin M, Real.exp (2 * t * inner ℝ (x i : Euclidean d) (x j : Euclidean d))) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => (hshell.2.1 (x i) (x j)).1))
  have hcoeff (n : ℕ) : (∑ i : Fin M, ∑ j : Fin M, part5_gaussian_shell t n (x i) (x j)) =
      ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) *
        (part5_gaussian_moment_coefficients_empirical x α) ^ 2 := by
    simp only [part5_gaussian_shell, part5_gaussian_moment_coefficients_empirical, pow_two,
      Finset.mul_sum, Finset.sum_mul]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin M))) (t := part5_multi_index_shell d n)]
    simp only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  simp only [← hcoeff]
  refine ⟨?_, habs⟩
  simp only [hpairs.tsum_eq, part5_gaussian_factorization d hd t, Finset.mul_sum]

/- lem:gaussian-cross-series -/
theorem part5_gaussian_cross_series (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (x : Config d M) (t : ℝ) (ht : 0 ≤ t) :
  (M : ℝ) * gaussianAverage d t = Real.exp (-2 * t) * (∑' n : ℕ, ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * part5_gaussian_moment_coefficients_empirical x α * part5_gaussian_moment_coefficients_continuum α) ∧ Summable (fun n : ℕ => |∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * part5_gaussian_moment_coefficients_empirical x α * part5_gaussian_moment_coefficients_continuum α|) := by
  have hshell := part5_gaussian_shell_hasSum d hd t ht
  have hfi (z : Sphere d) (n : ℕ) : Integrable (fun y => part5_gaussian_shell t n z y) (sigma d) :=
    integrable_finsetSum _ (fun α _ =>
      ((part5_monomial_bound d hd α).2.2.const_mul ((2 * t) ^ n * part5_multi_index_monomial α z)).div_const _)
  have hseries (z : Sphere d) := part5_integrate_shell_series (sigma d)
    (fun n y => part5_gaussian_shell t n z y) (part5_gaussian_shell_scalar_majorant t) (hfi z)
    (fun n => div_nonneg (pow_nonneg (mul_nonneg (by norm_num) ht) n) (Nat.cast_nonneg _))
    hshell.1.summable (fun n => Filter.Eventually.of_forall
      (fun y => (part5_gaussian_shell_majorant d hd t ht n z y).2))
  have hpoint (z y : Sphere d) : (∑' n : ℕ, part5_gaussian_shell t n z y) =
      Real.exp (2 * t * inner ℝ (z : Euclidean d) (y : Euclidean d)) :=
    (hshell.2.1 z y).1.tsum_eq
  have hcenter (z : Sphere d) : gaussianAverage d t = Real.exp (-2 * t) *
      (∑' n : ℕ, ∫ y, part5_gaussian_shell t n z y ∂sigma d) := by
    rw [← (hseries z).2.2.2.2, ← integral_const_mul]
    simp only [hpoint, ← part5_gaussian_factorization d hd t, (gaussian_center d hd t z).2]
  have hcoeff (z : Sphere d) (n : ℕ) : (∫ y, part5_gaussian_shell t n z y ∂sigma d) =
      ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) *
        part5_multi_index_monomial α z * part5_gaussian_moment_coefficients_continuum α := by
    dsimp only [part5_gaussian_shell]
    rw [integral_finsetSum _ (fun α _ =>
      ((part5_monomial_bound d hd α).2.2.const_mul ((2 * t) ^ n * part5_multi_index_monomial α z)).div_const _)]
    simp only [integral_div, integral_const_mul, part5_gaussian_moment_coefficients_continuum,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hcollect (n : ℕ) : (∑ i : Fin M, ∫ y, part5_gaussian_shell t n (x i) y ∂sigma d) =
      ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) *
        part5_gaussian_moment_coefficients_empirical x α * part5_gaussian_moment_coefficients_continuum α := by
    simp only [hcoeff, part5_gaussian_moment_coefficients_empirical, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  have habs : Summable (fun n : ℕ => |∑ i : Fin M, ∫ y, part5_gaussian_shell t n (x i) y ∂sigma d|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => Finset.abs_sum_le_sum_abs _ _)
      (summable_sum (fun i _ => (hseries (x i)).2.1))
  have hsummable (i : Fin M) : Summable (fun n : ℕ => ∫ y, part5_gaussian_shell t n (x i) y ∂sigma d) :=
    Summable.of_norm (f := fun n : ℕ => ∫ y, part5_gaussian_shell t n (x i) y ∂sigma d)
      (hseries (x i)).2.1
  simp only [← hcollect]
  refine ⟨?_, habs⟩
  rw [Summable.tsum_finsetSum (fun i _ => hsummable i), Finset.mul_sum]
  calc
    _ = ∑ _i : Fin M, gaussianAverage d t := by simp
    _ = _ := Finset.sum_congr rfl (fun i _ => hcenter (x i))

/- lem:gaussian-continuum-series -/
theorem part5_gaussian_continuum_series (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (ht : 0 ≤ t) :
  gaussianAverage d t = Real.exp (-2 * t) * (∑' n : ℕ, ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * (part5_gaussian_moment_coefficients_continuum α) ^ 2) ∧ Summable (fun n : ℕ => |∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * (part5_gaussian_moment_coefficients_continuum α) ^ 2|) := by
  let F (n : ℕ) (z : Sphere d) : ℝ := ∑ α ∈ part5_multi_index_shell d n,
    (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * part5_multi_index_monomial α z *
      part5_gaussian_moment_coefficients_continuum α
  have hfirst (z : Sphere d) : gaussianAverage d t = Real.exp (-2 * t) * (∑' n : ℕ, F n z) := by
    simpa [F, part5_gaussian_moment_coefficients_empirical, Fin.sum_univ_one] using
      (part5_gaussian_cross_series d hd 1 (fun _ : Fin 1 => z) t ht).1
  have hcoeff (z : Sphere d) (n : ℕ) : (∫ y, part5_gaussian_shell t n z y ∂sigma d) = F n z := by
    dsimp only [part5_gaussian_shell, F]
    rw [integral_finsetSum _ (fun α _ =>
      ((part5_monomial_bound d hd α).2.2.const_mul ((2 * t) ^ n * part5_multi_index_monomial α z)).div_const _)]
    simp only [integral_div, integral_const_mul, part5_gaussian_moment_coefficients_continuum,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hbound (n : ℕ) (z : Sphere d) : |F n z| ≤ part5_gaussian_shell_scalar_majorant t n := by
    simpa [hcoeff, Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const (μ := sigma d) (f := fun y => part5_gaussian_shell t n z y)
        (Filter.Eventually.of_forall (fun y => (part5_gaussian_shell_majorant d hd t ht n z y).2)))
  have hfi (n : ℕ) : Integrable (F n) (sigma d) :=
    integrable_finsetSum _ (fun α _ =>
      ((part5_monomial_bound d hd α).2.2.const_mul ((2 * t) ^ n / (part5_multi_index_factorial α : ℝ))).mul_const
        (part5_gaussian_moment_coefficients_continuum α))
  have hseries := part5_integrate_shell_series (sigma d) F (part5_gaussian_shell_scalar_majorant t) hfi
    (fun n => div_nonneg (pow_nonneg (mul_nonneg (by norm_num) ht) n) (Nat.cast_nonneg _))
    (part5_gaussian_shell_hasSum d hd t ht).1.summable
    (fun n => Filter.Eventually.of_forall (hbound n))
  have hsecond (n : ℕ) : (∫ z, F n z ∂sigma d) =
      ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) *
        (part5_gaussian_moment_coefficients_continuum α) ^ 2 := by
    dsimp only [F]
    rw [integral_finsetSum _ (fun α _ =>
      ((part5_monomial_bound d hd α).2.2.const_mul ((2 * t) ^ n / (part5_multi_index_factorial α : ℝ))).mul_const
        (part5_gaussian_moment_coefficients_continuum α))]
    simp only [integral_mul_const, integral_const_mul, part5_gaussian_moment_coefficients_continuum,
      pow_two, mul_assoc]
  simp only [← hsecond]
  refine ⟨?_, hseries.2.1⟩
  rw [← hseries.2.2.2.2, ← integral_const_mul]
  calc
    _ = ∫ _z : Sphere d, gaussianAverage d t ∂sigma d := by simp
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hfirst)

/- def:gaussian-partial-sums -/
noncomputable def part5_gaussian_partial_sums_square_shell {d M : ℕ} (x : Config d M) (t : ℝ) (n : ℕ) :
  ℝ := by
  classical
  exact (
    ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * (part5_gaussian_moment_coefficients_empirical x α - (M : ℝ) * part5_gaussian_moment_coefficients_continuum α) ^ 2
  )

/- def:gaussian-partial-sums -/
noncomputable def part5_gaussian_partial_sums_empirical {d M : ℕ} (x : Config d M) (t : ℝ) (R : ℕ) :
  ℝ := by
  classical
  exact (
    Real.exp (-2 * t) * ∑ n ∈ Finset.range (R + 1), ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * (part5_gaussian_moment_coefficients_empirical x α) ^ 2
  )

/- def:gaussian-partial-sums -/
noncomputable def part5_gaussian_partial_sums_cross {d M : ℕ} (x : Config d M) (t : ℝ) (R : ℕ) :
  ℝ := by
  classical
  exact (
    Real.exp (-2 * t) * ∑ n ∈ Finset.range (R + 1), ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * part5_gaussian_moment_coefficients_empirical x α * part5_gaussian_moment_coefficients_continuum α
  )

/- def:gaussian-partial-sums -/
noncomputable def part5_gaussian_partial_sums_continuum (d : ℕ) (t : ℝ) (R : ℕ) :
  ℝ := by
  classical
  exact (
    Real.exp (-2 * t) * ∑ n ∈ Finset.range (R + 1), ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * (part5_gaussian_moment_coefficients_continuum α) ^ 2
  )

/- lem:gaussian-square-summable -/
theorem part5_gaussian_square_summable (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (x : Config d M) (t : ℝ) (ht : 0 ≤ t) :
  (∀ n : ℕ, 0 ≤ part5_gaussian_partial_sums_square_shell x t n ∧ part5_gaussian_partial_sums_square_shell x t n ≤ 4 * (M : ℝ) ^ 2 * (2 * t * ((d : ℝ) + 1)) ^ n / (Nat.factorial n : ℝ)) ∧ Summable (part5_gaussian_partial_sums_square_shell x t) := by
  have hc (n : ℕ) (α : part5_multi_index d) : 0 ≤ (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) :=
    (part5_shell_finite d n).2.2 t ht α
  have hdelta (α : part5_multi_index d) := (part5_gaussian_coefficient_bounds d hd M x α).2.2
  have hsq (α : part5_multi_index d) :
      (part5_gaussian_moment_coefficients_empirical x α - (M : ℝ) * part5_gaussian_moment_coefficients_continuum α) ^ 2 ≤
        4 * (M : ℝ) ^ 2 := by
    simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      (sq_le_sq' (abs_le.mp (hdelta α)).1 (abs_le.mp (hdelta α)).2)
  have hweights (n : ℕ) : (∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ)) =
      (2 * t * ((d : ℝ) + 1)) ^ n / (Nat.factorial n : ℝ) := by
    simpa [Finset.mul_sum, ← mul_div_assoc, ← mul_pow, ← div_eq_mul_inv] using
      (congrArg (fun a : ℝ => (2 * t) ^ n * a) (part5_multinomial_shell d n (fun _ => (1 : ℝ))))
  have hnonneg (n : ℕ) : 0 ≤ part5_gaussian_partial_sums_square_shell x t n :=
    Finset.sum_nonneg (fun α _ => mul_nonneg (hc n α) (sq_nonneg _))
  have hupper (n : ℕ) : part5_gaussian_partial_sums_square_shell x t n ≤
      4 * (M : ℝ) ^ 2 * (2 * t * ((d : ℝ) + 1)) ^ n / (Nat.factorial n : ℝ) := by
    calc
      _ ≤ ∑ α ∈ part5_multi_index_shell d n, (2 * t) ^ n / (part5_multi_index_factorial α : ℝ) * (4 * (M : ℝ) ^ 2) :=
        Finset.sum_le_sum (fun α _ => mul_le_mul_of_nonneg_left (hsq α) (hc n α))
      _ = _ := by rw [← Finset.sum_mul, hweights]; ring
  have hmajor : Summable (fun n : ℕ => 4 * (M : ℝ) ^ 2 * (2 * t * ((d : ℝ) + 1)) ^ n / (Nat.factorial n : ℝ)) := by
    simpa only [mul_div_assoc] using
      (NormedSpace.expSeries_div_hasSum_exp (2 * t * ((d : ℝ) + 1))).summable.mul_left (4 * (M : ℝ) ^ 2)
  exact ⟨fun n => ⟨hnonneg n, hupper n⟩, Summable.of_nonneg_of_le hnonneg hupper hmajor⟩

/- lem:gaussian-finite-square -/
theorem part5_gaussian_finite_square (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (x : Config d M) (t : ℝ) (R : ℕ) :
  part5_gaussian_partial_sums_empirical x t R - 2 * (M : ℝ) * part5_gaussian_partial_sums_cross x t R + (M : ℝ) ^ 2 * part5_gaussian_partial_sums_continuum d t R = Real.exp (-2 * t) * ∑ n ∈ Finset.range (R + 1), part5_gaussian_partial_sums_square_shell x t n := by
  have hterm (c a m : ℝ) : c * (a - (M : ℝ) * m) ^ 2 =
      c * a ^ 2 - 2 * (M : ℝ) * (c * a * m) + (M : ℝ) ^ 2 * (c * m ^ 2) := by ring
  simp only [part5_gaussian_partial_sums_empirical, part5_gaussian_partial_sums_cross,
    part5_gaussian_partial_sums_continuum, part5_gaussian_partial_sums_square_shell,
    hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/- lem:gaussian-partial-sum-limits -/
theorem part5_gaussian_partial_sum_limits (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (x : Config d M) (t : ℝ) (ht : 0 ≤ t) :
  Filter.Tendsto (part5_gaussian_partial_sums_empirical x t) Filter.atTop (nhds (∑ i : Fin M, ∑ j : Fin M, Real.exp (-t * dist (x i) (x j) ^ 2))) ∧ Filter.Tendsto (part5_gaussian_partial_sums_cross x t) Filter.atTop (nhds ((M : ℝ) * gaussianAverage d t)) ∧ Filter.Tendsto (part5_gaussian_partial_sums_continuum d t) Filter.atTop (nhds (gaussianAverage d t)) ∧ Filter.Tendsto (fun R : ℕ => ∑ n ∈ Finset.range (R + 1), part5_gaussian_partial_sums_square_shell x t n) Filter.atTop (nhds (∑' n : ℕ, part5_gaussian_partial_sums_square_shell x t n)) := by
  have hlim (f : ℕ → ℝ) (hf : Summable (fun n => |f n|)) :
      Filter.Tendsto (fun R : ℕ => Real.exp (-2 * t) * ∑ n ∈ Finset.range (R + 1), f n)
        Filter.atTop (nhds (Real.exp (-2 * t) * ∑' n, f n)) :=
    (((Summable.of_norm (f := f) hf).hasSum.tendsto_sum_nat).comp
      (Filter.tendsto_add_atTop_nat 1)).const_mul (Real.exp (-2 * t))
  refine ⟨?_, ?_, ?_, ((part5_gaussian_square_summable d hd M x t ht).2.hasSum.tendsto_sum_nat).comp
    (Filter.tendsto_add_atTop_nat 1)⟩
  · rw [(part5_gaussian_empirical_series d hd M x t ht).1]
    exact hlim _ (part5_gaussian_empirical_series d hd M x t ht).2
  · rw [(part5_gaussian_cross_series d hd M x t ht).1]
    exact hlim _ (part5_gaussian_cross_series d hd M x t ht).2
  · rw [(part5_gaussian_continuum_series d hd t ht).1]
    exact hlim _ (part5_gaussian_continuum_series d hd t ht).2

/- def:gaussian-discrepancy -/
noncomputable def part5_gaussian_discrepancy {d M : ℕ} (x : Config d M) (t : ℝ) : ℝ := by
  classical
  exact (
    (∑ i : Fin M, ∑ j : Fin M, Real.exp (-t * dist (x i) (x j) ^ 2)) - (M : ℝ) ^ 2 * gaussianAverage d t
  )

/- lem:gaussian-positive -/
theorem part5_gaussian_positive (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (x : Config d M) (t : ℝ) (ht : 0 ≤ t) :
  part5_gaussian_discrepancy x t = Real.exp (-2 * t) * (∑' n : ℕ, part5_gaussian_partial_sums_square_shell x t n) ∧ 0 ≤ part5_gaussian_discrepancy x t := by
  obtain ⟨he, hc, hcont, hq⟩ := part5_gaussian_partial_sum_limits d hd M x t ht
  have hl := (he.sub (hc.const_mul (2 * (M : ℝ)))).add
    (hcont.const_mul ((M : ℝ) ^ 2))
  have hvalue := tendsto_nhds_unique
    (hl.congr (part5_gaussian_finite_square d hd M x t))
    (hq.const_mul (Real.exp (-2 * t)))
  have hidentity : part5_gaussian_discrepancy x t =
      Real.exp (-2 * t) * ∑' n : ℕ, part5_gaussian_partial_sums_square_shell x t n := by
    dsimp only [part5_gaussian_discrepancy]
    nlinarith only [hvalue]
  exact ⟨hidentity, hidentity.symm ▸ mul_nonneg (Real.exp_nonneg _)
    (tsum_nonneg (fun n => ((part5_gaussian_square_summable d hd M x t ht).1 n).1))⟩

/- lem:gaussian-discrepancy-lower -/
theorem part5_gaussian_discrepancy_lower (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (x : Config d M) (t : ℝ) (ht : 0 ≤ t) :
  (M : ℝ) - (M : ℝ) ^ 2 * gaussianAverage d t ≤ part5_gaussian_discrepancy x t ∧ (M : ℝ) ^ 2 * gaussianAverage d t - (M : ℝ) ≤ ∑ i : Fin M, ∑ j : Fin M, if i = j then 0 else Real.exp (-t * dist (x i) (x j) ^ 2) := by
  have hterm (i j : Fin M) : Real.exp (-t * dist (x i) (x j) ^ 2) =
      (if i = j then 1 else 0) + (if i = j then 0 else Real.exp (-t * dist (x i) (x j) ^ 2)) := by
    by_cases hij : i = j <;> simp [hij]
  have hsplit : (∑ i : Fin M, ∑ j : Fin M, Real.exp (-t * dist (x i) (x j) ^ 2)) =
      (M : ℝ) + ∑ i : Fin M, ∑ j : Fin M, if i = j then 0 else Real.exp (-t * dist (x i) (x j) ^ 2) := by
    calc
      _ = ∑ i : Fin M, ∑ j : Fin M, ((if i = j then 1 else 0) +
          (if i = j then 0 else Real.exp (-t * dist (x i) (x j) ^ 2))) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))
      _ = _ := by simp [Finset.sum_add_distrib]
  have hoff : 0 ≤ ∑ i : Fin M, ∑ j : Fin M,
      if i = j then 0 else Real.exp (-t * dist (x i) (x j) ^ 2) := by positivity
  have hpos := (part5_gaussian_positive d hd M x t ht).2
  dsimp only [part5_gaussian_discrepancy] at hpos ⊢
  exact ⟨by linarith only [hsplit, hoff], by linarith only [hsplit, hpos]⟩

/- lem:exp-difference-bound -/
theorem part5_exp_difference_bound (u : ℝ) (hu : 0 ≤ u) :
  0 ≤ 1 - Real.exp (-u) ∧ 1 - Real.exp (-u) ≤ min u 1 := by
  refine ⟨sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)), le_min ?_ ?_⟩
  · linarith only [Real.add_one_le_exp (-u)]
  · exact sub_le_self _ (Real.exp_nonneg _)

/- lem:power-integrals -/
theorem part5_power_integrals (b T : ℝ) (hT : 0 < T) :
  ((-1 < b) → IntegrableOn (fun t : ℝ => Real.rpow t b) (Set.Ioo 0 T) volume ∧ (∫ t in (0 : ℝ)..T, Real.rpow t b) = Real.rpow T (b + 1) / (b + 1)) ∧ ((b < -1) → IntegrableOn (fun t : ℝ => Real.rpow t b) (Set.Ioi T) volume ∧ (∫ t in Set.Ioi T, Real.rpow t b ∂volume) = -Real.rpow T (b + 1) / (b + 1)) := by
  refine ⟨fun hb => ⟨(intervalIntegral.integrableOn_Ioo_rpow_iff hT).2 hb, ?_⟩,
    fun hb => ⟨integrableOn_Ioi_rpow_of_lt hb hT, integral_Ioi_rpow_of_lt hb hT⟩⟩
  change (∫ t : ℝ in (0 : ℝ)..T, t ^ b) = T ^ (b + 1) / (b + 1)
  rw [integral_rpow (Or.inl hb), Real.zero_rpow (by linarith : b + 1 ≠ 0), sub_zero]

/- lem:negative-riesz-integrable -/
theorem part5_negative_riesz_integrable (r a : ℝ) (hr : 0 < r) (ha : 0 < a) (ha1 : a < 1) :
  IntegrableOn (fun t : ℝ => (Real.exp (-r ^ 2 * t) - 1) * Real.rpow t (-a - 1)) (Set.Ioi 0) volume := by
  change IntegrableOn (fun t : ℝ => (Real.exp (-r ^ 2 * t) - 1) * t ^ (-a - 1)) (Set.Ioi 0) volume
  have hmeas : Measurable (fun t : ℝ => (Real.exp (-r ^ 2 * t) - 1) * t ^ (-a - 1)) := by fun_prop
  have hdiff (t : ℝ) (ht : 0 < t) : |Real.exp (-r ^ 2 * t) - 1| ≤ min (r ^ 2 * t) 1 := by
    have he := part5_exp_difference_bound (r ^ 2 * t) (mul_nonneg (sq_nonneg r) ht.le)
    simp only [← neg_mul] at he
    simpa only [abs_sub_comm, abs_of_nonneg he.1] using he.2
  have hnear_bound (t : ℝ) (ht : 0 < t) :
      |(Real.exp (-r ^ 2 * t) - 1) * t ^ (-a - 1)| ≤ r ^ 2 * t ^ (-a) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le (-a - 1))]
    calc
      _ ≤ (r ^ 2 * t) * t ^ (-a - 1) :=
        mul_le_mul_of_nonneg_right ((hdiff t ht).trans (min_le_left _ _))
          (Real.rpow_nonneg ht.le _)
      _ = _ := by
        rw [mul_assoc, mul_comm t _, ← Real.rpow_add_one ht.ne', sub_add_cancel]
  have htail_bound (t : ℝ) (ht : 0 < t) :
      |(Real.exp (-r ^ 2 * t) - 1) * t ^ (-a - 1)| ≤ t ^ (-a - 1) := by
    simpa only [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le (-a - 1)), one_mul] using
      mul_le_mul_of_nonneg_right ((hdiff t ht).trans (min_le_right _ _))
        (Real.rpow_nonneg ht.le (-a - 1))
  have hnear : IntegrableOn (fun t : ℝ => (Real.exp (-r ^ 2 * t) - 1) * t ^ (-a - 1))
      (Set.Ioo 0 1) volume := by
    refine (((part5_power_integrals (-a) 1 zero_lt_one).1 (by linarith)).1.const_mul (r ^ 2)).mono'
      hmeas.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht =>
      by
        rw [Real.norm_eq_abs]
        exact hnear_bound t ht.1)
  have htail : IntegrableOn (fun t : ℝ => (Real.exp (-r ^ 2 * t) - 1) * t ^ (-a - 1))
      (Set.Ioi 1) volume := by
    refine ((part5_power_integrals (-a - 1) 1 zero_lt_one).2 (by linarith)).1.mono'
      hmeas.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht =>
      (Real.norm_eq_abs _).symm ▸ htail_bound t (lt_trans zero_lt_one ht))
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact ((integrableOn_Ioc_iff_integrableOn_Ioo
    (f := fun t : ℝ => (Real.exp (-r ^ 2 * t) - 1) * t ^ (-a - 1))
    (μ := volume) (a := 0) (b := 1)).mpr hnear).union htail

/- lem:negative-riesz-boundary -/
theorem part5_negative_riesz_boundary (r a : ℝ) (hr : 0 < r) (ha : 0 < a) (ha1 : a < 1) :
  (∀ ε : ℝ, 0 < ε → |(Real.exp (-r ^ 2 * ε) - 1) * Real.rpow ε (-a)| ≤ r ^ 2 * Real.rpow ε (1 - a)) ∧ (∀ R : ℝ, 0 < R → |(Real.exp (-r ^ 2 * R) - 1) * Real.rpow R (-a)| ≤ Real.rpow R (-a)) ∧ Filter.Tendsto (fun ε : ℝ => |(Real.exp (-r ^ 2 * ε) - 1) * Real.rpow ε (-a)|) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : ℝ)) ∧ Filter.Tendsto (fun R : ℝ => |(Real.exp (-r ^ 2 * R) - 1) * Real.rpow R (-a)|) Filter.atTop (nhds (0 : ℝ)) := by
  have hdiff (t : ℝ) (ht : 0 < t) : |Real.exp (-r ^ 2 * t) - 1| ≤ min (r ^ 2 * t) 1 := by
    have he := part5_exp_difference_bound (r ^ 2 * t) (mul_nonneg (sq_nonneg r) ht.le)
    simp only [← neg_mul] at he
    simpa only [abs_sub_comm, abs_of_nonneg he.1] using he.2
  have hnear (t : ℝ) (ht : 0 < t) :
      |(Real.exp (-r ^ 2 * t) - 1) * t ^ (-a)| ≤ r ^ 2 * t ^ (1 - a) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le (-a))]
    calc
      _ ≤ (r ^ 2 * t) * t ^ (-a) :=
        mul_le_mul_of_nonneg_right ((hdiff t ht).trans (min_le_left _ _))
          (Real.rpow_nonneg ht.le _)
      _ = _ := by
        rw [mul_assoc, mul_comm t _, ← Real.rpow_add_one ht.ne',
          show -a + 1 = 1 - a by ring]
  have htail (t : ℝ) (ht : 0 < t) :
      |(Real.exp (-r ^ 2 * t) - 1) * t ^ (-a)| ≤ t ^ (-a) := by
    simpa only [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le (-a)), one_mul] using
      mul_le_mul_of_nonneg_right ((hdiff t ht).trans (min_le_right _ _))
        (Real.rpow_nonneg ht.le (-a))
  have hzero : Filter.Tendsto (fun t : ℝ => r ^ 2 * t ^ (1 - a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : ℝ)) := by
    simpa only [Real.zero_rpow (by linarith : 1 - a ≠ 0), mul_zero] using
      ((Real.continuous_rpow_const (by linarith : 0 ≤ 1 - a)).continuousWithinAt
        (x := (0 : ℝ)) (s := Set.Ioi 0)).tendsto.const_mul (r ^ 2)
  refine ⟨hnear, htail, ?_, ?_⟩
  · exact squeeze_zero' (Filter.Eventually.of_forall (fun t => abs_nonneg _))
      (Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => hnear t ht)) hzero
  · exact squeeze_zero' (Filter.Eventually.of_forall (fun t => abs_nonneg _))
      ((Filter.eventually_gt_atTop (0 : ℝ)).mono (fun t ht => htail t ht))
      (tendsto_rpow_neg_atTop ha)

/- lem:negative-riesz-proper-ibp -/
theorem part5_negative_riesz_proper_ibp (r a ε R : ℝ) (hr : 0 < r) (ha : 0 < a) (ha1 : a < 1) (hε : 0 < ε) (hεR : ε < R) :
  (∫ t in ε..R, (Real.exp (-r ^ 2 * t) - 1) * Real.rpow t (-a - 1)) = -(1 / a) * ((Real.exp (-r ^ 2 * R) - 1) * Real.rpow R (-a) - ((Real.exp (-r ^ 2 * ε) - 1) * Real.rpow ε (-a))) - (r ^ 2 / a) * (∫ t in ε..R, Real.exp (-r ^ 2 * t) * Real.rpow t (-a)) := by
  change (∫ t in ε..R, (Real.exp (-r ^ 2 * t) - 1) * t ^ (-a - 1)) =
    -(1 / a) * ((Real.exp (-r ^ 2 * R) - 1) * R ^ (-a) -
      ((Real.exp (-r ^ 2 * ε) - 1) * ε ^ (-a))) -
    (r ^ 2 / a) * (∫ t in ε..R, Real.exp (-r ^ 2 * t) * t ^ (-a))
  have hu (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-r ^ 2 * t) - 1)
      (-r ^ 2 * Real.exp (-r ^ 2 * t)) t := by
    convert (((hasDerivAt_id t).const_mul (-r ^ 2)).exp.sub_const 1) using 1
    all_goals first | rfl | simp only [id_eq, mul_one, mul_comm]
  have hv (t : ℝ) (ht : 0 < t) : HasDerivAt (fun t : ℝ => -(1 / a) * t ^ (-a))
      (t ^ (-a - 1)) t := by
    convert (Real.hasDerivAt_rpow_const (p := -a) (Or.inl ht.ne')).const_mul (-(1 / a)) using 1
    all_goals first | rfl | field_simp
  have hp (b : ℝ) : ContinuousOn (fun t : ℝ => t ^ b) (Set.Icc ε R) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (hε.trans_le ht.1).ne')
  have hu' : IntervalIntegrable (fun t : ℝ => -r ^ 2 * Real.exp (-r ^ 2 * t)) volume ε R :=
    (by fun_prop : Continuous (fun t : ℝ => -r ^ 2 * Real.exp (-r ^ 2 * t))).intervalIntegrable ε R
  have hv' : IntervalIntegrable (fun t : ℝ => t ^ (-a - 1)) volume ε R :=
    (hp (-a - 1)).intervalIntegrable_of_Icc hεR.le
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => hu t)
    (fun t ht => hv t (hε.trans_le ((Set.uIcc_of_le hεR.le) ▸ ht).1)) hu' hv'
  have hproduct (z w : ℝ) : (-r ^ 2 * z) * (-(1 / a) * w) = (r ^ 2 / a) * (z * w) := by ring
  simp_rw [hproduct, intervalIntegral.integral_const_mul] at hibp
  nlinarith only [hibp]

/- lem:negative-riesz-limit -/
theorem part5_negative_riesz_limit (r a : ℝ) (hr : 0 < r) (ha : 0 < a) (ha1 : a < 1) :
  (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-r ^ 2 * t) - 1) * Real.rpow t (-a - 1) ∂volume) = -(r ^ 2 / a) * (∫ t in Set.Ioi (0 : ℝ), Real.exp (-r ^ 2 * t) * Real.rpow t (-a) ∂volume) := by
  let U : ℕ → ℝ := fun n => (n : ℝ) + 2
  have hU_one (n : ℕ) : 1 < U n :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hL_pos (n : ℕ) : 0 < 1 / U n := one_div_pos.mpr (zero_lt_one.trans (hU_one n))
  have hLU (n : ℕ) : 1 / U n < U n :=
    (div_lt_iff₀ (zero_lt_one.trans (hU_one n))).mpr (by nlinarith only [hU_one n])
  have hU_limit : Filter.Tendsto U Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have hL_limit : Filter.Tendsto (fun n => 1 / U n) Filter.atTop (nhds (0 : ℝ)) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp hU_limit
  have hL_within : Filter.Tendsto (fun n => 1 / U n) Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hL_limit, Filter.Eventually.of_forall hL_pos⟩
  have hcover : MeasureTheory.AECover (volume.restrict (Set.Ioi (0 : ℝ))) Filter.atTop
      (fun n => Set.Ioc (1 / U n) (U n)) := by
    refine ⟨?_, fun _ => measurableSet_Ioc⟩
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
    exact (hL_limit.eventually (gt_mem_nhds ht)).and
      (hU_limit.eventually (Filter.eventually_ge_atTop t))
  have hlim (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi 0) volume) :
      Filter.Tendsto (fun n => ∫ t in (1 / U n)..U n, f t) Filter.atTop
        (nhds (∫ t in Set.Ioi (0 : ℝ), f t ∂volume)) := by
    refine (hcover.integral_tendsto_of_countably_generated hf).congr (fun n => ?_)
    rw [intervalIntegral.integral_of_le (hLU n).le,
      Measure.restrict_restrict_of_subset (μ := volume) (t := Set.Ioi (0 : ℝ))
        (fun t (ht : t ∈ Set.Ioc (1 / U n) (U n)) => (hL_pos n).trans ht.1)]
  have hG : IntegrableOn (fun t : ℝ => Real.exp (-r ^ 2 * t) * Real.rpow t (-a))
      (Set.Ioi 0) volume := by
    simpa only [show 1 - a - 1 = -a by ring, mul_comm] using
      scaled_gamma_integrable (1 - a) (r ^ 2) (by linarith) (sq_pos_of_pos hr)
  have hb := part5_negative_riesz_boundary r a hr ha ha1
  have hb0 : Filter.Tendsto (fun t : ℝ => (Real.exp (-r ^ 2 * t) - 1) * Real.rpow t (-a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : ℝ)) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr hb.2.2.1
  have hbtop : Filter.Tendsto (fun t : ℝ => (Real.exp (-r ^ 2 * t) - 1) * Real.rpow t (-a))
      Filter.atTop (nhds (0 : ℝ)) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr hb.2.2.2
  have hright := (((hbtop.comp hU_limit).sub (hb0.comp hL_within)).const_mul (-(1 / a))).sub
    ((hlim _ hG).const_mul (r ^ 2 / a))
  have heq := tendsto_nhds_unique
    ((hlim _ (part5_negative_riesz_integrable r a hr ha ha1)).congr
      (fun n => part5_negative_riesz_proper_ibp r a (1 / U n) (U n) hr ha ha1 (hL_pos n) (hLU n)))
    hright
  simpa only [sub_self, mul_zero, zero_sub, neg_mul] using heq

/- lem:negative-riesz-improper-limit -/
theorem part5_negative_riesz_improper_limit (r a : ℝ) (hr : 0 < r) (ha : 0 < a) (ha1 : a < 1) :
  (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-r ^ 2 * t) - 1) * Real.rpow t (-a - 1) ∂volume) = Real.Gamma (-a) * Real.rpow r (2 * a) := by
  rw [part5_negative_riesz_limit r a hr ha ha1]
  have hG :
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-r ^ 2 * t) * Real.rpow t (-a) ∂volume) =
      Real.rpow (r ^ 2) (a - 1) * Real.Gamma (1 - a) := by
    simpa only [show 1 - a - 1 = -a by ring, show -(1 - a) = a - 1 by ring,
      mul_comm] using scaled_gamma_integral (1 - a) (r ^ 2) (by linarith) (sq_pos_of_pos hr)
  have hGamma : Real.Gamma (1 - a) = (-a) * Real.Gamma (-a) := by
    simpa only [show -a + 1 = 1 - a by ring] using
      (Real.Gamma_add_one (neg_ne_zero.mpr ha.ne'))
  have hpow : r ^ 2 * Real.rpow (r ^ 2) (a - 1) = Real.rpow r (2 * a) := by
    change r ^ 2 * (r ^ 2) ^ (a - 1) = r ^ (2 * a)
    rw [mul_comm, ← Real.rpow_add_one (sq_pos_of_pos hr).ne', sub_add_cancel,
      ← Real.rpow_natCast_mul hr.le 2 a]
    norm_num
  rw [hG, hGamma, ← hpow]
  field_simp

/- lem:frullani-proper-fubini -/
theorem part5_frullani_proper_fubini (a b ε R : ℝ) (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) (hεR : ε < R) :
  (∫ t in ε..R, (Real.exp (-a * t) - Real.exp (-b * t)) / t) = (∫ u in a..b, (∫ t in ε..R, Real.exp (-u * t))) ∧ (∫ u in a..b, (∫ t in ε..R, Real.exp (-u * t))) = (∫ u in a..b, (Real.exp (-u * ε) - Real.exp (-u * R)) / u) := by
  have hexp (c l h : ℝ) (hc : 0 < c) :
      (∫ x in l..h, Real.exp (-c * x)) = (Real.exp (-c * l) - Real.exp (-c * h)) / c := by
    rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hc.ne'),
      integral_exp, smul_eq_mul]
    simp only [inv_neg, div_eq_mul_inv]; ring
  have hrect : IntegrableOn (fun p : ℝ × ℝ => Real.exp (-p.2 * p.1))
      (Set.uIoc ε R ×ˢ Set.uIoc a b) volume :=
    (ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
      (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => Real.exp (-p.2 * p.1))
        (Set.uIcc ε R ×ˢ Set.uIcc a b))).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hpoint (t : ℝ) (ht : 0 < t) :
      (Real.exp (-a * t) - Real.exp (-b * t)) / t =
        ∫ u in a..b, Real.exp (-u * t) := by
    simpa only [show ∀ x : ℝ, -x * t = -t * x by intro x; ring] using
      (hexp t a b ht).symm
  refine ⟨?_, intervalIntegral.integral_congr
    (fun u hu => hexp u ε R ((lt_min ha hb).trans_le hu.1))⟩
  exact (intervalIntegral.integral_congr (fun t ht =>
    hpoint t ((lt_min hε (hε.trans hεR)).trans_le ht.1))).trans
      (intervalIntegral_intervalIntegral_swap hrect)

/- lem:frullani-integrable -/
theorem part5_frullani_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  IntegrableOn (fun t : ℝ => (Real.exp (-a * t) - Real.exp (-b * t)) / t) (Set.Ioi 0) volume := by
  have hmeas : Measurable (fun t : ℝ => (Real.exp (-a * t) - Real.exp (-b * t)) / t) := by
    fun_prop
  have hpoint (t : ℝ) (ht : 0 < t) :
      (∫ u in a..b, Real.exp (-u * t)) = (Real.exp (-a * t) - Real.exp (-b * t)) / t := by
    simp_rw [show ∀ u : ℝ, -u * t = u * (-t) by intro u; ring]
    rw [intervalIntegral.integral_comp_mul_right Real.exp (neg_ne_zero.mpr ht.ne'),
      integral_exp, smul_eq_mul]
    field_simp
    ring
  have hbound (t : ℝ) (ht : 0 < t) (u : ℝ) (hu : u ∈ Set.uIoc a b) :
      ‖Real.exp (-u * t)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr ((lt_min ha hb).trans hu.1).le) ht.le)
  have hnear_bound (t : ℝ) (ht : 0 < t) :
      |(Real.exp (-a * t) - Real.exp (-b * t)) / t| ≤ |b - a| := by
    simpa only [hpoint t ht, Real.norm_eq_abs, one_mul] using
      intervalIntegral.norm_integral_le_of_norm_le_const (hbound t ht)
  have htail_bound (t : ℝ) (ht : 1 ≤ t) :
      |(Real.exp (-a * t) - Real.exp (-b * t)) / t| ≤
        Real.exp (-a * t) + Real.exp (-b * t) := by
    rw [abs_div, abs_of_nonneg (zero_le_one.trans ht)]
    exact (div_le_self (abs_nonneg _) ht).trans
      (abs_le.mpr ⟨by linarith only [Real.exp_nonneg (-a * t)],
        by linarith only [Real.exp_nonneg (-b * t)]⟩)
  have he (c : ℝ) (hc : 0 < c) :
      IntegrableOn (fun t : ℝ => Real.exp (-c * t)) (Set.Ioi 1) volume := by
    simpa only [sub_self, Real.rpow_eq_pow, Real.rpow_zero, one_mul] using
      (scaled_gamma_integrable 1 c zero_lt_one hc).mono_set
        (Set.Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  have hnear : IntegrableOn (fun t : ℝ => (Real.exp (-a * t) - Real.exp (-b * t)) / t)
      (Set.Ioc 0 1) volume :=
    (integrableOn_const (C := |b - a|) (μ := volume) (s := Set.Ioc (0 : ℝ) 1)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).mono'
      hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht =>
        (Real.norm_eq_abs _).symm ▸ hnear_bound t ht.1))
  have htail : IntegrableOn (fun t : ℝ => (Real.exp (-a * t) - Real.exp (-b * t)) / t)
      (Set.Ioi 1) volume :=
    ((he a ha).add (he b hb)).mono' hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht =>
        (Real.norm_eq_abs _).symm ▸ htail_bound t ht.le))
  simpa only [Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one)] using
    hnear.union htail

/- lem:frullani-value -/
theorem part5_frullani_value (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-a * t) - Real.exp (-b * t)) / t ∂volume) = Real.log (b / a) := by
  let U : ℕ → ℝ := fun n => (n : ℝ) + 2
  have hU_one (n : ℕ) : 1 < U n :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hL_pos (n : ℕ) : 0 < 1 / U n := one_div_pos.mpr (zero_lt_one.trans (hU_one n))
  have hLU (n : ℕ) : 1 / U n < U n :=
    (div_lt_iff₀ (zero_lt_one.trans (hU_one n))).mpr (by nlinarith only [hU_one n])
  have hU_limit : Filter.Tendsto U Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have hL_limit : Filter.Tendsto (fun n => 1 / U n) Filter.atTop (nhds (0 : ℝ)) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp hU_limit
  have hcover : MeasureTheory.AECover (volume.restrict (Set.Ioi (0 : ℝ))) Filter.atTop
      (fun n => Set.Ioc (1 / U n) (U n)) := by
    refine ⟨?_, fun _ => measurableSet_Ioc⟩
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
    exact (hL_limit.eventually (gt_mem_nhds ht)).and
      (hU_limit.eventually (Filter.eventually_ge_atTop t))
  have hleft : Filter.Tendsto
      (fun n => ∫ t in (1 / U n)..U n, (Real.exp (-a * t) - Real.exp (-b * t)) / t)
      Filter.atTop
      (nhds (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-a * t) - Real.exp (-b * t)) / t ∂volume)) := by
    refine (hcover.integral_tendsto_of_countably_generated
      (part5_frullani_integrable a b ha hb)).congr (fun n => ?_)
    rw [intervalIntegral.integral_of_le (hLU n).le,
      Measure.restrict_restrict_of_subset (μ := volume) (t := Set.Ioi (0 : ℝ))
        (fun t (ht : t ∈ Set.Ioc (1 / U n) (U n)) => (hL_pos n).trans ht.1)]
  let F : ℕ → ℝ → ℝ := fun n u =>
    (Real.exp (-u * (1 / U n)) - Real.exp (-u * U n)) / u
  have hu_pos (u : ℝ) (hu : u ∈ Set.uIoc a b) : 0 < u := (lt_min ha hb).trans hu.1
  have hexp_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
      0 ≤ Real.exp (-u * t) ∧ Real.exp (-u * t) ≤ 1 :=
    ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) ht)⟩
  have hF_bound (n : ℕ) (u : ℝ) (hu : u ∈ Set.uIoc a b) :
      ‖F n u‖ ≤ 2 / min a b := by
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hu_pos u hu)]
    have he0 := hexp_bound (1 / U n) u (hL_pos n).le (hu_pos u hu).le
    have he1 := hexp_bound (U n) u (zero_lt_one.trans (hU_one n)).le (hu_pos u hu).le
    have hdiff : |Real.exp (-u * (1 / U n)) - Real.exp (-u * U n)| ≤ 2 :=
      abs_le.mpr ⟨by linarith only [he0.1, he1.2], by linarith only [he0.2, he1.1]⟩
    exact (div_le_div_of_nonneg_right hdiff (hu_pos u hu).le).trans
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (lt_min ha hb) hu.1.le)
  have hF_meas (n : ℕ) : Measurable (F n) := by fun_prop
  have hsmall (u : ℝ) : Filter.Tendsto (fun n => Real.exp (-u * (1 / U n)))
      Filter.atTop (nhds (1 : ℝ)) := by
    have hmul := hL_limit.const_mul (-u)
    simp only [mul_zero] at hmul
    exact Real.tendsto_exp_nhds_zero_nhds_one.comp hmul
  have hlarge (u : ℝ) (hu : 0 < u) : Filter.Tendsto (fun n => Real.exp (-u * U n))
      Filter.atTop (nhds (0 : ℝ)) := by
    have hlim := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hu hU_limit)
    change Filter.Tendsto (fun n => Real.exp (-(u * U n))) Filter.atTop (nhds (0 : ℝ)) at hlim
    simpa only [← neg_mul] using hlim
  have hF_limit (u : ℝ) (hu : u ∈ Set.uIoc a b) :
      Filter.Tendsto (fun n => F n u) Filter.atTop (nhds (1 / u)) := by
    simpa only [F, sub_zero] using ((hsmall u).sub (hlarge u (hu_pos u hu))).div_const u
  have hright : Filter.Tendsto (fun n => ∫ u in a..b, F n u) Filter.atTop
      (nhds (∫ u in a..b, (1 / u : ℝ))) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2 / min a b)
      (Filter.Eventually.of_forall (fun n => (hF_meas n).aestronglyMeasurable))
      (Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall (fun u hu => hF_bound n u hu)))
      ((continuous_const : Continuous (fun _ : ℝ => 2 / min a b)).intervalIntegrable a b)
      (Filter.Eventually.of_forall (fun u hu => hF_limit u hu))
  have hproper (n : ℕ) :=
    part5_frullani_proper_fubini a b (1 / U n) (U n) ha hb (hL_pos n) (hLU n)
  have heq := tendsto_nhds_unique
    (hleft.congr (fun n => (hproper n).1.trans (hproper n).2)) hright
  exact heq.trans (integral_one_div_of_pos ha hb)

/- lem:frullani-identity -/
theorem part5_frullani_identity (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  (∫ t in Set.Ioi (0 : ℝ), |Real.exp (-a * t) - Real.exp (-b * t)| / t ∂volume) = |Real.log (b / a)| := by
  have hordered (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q) :
      (∫ t in Set.Ioi (0 : ℝ), |Real.exp (-p * t) - Real.exp (-q * t)| / t ∂volume) =
        |Real.log (q / p)| := by
    have hpos (t : ℝ) (ht : 0 < t) : 0 ≤ Real.exp (-p * t) - Real.exp (-q * t) :=
      sub_nonneg.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hpq) ht.le))
    have hlog : 0 ≤ Real.log (q / p) := by
      rw [← part5_frullani_value p q hp hq]
      exact setIntegral_nonneg measurableSet_Ioi (fun t ht => div_nonneg (hpos t ht) ht.le)
    rw [abs_of_nonneg hlog, ← part5_frullani_value p q hp hq]
    exact integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => congrArg (fun v : ℝ => v / t) (abs_of_nonneg (hpos t ht))))
  refine (le_total a b).elim (hordered a b ha hb) ?_
  intro hba
  simpa only [Real.log_div hb.ne' ha.ne', Real.log_div ha.ne' hb.ne', abs_sub_comm] using
    hordered b a hb ha hba

/- def:riesz-gamma-coefficient -/
noncomputable def part5_riesz_gamma_coefficient (s : ℝ) : ℝ := by
  classical
  exact (
    1 / (s * Real.Gamma (s / 2))
  )

/- lem:riesz-gamma-positive -/
theorem part5_riesz_gamma_positive (s : ℝ) (hs : 0 < s ∨ (-2 < s ∧ s < 0)) :
  0 < part5_riesz_gamma_coefficient s := by
  change 0 < 1 / (s * Real.Gamma (s / 2))
  apply one_div_pos.mpr
  rcases hs with hs | ⟨hs, hs0⟩
  · exact mul_pos hs (Real.Gamma_pos_of_pos (by linarith : 0 < s / 2))
  exact mul_pos_of_neg_of_neg hs0 (gamma_negative_strip (s / 2) (by linarith) (by linarith))

/- lem:positive-pointwise -/
theorem part5_positive_pointwise (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
  IntegrableOn (fun t : ℝ => Real.exp (-t * r ^ 2) * Real.rpow t (s / 2 - 1)) (Set.Ioi 0) volume ∧ (1 / s) * Real.rpow r (-s) = part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * r ^ 2) * Real.rpow t (s / 2 - 1) ∂volume) := by
  have hshape : 0 < s / 2 := by linarith
  constructor
  · simpa only [neg_mul, mul_neg, mul_comm] using scaled_gamma_integrable (s / 2) (r ^ 2) hshape (sq_pos_of_pos hr)
  have hvalue : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * r ^ 2) * Real.rpow t (s / 2 - 1) ∂volume) =
      Real.rpow (r ^ 2) (-(s / 2)) * Real.Gamma (s / 2) := by
    simpa only [neg_mul, mul_neg, mul_comm] using scaled_gamma_integral (s / 2) (r ^ 2) hshape (sq_pos_of_pos hr)
  have hpow : Real.rpow (r ^ 2) (-(s / 2)) = Real.rpow r (-s) := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) * -(s / 2) = -s by ring, Real.rpow_eq_pow] using
      (Real.rpow_natCast_mul hr.le 2 (-(s / 2))).symm
  rw [hvalue, hpow, part5_riesz_gamma_coefficient]
  field_simp [(Real.Gamma_pos_of_pos hshape).ne', hs.ne']

/- lem:negative-riesz-integrable -/
theorem part5_negative_riesz_integrable_zero (a : ℝ) :
  ∀ t : ℝ, (Real.exp (-(0 : ℝ) ^ 2 * t) - 1) * Real.rpow t (-a - 1) = 0 := by
  simp

/- lem:negative-pointwise -/
theorem part5_negative_pointwise (s r : ℝ) (hs : -2 < s) (hs0 : s < 0) (hr : 0 ≤ r) :
  IntegrableOn (fun t : ℝ => (Real.exp (-t * r ^ 2) - 1) * Real.rpow t (s / 2 - 1)) (Set.Ioi 0) volume ∧ (1 / s) * Real.rpow r (-s) = part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t * r ^ 2) - 1) * Real.rpow t (s / 2 - 1) ∂volume) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [Real.rpow_eq_pow, Real.zero_rpow (neg_pos.mpr hs0).ne']
  have ha : 0 < -s / 2 ∧ -s / 2 < 1 := ⟨by linarith, by linarith⟩
  constructor
  · simpa only [show -(-s / 2) = s / 2 by ring, neg_mul, mul_neg, mul_comm] using
      part5_negative_riesz_integrable r (-s / 2) hr ha.1 ha.2
  have hvalue : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t * r ^ 2) - 1) * Real.rpow t (s / 2 - 1) ∂volume) =
      Real.Gamma (s / 2) * Real.rpow r (-s) := by
    simpa only [show -(-s / 2) = s / 2 by ring, show (2 : ℝ) * (-s / 2) = -s by ring,
      neg_mul, mul_neg, mul_comm] using part5_negative_riesz_improper_limit r (-s / 2) hr ha.1 ha.2
  have hden : s * Real.Gamma (s / 2) ≠ 0 :=
    (one_div_pos.mp (part5_riesz_gamma_positive s (Or.inr ⟨hs, hs0⟩))).ne'
  rw [hvalue, part5_riesz_gamma_coefficient]
  field_simp [hs0.ne, (mul_ne_zero_iff.mp hden).2]

/- lem:log-pointwise -/
theorem part5_log_pointwise (r : ℝ) (hr : 0 < r) :
  IntegrableOn (fun t : ℝ => (Real.exp (-t * r ^ 2) - Real.exp (-t)) / t) (Set.Ioi 0) volume ∧ -Real.log r = (1 / 2 : ℝ) * (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t * r ^ 2) - Real.exp (-t)) / t ∂volume) ∧ (∫ t in Set.Ioi (0 : ℝ), |Real.exp (-t * r ^ 2) - Real.exp (-t)| / t ∂volume) = 2 * |Real.log r| := by
  have hlog : Real.log (1 / r ^ 2) = -(2 * Real.log r) := by
    simp only [one_div, Real.log_inv, Real.log_pow, Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [neg_mul, mul_neg, one_mul, mul_one, mul_comm] using
      part5_frullani_integrable (r ^ 2) 1 (sq_pos_of_pos hr) zero_lt_one
  · have hvalue : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t * r ^ 2) - Real.exp (-t)) / t ∂volume) =
        -(2 * Real.log r) := by
      simpa only [neg_mul, mul_neg, one_mul, mul_one, mul_comm, hlog] using
        part5_frullani_value (r ^ 2) 1 (sq_pos_of_pos hr) zero_lt_one
    linarith only [hvalue]
  simpa only [neg_mul, mul_neg, one_mul, mul_one, mul_comm, hlog, abs_neg, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      part5_frullani_identity (r ^ 2) 1 (sq_pos_of_pos hr) zero_lt_one

/- lem:J-continuous -/
theorem part5_J_continuous (d : ℕ) (hd : 2 ≤ d) :
  Continuous (gaussianAverage d) ∧ Measurable (gaussianAverage d) ∧ ∀ t : ℝ, 0 ≤ t → 0 < gaussianAverage d t ∧ gaussianAverage d t ≤ 1 := by
  have hcont : Continuous (gaussianAverage d) := by
    change Continuous (fun t : ℝ => ∫ y : Sphere d, Real.exp (-t * dist (northPole d) y ^ 2) ∂sigma d)
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous (μ := sigma d)
        (f := fun t : ℝ => fun y : Sphere d => Real.exp (-t * dist (northPole d) y ^ 2))
        (by fun_prop) (s := Set.univ) isCompact_univ)
  refine ⟨hcont, hcont.measurable, ?_⟩
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · simp [gaussianAverage]
  refine ⟨(gaussian_positive d hd t ht).1.trans_le (gaussian_positive d hd t ht).2, ?_⟩
  have hbound (y : Sphere d) : Real.exp (-t * dist (northPole d) y ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) (sq_nonneg _))
  simpa only [gaussianAverage, integral_const, probReal_univ, one_smul] using
    integral_mono (gaussian_center d hd t (northPole d)).1 (integrable_const (1 : ℝ)) hbound

/- def:gaussian-total-representatives -/
noncomputable def part5_gaussian_total_representatives_positive {d : ℕ} (s t : ℝ) (y : Sphere d) :
  ℝ := by
  classical
  exact (
    if 0 < t then if y = northPole d then 0 else Real.exp (-t * dist (northPole d) y ^ 2) * Real.rpow t (s / 2 - 1) else 0
  )

/- def:gaussian-total-representatives -/
noncomputable def part5_gaussian_total_representatives_negative {d : ℕ} (s t : ℝ) (y : Sphere d) :
  ℝ := by
  classical
  exact (
    if 0 < t then (Real.exp (-t * dist (northPole d) y ^ 2) - 1) * Real.rpow t (s / 2 - 1) else 0
  )

/- def:gaussian-total-representatives -/
noncomputable def part5_gaussian_total_representatives_logarithmic {d : ℕ} (t : ℝ) (y : Sphere d) :
  ℝ := by
  classical
  exact (
    if 0 < t then if y = northPole d then 0 else (Real.exp (-t * dist (northPole d) y ^ 2) - Real.exp (-t)) / t else 0
  )

/- lem:gaussian-total-measurable -/
theorem part5_gaussian_total_measurable (d : ℕ) (hd : 2 ≤ d) (s : ℝ) :
  Measurable (fun p : ℝ × Sphere d => part5_gaussian_total_representatives_positive s p.1 p.2) ∧ Measurable (fun p : ℝ × Sphere d => part5_gaussian_total_representatives_negative s p.1 p.2) ∧ Measurable (fun p : ℝ × Sphere d => part5_gaussian_total_representatives_logarithmic p.1 p.2) ∧ (∀ (t : ℝ) (y : Sphere d), 0 ≤ part5_gaussian_total_representatives_positive s t y) ∧ ∀ t : ℝ, 0 < t → ((fun y : Sphere d => part5_gaussian_total_representatives_positive s t y) =ᵐ[sigma d] (fun y => Real.exp (-t * dist (northPole d) y ^ 2) * Real.rpow t (s / 2 - 1))) ∧ ((fun y : Sphere d => part5_gaussian_total_representatives_logarithmic t y) =ᵐ[sigma d] (fun y => (Real.exp (-t * dist (northPole d) y ^ 2) - Real.exp (-t)) / t)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold part5_gaussian_total_representatives_positive
    simp only [Real.rpow_eq_pow]
    exact Measurable.ite (isOpen_lt continuous_const continuous_fst).measurableSet
      (Measurable.ite (isClosed_eq continuous_snd continuous_const).measurableSet
        measurable_const (by fun_prop)) measurable_const
  · simp only [part5_gaussian_total_representatives_negative, Real.rpow_eq_pow]
    exact Measurable.ite (isOpen_lt continuous_const continuous_fst).measurableSet
      (by fun_prop) measurable_const
  · unfold part5_gaussian_total_representatives_logarithmic
    exact Measurable.ite (isOpen_lt continuous_const continuous_fst).measurableSet
      (Measurable.ite (isClosed_eq continuous_snd continuous_const).measurableSet
        measurable_const (by fun_prop)) measurable_const
  · intro t y
    unfold part5_gaussian_total_representatives_positive
    split_ifs with ht hy
    all_goals first | exact le_rfl | exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg ht.le _)
  letI : NullSingletonClass (sigma d) := sphere_nullSingletonClass d hd
  intro t ht
  exact ⟨((sigma d).ae_ne (northPole d)).mono (fun y hy => by
      simp only [part5_gaussian_total_representatives_positive, if_pos ht, if_neg hy]),
    ((sigma d).ae_ne (northPole d)).mono (fun y hy => by
      simp only [part5_gaussian_total_representatives_logarithmic, if_pos ht, if_neg hy])⟩

/- lem:positive-J-integrable -/
theorem part5_positive_J_integrable (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) :
  IntegrableOn (fun t : ℝ => gaussianAverage d t * Real.rpow t (s / 2 - 1)) (Set.Ioi 0) volume := by
  change IntegrableOn (fun t : ℝ => gaussianAverage d t * t ^ (s / 2 - 1)) (Set.Ioi 0) volume
  have hmeas : Measurable (fun t : ℝ => gaussianAverage d t * t ^ (s / 2 - 1)) :=
    (part5_J_continuous d hd).2.1.mul (by fun_prop)
  have hnonneg (t : ℝ) (ht : 0 < t) : 0 ≤ gaussianAverage d t * t ^ (s / 2 - 1) :=
    mul_nonneg ((part5_J_continuous d hd).2.2 t ht.le).1.le (Real.rpow_nonneg ht.le _)
  have hnear_bound (t : ℝ) (ht : 0 < t) : ‖gaussianAverage d t * t ^ (s / 2 - 1)‖ ≤ t ^ (s / 2 - 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t ht)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      ((part5_J_continuous d hd).2.2 t ht.le).2 (Real.rpow_nonneg ht.le (s / 2 - 1))
  have hnear_pow : IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1)) (Set.Ioc 0 1) volume := by
    apply (integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).mpr
    simpa only [Real.rpow_eq_pow] using ((part5_power_integrals (s / 2 - 1) 1 zero_lt_one).1 (by linarith)).1
  have hnear : IntegrableOn (fun t : ℝ => gaussianAverage d t * t ^ (s / 2 - 1)) (Set.Ioc 0 1) volume :=
    hnear_pow.mono' hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => hnear_bound t ht.1))
  have htail_bound (t : ℝ) (ht : 0 < t) : ‖gaussianAverage d t * t ^ (s / 2 - 1)‖ ≤
      gaussianAverageConstant d * t ^ ((s - (d : ℝ)) / 2 - 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t ht)]
    simpa only [Real.rpow_eq_pow, mul_assoc, ← Real.rpow_add ht,
      show -(d : ℝ) / 2 + (s / 2 - 1) = (s - (d : ℝ)) / 2 - 1 by ring] using
      mul_le_mul_of_nonneg_right ((gaussian_average d hd).2.1 t ht).2
        (Real.rpow_nonneg ht.le (s / 2 - 1))
  have htail_pow : IntegrableOn (fun t : ℝ => t ^ ((s - (d : ℝ)) / 2 - 1)) (Set.Ioi 1) volume := by
    simpa only [Real.rpow_eq_pow] using
      ((part5_power_integrals ((s - (d : ℝ)) / 2 - 1) 1 zero_lt_one).2 (by linarith)).1
  have htail : IntegrableOn (fun t : ℝ => gaussianAverage d t * t ^ (s / 2 - 1)) (Set.Ioi 1) volume :=
    (htail_pow.const_mul (gaussianAverageConstant d)).mono' hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => htail_bound t (zero_lt_one.trans ht)))
  simpa only [Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one)] using hnear.union htail

/- lem:positive-continuum -/
theorem part5_positive_continuum (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) :
  continuousEnergy d s = part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), gaussianAverage d t * Real.rpow t (s / 2 - 1) ∂volume) := by
  let G : ℝ → Sphere d → ℝ := part5_gaussian_total_representatives_positive s
  have hmeas : Measurable (Function.uncurry G) := (part5_gaussian_total_measurable d hd s).1
  have hnonneg (t : ℝ) (y : Sphere d) : 0 ≤ G t y :=
    (part5_gaussian_total_measurable d hd s).2.2.2.1 t y
  have hsection (t : ℝ) (ht : 0 < t) : (G t) =ᵐ[sigma d]
      (fun y => Real.exp (-t * dist (northPole d) y ^ 2) * Real.rpow t (s / 2 - 1)) :=
    ((part5_gaussian_total_measurable d hd s).2.2.2.2 t ht).1
  have hsection_int (t : ℝ) (ht : 0 < t) : Integrable (G t) (sigma d) :=
    (((gaussian_center d hd t (northPole d)).1).mul_const (Real.rpow t (s / 2 - 1))).congr
      (hsection t ht).symm
  have hsection_value (t : ℝ) (ht : 0 < t) : (∫ y, G t y ∂sigma d) =
      gaussianAverage d t * Real.rpow t (s / 2 - 1) := by
    simpa only [gaussianAverage, integral_mul_const] using integral_congr_ae (hsection t ht)
  have hnorm (t : ℝ) : (∫ y, ‖G t y‖ ∂sigma d) = ∫ y, G t y ∂sigma d :=
    integral_congr_ae (Filter.Eventually.of_forall (fun y => Real.norm_of_nonneg (hnonneg t y)))
  have hprod : Integrable (Function.uncurry G) ((volume.restrict (Set.Ioi (0 : ℝ))).prod (sigma d)) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    refine ⟨ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hsection_int t ht), ?_⟩
    exact (part5_positive_J_integrable d hd s hs hsd).congr
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ((hnorm t).trans (hsection_value t ht)).symm))
  have hkernel (y : Sphere d) : kernel d s (northPole d) y =
      part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), G t y ∂volume) := by
    by_cases hy : y = northPole d
    · simp [hy, G, part5_gaussian_total_representatives_positive, kernel_diag]
    have htime : (fun t => G t y) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun t => Real.exp (-t * dist (northPole d) y ^ 2) * Real.rpow t (s / 2 - 1)) :=
      ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => by
        simp only [G, part5_gaussian_total_representatives_positive, if_pos (show 0 < t from ht), if_neg hy])
    rw [kernel_ne_zero_offDiag hs.ne' (Ne.symm hy), integral_congr_ae htime]
    exact (part5_positive_pointwise s (dist (northPole d) y) hs (dist_pos.mpr (Ne.symm hy))).2
  unfold continuousEnergy
  simp_rw [hkernel]
  rw [integral_const_mul, ← integral_integral_swap hprod]
  exact congrArg (fun z : ℝ => part5_riesz_gamma_coefficient s * z)
    (integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hsection_value t ht)))

/- lem:negative-product-integrable -/
theorem part5_negative_product_integrable (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : -2 < s) (hs0 : s < 0) :
  Integrable (fun p : ℝ × Sphere d => part5_gaussian_total_representatives_negative s p.1 p.2) ((volume.restrict (Set.Ioi (0 : ℝ))).prod (sigma d)) := by
  let B : ℝ → ℝ := fun t => if t ≤ 1 then 4 * t ^ (s / 2) else t ^ (s / 2 - 1)
  have hnear_pow : IntegrableOn (fun t : ℝ => t ^ (s / 2)) (Set.Ioc 0 1) volume := by
    apply (integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).mpr
    simpa only [Real.rpow_eq_pow] using ((part5_power_integrals (s / 2) 1 zero_lt_one).1 (by linarith)).1
  have hnear : IntegrableOn B (Set.Ioc 0 1) volume :=
    (hnear_pow.const_mul 4).congr (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => by
      simp only [B, if_pos ht.2]))
  have htail_pow : IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1)) (Set.Ioi 1) volume := by
    simpa only [Real.rpow_eq_pow] using ((part5_power_integrals (s / 2 - 1) 1 zero_lt_one).2 (by linarith)).1
  have htail : IntegrableOn B (Set.Ioi 1) volume :=
    htail_pow.congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => by
      simp only [B, if_neg (not_le.mpr (show 1 < t from ht))]))
  have hB : IntegrableOn B (Set.Ioi 0) volume := by
    simpa only [Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one)] using hnear.union htail
  have hBprod : Integrable (fun p : ℝ × Sphere d => B p.1)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (sigma d)) := hB.comp_fst (sigma d)
  have hdist (y : Sphere d) : dist (northPole d) y ≤ 2 := by
    simpa only [unitSphereN_dist_eq] using (unitSphereN_geometry (northPole d) y).2.1
  have hsq (y : Sphere d) : dist (northPole d) y ^ 2 ≤ 4 := by
    nlinarith only [hdist y, dist_nonneg (x := northPole d) (y := y)]
  have hdiff (t : ℝ) (ht : 0 < t) (y : Sphere d) :
      |Real.exp (-t * dist (northPole d) y ^ 2) - 1| ≤ min (4 * t) 1 := by
    have he := part5_exp_difference_bound (t * dist (northPole d) y ^ 2)
      (mul_nonneg ht.le (sq_nonneg _))
    rw [neg_mul, abs_sub_comm, abs_of_nonneg he.1]
    exact he.2.trans (min_le_min (by
      nlinarith only [mul_nonneg ht.le (sub_nonneg.mpr (hsq y))]) le_rfl)
  have hpower (t : ℝ) (ht : 0 < t) : (4 * t) * t ^ (s / 2 - 1) = 4 * t ^ (s / 2) := by
    rw [mul_assoc, mul_comm t, ← Real.rpow_add_one ht.ne', sub_add_cancel]
  have hbound (t : ℝ) (ht : 0 < t) (y : Sphere d) :
      ‖part5_gaussian_total_representatives_negative s t y‖ ≤ B t := by
    simp only [part5_gaussian_total_representatives_negative, if_pos ht, Real.rpow_eq_pow,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le (s / 2 - 1))]
    by_cases h1 : t ≤ 1
    · simpa only [B, if_pos h1, hpower t ht] using
        mul_le_mul_of_nonneg_right ((hdiff t ht y).trans (min_le_left _ _))
          (Real.rpow_nonneg ht.le (s / 2 - 1))
    simpa only [B, if_neg h1, one_mul] using
      mul_le_mul_of_nonneg_right ((hdiff t ht y).trans (min_le_right _ _))
        (Real.rpow_nonneg ht.le (s / 2 - 1))
  have htpos : ∀ᵐ p : ℝ × Sphere d ∂(volume.restrict (Set.Ioi (0 : ℝ))).prod (sigma d), 0 < p.1 :=
    (Measure.ae_prod_iff_ae_ae (isOpen_lt continuous_const continuous_fst).measurableSet).2
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => Filter.Eventually.of_forall (fun _ => ht)))
  exact hBprod.mono' (part5_gaussian_total_measurable d hd s).2.1.aestronglyMeasurable
    (htpos.mono (fun p hp => hbound p.1 hp p.2))

/- lem:negative-continuum -/
theorem part5_negative_continuum (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : -2 < s) (hs0 : s < 0) :
  IntegrableOn (fun t : ℝ => (gaussianAverage d t - 1) * Real.rpow t (s / 2 - 1)) (Set.Ioi 0) volume ∧ continuousEnergy d s = part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), (gaussianAverage d t - 1) * Real.rpow t (s / 2 - 1) ∂volume) := by
  let G : ℝ → Sphere d → ℝ := part5_gaussian_total_representatives_negative s
  have hprod : Integrable (Function.uncurry G) ((volume.restrict (Set.Ioi (0 : ℝ))).prod (sigma d)) :=
    part5_negative_product_integrable d hd s hs hs0
  have hsection_value (t : ℝ) (ht : 0 < t) : (∫ y, G t y ∂sigma d) =
      (gaussianAverage d t - 1) * Real.rpow t (s / 2 - 1) := by
    simp only [G, part5_gaussian_total_representatives_negative, if_pos ht, integral_mul_const]
    rw [integral_sub (gaussian_center d hd t (northPole d)).1 (integrable_const (1 : ℝ)),
      integral_const, probReal_univ, one_smul, gaussianAverage]
  constructor
  · exact hprod.integral_prod_left.congr
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hsection_value t ht))
  have hkernel (y : Sphere d) : kernel d s (northPole d) y =
      part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), G t y ∂volume) := by
    by_cases hy : y = northPole d
    · simp [hy, G, part5_gaussian_total_representatives_negative, kernel_diag]
    have htime : (fun t => G t y) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun t => (Real.exp (-t * dist (northPole d) y ^ 2) - 1) * Real.rpow t (s / 2 - 1)) :=
      ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => by
        simp only [G, part5_gaussian_total_representatives_negative, if_pos (show 0 < t from ht)])
    rw [kernel_ne_zero_offDiag hs0.ne (Ne.symm hy), integral_congr_ae htime]
    exact (part5_negative_pointwise s (dist (northPole d) y) hs hs0 dist_nonneg).2
  unfold continuousEnergy
  simp_rw [hkernel]
  rw [integral_const_mul, ← integral_integral_swap hprod]
  exact congrArg (fun z : ℝ => part5_riesz_gamma_coefficient s * z)
    (integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hsection_value t ht)))

/- lem:log-section-norm -/
theorem part5_log_section_norm (d : ℕ) (hd : 2 ≤ d) :
  (∀ y : Sphere d, IntegrableOn (fun t : ℝ => part5_gaussian_total_representatives_logarithmic t y) (Set.Ioi 0) volume ∧ (∫ t in Set.Ioi (0 : ℝ), |part5_gaussian_total_representatives_logarithmic t y| ∂volume) = 2 * |Real.log (dist (northPole d) y)|) ∧ Integrable (fun y : Sphere d => 2 * |Real.log (dist (northPole d) y)|) (sigma d) := by
  constructor
  · intro y
    by_cases hy : y = northPole d
    · simp [hy, part5_gaussian_total_representatives_logarithmic]
    have hpoint := part5_log_pointwise (dist (northPole d) y) (dist_pos.mpr (Ne.symm hy))
    have heq : (fun t : ℝ => part5_gaussian_total_representatives_logarithmic t y) =ᵐ[volume.restrict (Set.Ioi 0)]
        (fun t => (Real.exp (-t * dist (northPole d) y ^ 2) - Real.exp (-t)) / t) :=
      ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => by
        simp only [part5_gaussian_total_representatives_logarithmic,
          if_pos (show 0 < t from ht), if_neg hy])
    refine ⟨hpoint.1.congr heq.symm, ?_⟩
    calc
      (∫ t in Set.Ioi (0 : ℝ), |part5_gaussian_total_representatives_logarithmic t y|) =
          ∫ t in Set.Ioi (0 : ℝ), |Real.exp (-t * dist (northPole d) y ^ 2) - Real.exp (-t)| / t :=
        integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => by
          simp only [part5_gaussian_total_representatives_logarithmic,
            if_pos (show 0 < t from ht), if_neg hy, abs_div,
            abs_of_pos (show 0 < t from ht)]))
      _ = 2 * |Real.log (dist (northPole d) y)| := hpoint.2.2
  have hint := (kernel_section_integrable d hd 0 (by exact_mod_cast (by omega : 0 < d))
    (northPole d)).abs.const_mul 2
  refine hint.congr (Filter.Eventually.of_forall (fun y => ?_))
  by_cases hy : y = northPole d
  · simp [hy, kernel_diag]
  simp only [kernel_zero_offDiag (Ne.symm hy), abs_neg]

/- lem:log-product-integrable -/
theorem part5_log_product_integrable (d : ℕ) (hd : 2 ≤ d) :
  Integrable (fun p : ℝ × Sphere d => part5_gaussian_total_representatives_logarithmic p.1 p.2) ((volume.restrict (Set.Ioi (0 : ℝ))).prod (sigma d)) := by
  apply (integrable_prod_iff' (part5_gaussian_total_measurable d hd 0).2.2.1.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun y => ((part5_log_section_norm d hd).1 y).1), ?_⟩
  exact (part5_log_section_norm d hd).2.congr (Filter.Eventually.of_forall (fun y => by
    simpa only [Real.norm_eq_abs] using ((part5_log_section_norm d hd).1 y).2.symm))

/- lem:log-continuum -/
theorem part5_log_continuum (d : ℕ) (hd : 2 ≤ d) :
  IntegrableOn (fun t : ℝ => (gaussianAverage d t - Real.exp (-t)) / t) (Set.Ioi 0) volume ∧ continuousEnergy d 0 = (1 / 2 : ℝ) * (∫ t in Set.Ioi (0 : ℝ), (gaussianAverage d t - Real.exp (-t)) / t ∂volume) := by
  let G : ℝ → Sphere d → ℝ := part5_gaussian_total_representatives_logarithmic
  have hprod : Integrable (Function.uncurry G) ((volume.restrict (Set.Ioi (0 : ℝ))).prod (sigma d)) :=
    part5_log_product_integrable d hd
  have hsection_value (t : ℝ) (ht : 0 < t) : (∫ y, G t y ∂sigma d) =
      (gaussianAverage d t - Real.exp (-t)) / t := by
    rw [integral_congr_ae ((part5_gaussian_total_measurable d hd 0).2.2.2.2 t ht).2]
    rw [integral_div, integral_sub (gaussian_center d hd t (northPole d)).1
      (integrable_const (Real.exp (-t))), integral_const, probReal_univ, one_smul, gaussianAverage]
  refine ⟨hprod.integral_prod_left.congr
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hsection_value t ht)), ?_⟩
  have hkernel (y : Sphere d) : kernel d 0 (northPole d) y =
      (1 / 2 : ℝ) * (∫ t in Set.Ioi (0 : ℝ), G t y ∂volume) := by
    by_cases hy : y = northPole d
    · simp [hy, G, part5_gaussian_total_representatives_logarithmic, kernel_diag]
    have htime : (fun t => G t y) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun t => (Real.exp (-t * dist (northPole d) y ^ 2) - Real.exp (-t)) / t) :=
      ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => by
        simp only [G, part5_gaussian_total_representatives_logarithmic,
          if_pos (show 0 < t from ht), if_neg hy])
    rw [kernel_zero_offDiag (Ne.symm hy), integral_congr_ae htime]
    exact (part5_log_pointwise (dist (northPole d) y) (dist_pos.mpr (Ne.symm hy))).2.1
  unfold continuousEnergy
  simp_rw [hkernel]
  rw [integral_const_mul, ← integral_integral_swap hprod]
  exact congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
    (integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hsection_value t ht)))

/- lem:negative-discrepancy-identity -/
theorem part5_negative_discrepancy_identity (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : -2 < s) (hs0 : s < 0) (M : ℕ) (x : Config d M) (hx : Function.Injective x) :
  IntegrableOn (fun t : ℝ => part5_gaussian_discrepancy x t * Real.rpow t (s / 2 - 1)) (Set.Ioi 0) volume ∧ finiteEnergy s x - (M : ℝ) ^ 2 * continuousEnergy d s = part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), part5_gaussian_discrepancy x t * Real.rpow t (s / 2 - 1) ∂volume) := by
  let F : Fin M → Fin M → ℝ → ℝ := fun i j t =>
    (Real.exp (-t * dist (x i) (x j) ^ 2) - 1) * Real.rpow t (s / 2 - 1)
  have hFint (i j : Fin M) : IntegrableOn (F i j) (Set.Ioi 0) volume :=
    (part5_negative_pointwise s (dist (x i) (x j)) hs hs0 dist_nonneg).1
  have hFvalue (i j : Fin M) : (if i = j then 0 else kernel d s (x i) (x j)) =
      part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), F i j t) := by
    by_cases hij : i = j
    · simp [hij, F]
    simpa only [if_neg hij, kernel_ne_zero_offDiag hs0.ne (hx.ne hij)] using
      (part5_negative_pointwise s (dist (x i) (x j)) hs hs0 dist_nonneg).2
  have hrow (i : Fin M) : IntegrableOn (fun t => ∑ j : Fin M, F i j t) (Set.Ioi 0) volume :=
    integrable_finsetSum Finset.univ (fun j _ => hFint i j)
  have hsum : IntegrableOn (fun t => ∑ i : Fin M, ∑ j : Fin M, F i j t) (Set.Ioi 0) volume :=
    integrable_finsetSum Finset.univ (fun i _ => hrow i)
  have hcont := part5_negative_continuum d hd s hs hs0
  have hdecomp (t : ℝ) : part5_gaussian_discrepancy x t * Real.rpow t (s / 2 - 1) =
      (∑ i : Fin M, ∑ j : Fin M, F i j t) -
        (M : ℝ) ^ 2 * ((gaussianAverage d t - 1) * Real.rpow t (s / 2 - 1)) := by
    simp only [part5_gaussian_discrepancy, F, ← Finset.sum_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp_rw [hdecomp]
  refine ⟨hsum.sub (hcont.1.const_mul ((M : ℝ) ^ 2)), ?_⟩
  rw [integral_sub hsum (hcont.1.const_mul ((M : ℝ) ^ 2)), integral_const_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => hrow i)]
  have hrowvalue (i : Fin M) : (∫ t in Set.Ioi (0 : ℝ), ∑ j : Fin M, F i j t) =
      ∑ j : Fin M, ∫ t in Set.Ioi (0 : ℝ), F i j t :=
    integral_finsetSum Finset.univ (fun j _ => hFint i j)
  have henergy : finiteEnergy s x = ∑ i : Fin M, ∑ j : Fin M,
      part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), F i j t) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      by_cases hij : i = j <;> simpa [hij] using hFvalue i j))
  simp only [henergy, hrowvalue, hcont.2, ← Finset.mul_sum]
  ring

/- lem:log-discrepancy-identity -/
theorem part5_log_discrepancy_identity (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (x : Config d M) (hx : Function.Injective x) :
  IntegrableOn (fun t : ℝ => (part5_gaussian_discrepancy x t - (M : ℝ) * (1 - Real.exp (-t))) / t) (Set.Ioi 0) volume ∧ finiteEnergy 0 x - (M : ℝ) ^ 2 * continuousEnergy d 0 = (1 / 2 : ℝ) * (∫ t in Set.Ioi (0 : ℝ), (part5_gaussian_discrepancy x t - (M : ℝ) * (1 - Real.exp (-t))) / t ∂volume) := by
  let F : Fin M → Fin M → ℝ → ℝ := fun i j t =>
    if i = j then 0 else (Real.exp (-t * dist (x i) (x j) ^ 2) - Real.exp (-t)) / t
  have hFint (i j : Fin M) : IntegrableOn (F i j) (Set.Ioi 0) volume := by
    by_cases hij : i = j
    · simp [F, hij]
    simpa only [F, if_neg hij] using
      (part5_log_pointwise (dist (x i) (x j)) (dist_pos.mpr (hx.ne hij))).1
  have hFvalue (i j : Fin M) : (if i = j then 0 else kernel d 0 (x i) (x j)) =
      (1 / 2 : ℝ) * (∫ t in Set.Ioi (0 : ℝ), F i j t) := by
    by_cases hij : i = j
    · simp [F, hij]
    simpa only [F, if_neg hij, kernel_zero_offDiag (hx.ne hij)] using
      (part5_log_pointwise (dist (x i) (x j)) (dist_pos.mpr (hx.ne hij))).2.1
  have hrow (i : Fin M) : IntegrableOn (fun t => ∑ j : Fin M, F i j t) (Set.Ioi 0) volume :=
    integrable_finsetSum Finset.univ (fun j _ => hFint i j)
  have hsum : IntegrableOn (fun t => ∑ i : Fin M, ∑ j : Fin M, F i j t) (Set.Ioi 0) volume :=
    integrable_finsetSum Finset.univ (fun i _ => hrow i)
  have hcont := part5_log_continuum d hd
  have hFexpand (i j : Fin M) (t : ℝ) : F i j t =
      ((Real.exp (-t * dist (x i) (x j) ^ 2) - Real.exp (-t)) -
        (if i = j then 1 - Real.exp (-t) else 0)) / t := by
    by_cases hij : i = j <;> simp [F, hij]
  have hdecomp (t : ℝ) : (part5_gaussian_discrepancy x t - (M : ℝ) * (1 - Real.exp (-t))) / t =
      (∑ i : Fin M, ∑ j : Fin M, F i j t) -
        (M : ℝ) ^ 2 * ((gaussianAverage d t - Real.exp (-t)) / t) := by
    simp only [part5_gaussian_discrepancy, hFexpand, ← Finset.sum_div,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp_rw [hdecomp]
  refine ⟨hsum.sub (hcont.1.const_mul ((M : ℝ) ^ 2)), ?_⟩
  rw [integral_sub hsum (hcont.1.const_mul ((M : ℝ) ^ 2)), integral_const_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => hrow i)]
  have hrowvalue (i : Fin M) : (∫ t in Set.Ioi (0 : ℝ), ∑ j : Fin M, F i j t) =
      ∑ j : Fin M, ∫ t in Set.Ioi (0 : ℝ), F i j t :=
    integral_finsetSum Finset.univ (fun j _ => hFint i j)
  have henergy : finiteEnergy 0 x = ∑ i : Fin M, ∑ j : Fin M,
      (1 / 2 : ℝ) * (∫ t in Set.Ioi (0 : ℝ), F i j t) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      by_cases hij : i = j <;> simpa [hij] using hFvalue i j))
  simp only [henergy, hrowvalue, hcont.2, ← Finset.mul_sum]
  ring

/- P5-IFACE-001 -/
theorem part5_kernel_continuous_offDiagonal (d : ℕ) (s : ℝ) : ContinuousOn (fun p : Sphere d × Sphere d => kernel d s p.1 p.2) {p | p.1 ≠ p.2} := by
  by_cases hs : s = 0
  · have hbranch : ContinuousOn (fun p : Sphere d × Sphere d =>
        -Real.log (dist p.1 p.2)) {p | p.1 ≠ p.2} :=
      (continuous_dist.continuousOn.log
        (fun p hp => dist_ne_zero.mpr hp)).neg
    refine hbranch.congr ?_
    intro p hp
    change p.1 ≠ p.2 at hp
    simp [kernel, hp, hs]
  · have hbranch : ContinuousOn (fun p : Sphere d × Sphere d =>
        (1 / s) * Real.rpow (dist p.1 p.2) (-s)) {p | p.1 ≠ p.2} :=
      (continuous_dist.continuousOn.rpow_const
        (fun p hp => Or.inl (dist_ne_zero.mpr hp))).const_mul (1 / s)
    refine hbranch.congr ?_
    intro p hp
    change p.1 ≠ p.2 at hp
    simp [kernel, hp, hs]

/- def:energy-constants -/
noncomputable def part5_energy_constants_positive (d : ℕ) (s : ℝ) : ℝ := by
  classical
  exact (
    2 * part5_riesz_gamma_coefficient s * gaussianAverageConstant d / ((d : ℝ) - s) + 2 * part5_riesz_gamma_coefficient s / s
  )

/- def:energy-constants -/
noncomputable def part5_energy_constants_negative (d : ℕ) (s : ℝ) : ℝ := by
  classical
  exact (
    part5_riesz_gamma_coefficient s * (-1 / s) * Real.rpow (2 * gaussianAverageConstant d) (s / (d : ℝ))
  )

/- def:energy-constants -/
noncomputable def part5_energy_constants_log (d : ℕ) : ℝ := by
  classical
  exact (
    (1 / 2 : ℝ) + gaussianAverageConstant d / (d : ℝ)
  )

/- lem:energy-constant-signs -/
theorem part5_energy_constant_signs (d : ℕ) (hd : 2 ≤ d) : (∀ s : ℝ, 0 < s → s < (d : ℝ) → 0 < part5_energy_constants_positive d s) ∧ (∀ s : ℝ, -2 < s → s < 0 → 0 < part5_energy_constants_negative d s) ∧ 0 < part5_energy_constants_log d ∧ (∀ s : ℝ, -2 < s → s < (d : ℝ) → 0 < 1 + s / (d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le (by norm_num) hdR
  have hC : 0 < gaussianAverageConstant d := (gaussian_average d hd).1
  refine ⟨fun s hs hsd => ?_, fun s hs hs0 => ?_, ?_, fun s hs hsd => ?_⟩
  · have hcs := part5_riesz_gamma_positive s (Or.inl hs)
    exact add_pos
      (div_pos (mul_pos (mul_pos (by norm_num) hcs) hC) (sub_pos.mpr hsd))
      (div_pos (mul_pos (by norm_num) hcs) hs)
  · have hcs := part5_riesz_gamma_positive s (Or.inr ⟨hs, hs0⟩)
    exact mul_pos (mul_pos hcs (div_pos_of_neg_of_neg (by norm_num) hs0))
      (Real.rpow_pos_of_pos (mul_pos (by norm_num) hC) _)
  · exact add_pos (by norm_num) (div_pos hC hdpos)
  · simpa only [add_div, div_self hdpos.ne'] using
      (div_pos (by linarith : 0 < (d : ℝ) + s) hdpos)

/- lem:positive-energy-truncation -/
theorem part5_positive_energy_truncation (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (M : ℕ) (x : Config d M) (hx : Function.Injective x) (T : ℝ) (hT : 0 < T) : continuousEnergy d s * (M : ℝ) ^ 2 - part5_riesz_gamma_coefficient s * (M : ℝ) ^ 2 * (∫ t in Set.Ioi T, gaussianAverage d t * Real.rpow t (s / 2 - 1) ∂volume) - (2 * part5_riesz_gamma_coefficient s / s) * (M : ℝ) * Real.rpow T (s / 2) ≤ finiteEnergy s x := by
  let F : Fin M → Fin M → ℝ → ℝ := fun i j t =>
    if i = j then 0 else Real.exp (-t * dist (x i) (x j) ^ 2) * Real.rpow t (s / 2 - 1)
  have hFint (i j : Fin M) : IntegrableOn (F i j) (Set.Ioi 0) volume := by
    by_cases hij : i = j
    · simp [F, hij]
    · simpa only [F, if_neg hij] using
        (part5_positive_pointwise s (dist (x i) (x j)) hs (dist_pos.mpr (hx.ne hij))).1
  have hFvalue (i j : Fin M) : (if i = j then 0 else kernel d s (x i) (x j)) =
      part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), F i j t) := by
    by_cases hij : i = j
    · simp [hij, F]
    · simpa only [F, if_neg hij, kernel_ne_zero_offDiag hs.ne' (hx.ne hij)] using
        (part5_positive_pointwise s (dist (x i) (x j)) hs (dist_pos.mpr (hx.ne hij))).2
  have hrow (i : Fin M) : IntegrableOn (fun t => ∑ j : Fin M, F i j t) (Set.Ioi 0) volume :=
    integrable_finsetSum Finset.univ (fun j _ => hFint i j)
  have hsum : IntegrableOn (fun t => ∑ i : Fin M, ∑ j : Fin M, F i j t) (Set.Ioi 0) volume :=
    integrable_finsetSum Finset.univ (fun i _ => hrow i)
  have hrowvalue (i : Fin M) : (∫ t in Set.Ioi (0 : ℝ), ∑ j : Fin M, F i j t) =
      ∑ j : Fin M, ∫ t in Set.Ioi (0 : ℝ), F i j t :=
    integral_finsetSum Finset.univ (fun j _ => hFint i j)
  have henergy : finiteEnergy s x = ∑ i : Fin M, ∑ j : Fin M,
      part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), F i j t) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hij : i = j
    all_goals simpa [hij] using hFvalue i j
  have henergy_integral : finiteEnergy s x = part5_riesz_gamma_coefficient s *
      (∫ t in Set.Ioi (0 : ℝ), ∑ i : Fin M, ∑ j : Fin M, F i j t) := by
    simpa only [integral_finsetSum Finset.univ (fun i _ => hrow i), hrowvalue,
      Finset.mul_sum] using henergy
  have hFnonneg (i j : Fin M) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ F i j t := by
    dsimp only [F]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht _)
  have htruncate : (∫ t in Set.Ioo (0 : ℝ) T, ∑ i : Fin M, ∑ j : Fin M, F i j t) ≤
      (∫ t in Set.Ioi (0 : ℝ), ∑ i : Fin M, ∑ j : Fin M, F i j t) :=
    setIntegral_mono_set hsum
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht =>
        Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hFnonneg i j t ht.le))))
      (Filter.Eventually.of_forall (fun t (ht : t ∈ Set.Ioo (0 : ℝ) T) => ht.1))
  let G : ℝ → ℝ := fun t => (M : ℝ) ^ 2 * (gaussianAverage d t * Real.rpow t (s / 2 - 1)) -
    (M : ℝ) * Real.rpow t (s / 2 - 1)
  have hJ := part5_positive_J_integrable d hd s hs hsd
  have hpower := (part5_power_integrals (s / 2 - 1) T hT).1 (by linarith)
  have hGint : IntegrableOn G (Set.Ioo 0 T) volume :=
    ((hJ.mono_set (fun t (ht : t ∈ Set.Ioo (0 : ℝ) T) => ht.1)).const_mul ((M : ℝ) ^ 2)).sub
      (hpower.1.const_mul (M : ℝ))
  have hpoint (t : ℝ) (ht : 0 < t) : G t ≤ ∑ i : Fin M, ∑ j : Fin M, F i j t := by
    convert (mul_le_mul_of_nonneg_right (part5_gaussian_discrepancy_lower d hd M x t ht.le).2
      (Real.rpow_nonneg ht.le (s / 2 - 1))) using 1
    · rfl
    · simp only [G, sub_mul, mul_assoc]
      rfl
    · simp only [F, Finset.sum_mul, ite_mul, zero_mul]
      rfl
  have hcompare : (∫ t in Set.Ioo (0 : ℝ) T, G t) ≤
      (∫ t in Set.Ioo (0 : ℝ) T, ∑ i : Fin M, ∑ j : Fin M, F i j t) :=
    integral_mono_ae hGint
      (hsum.mono_set (fun t (ht : t ∈ Set.Ioo (0 : ℝ) T) => ht.1))
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => hpoint t ht.1))
  have hsplit : (∫ t in Set.Ioo (0 : ℝ) T, gaussianAverage d t * Real.rpow t (s / 2 - 1)) =
      (∫ t in Set.Ioi (0 : ℝ), gaussianAverage d t * Real.rpow t (s / 2 - 1)) -
        (∫ t in Set.Ioi T, gaussianAverage d t * Real.rpow t (s / 2 - 1)) := by
    simpa only [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo] using
      (intervalIntegral.integral_Ioi_sub_Ioi hJ hT.le).symm
  have hpowvalue : (∫ t in Set.Ioo (0 : ℝ) T, Real.rpow t (s / 2 - 1)) =
      Real.rpow T (s / 2) / (s / 2) := by
    simpa only [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo,
      sub_add_cancel] using hpower.2
  have hbound : part5_riesz_gamma_coefficient s * (∫ t in Set.Ioo (0 : ℝ) T, G t) ≤
      finiteEnergy s x := by
    rw [henergy_integral]
    exact mul_le_mul_of_nonneg_left (hcompare.trans htruncate)
      (part5_riesz_gamma_positive s (Or.inl hs)).le
  change part5_riesz_gamma_coefficient s *
    (∫ t in Set.Ioo (0 : ℝ) T, (M : ℝ) ^ 2 *
      (gaussianAverage d t * Real.rpow t (s / 2 - 1)) - (M : ℝ) * Real.rpow t (s / 2 - 1)) ≤
    finiteEnergy s x at hbound
  rw [integral_sub
    ((hJ.mono_set (fun t (ht : t ∈ Set.Ioo (0 : ℝ) T) => ht.1)).const_mul ((M : ℝ) ^ 2))
    (hpower.1.const_mul (M : ℝ)), integral_const_mul, integral_const_mul, hsplit, hpowvalue] at hbound
  rw [part5_positive_continuum d hd s hs hsd]
  convert hbound using 1
  ring

/- lem:positive-energy-tail -/
theorem part5_positive_energy_tail (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (T : ℝ) (hT : 0 < T) : (∫ t in Set.Ioi T, gaussianAverage d t * Real.rpow t (s / 2 - 1) ∂volume) ≤ 2 * gaussianAverageConstant d * Real.rpow T (-((d : ℝ) - s) / 2) / ((d : ℝ) - s) := by
  have hJ := (part5_positive_J_integrable d hd s hs hsd).mono_set (Set.Ioi_subset_Ioi hT.le)
  have hpower := (part5_power_integrals ((s - (d : ℝ)) / 2 - 1) T hT).2 (by linarith)
  have hmul (t : ℝ) (ht : 0 < t) : Real.rpow t (-(d : ℝ) / 2) *
      Real.rpow t (s / 2 - 1) = Real.rpow t ((s - (d : ℝ)) / 2 - 1) :=
    (show Real.rpow t (-(d : ℝ) / 2 + (s / 2 - 1)) =
      Real.rpow t (-(d : ℝ) / 2) * Real.rpow t (s / 2 - 1) from
      Real.rpow_add ht _ _).symm.trans (congrArg (Real.rpow t) (by ring))
  have hpoint (t : ℝ) (ht : T < t) : gaussianAverage d t * Real.rpow t (s / 2 - 1) ≤
      gaussianAverageConstant d * Real.rpow t ((s - (d : ℝ)) / 2 - 1) := by
    calc
      gaussianAverage d t * Real.rpow t (s / 2 - 1) ≤
          (gaussianAverageConstant d * Real.rpow t (-(d : ℝ) / 2)) * Real.rpow t (s / 2 - 1) :=
        mul_le_mul_of_nonneg_right ((gaussian_average d hd).2.1 t (hT.trans ht)).2
          (show 0 ≤ Real.rpow t (s / 2 - 1) from Real.rpow_nonneg (hT.trans ht).le _)
      _ = gaussianAverageConstant d * Real.rpow t ((s - (d : ℝ)) / 2 - 1) := by
        rw [mul_assoc, hmul t (hT.trans ht)]
  have hbound : (∫ t in Set.Ioi T, gaussianAverage d t * Real.rpow t (s / 2 - 1)) ≤
      (∫ t in Set.Ioi T, gaussianAverageConstant d * Real.rpow t ((s - (d : ℝ)) / 2 - 1)) :=
    integral_mono_ae hJ (hpower.1.const_mul (gaussianAverageConstant d))
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hpoint t ht))
  rw [integral_const_mul, hpower.2,
    show (s - (d : ℝ)) / 2 - 1 + 1 = -((d : ℝ) - s) / 2 by ring] at hbound
  convert hbound using 1
  field_simp [(sub_pos.mpr hsd).ne']

/- lem:energy-cutoff-powers -/
theorem part5_energy_cutoff_powers (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (hM : 1 ≤ M) (s : ℝ) : let T := Real.rpow (M : ℝ) (2 / (d : ℝ)); 1 ≤ T ∧ (M : ℝ) * Real.rpow T (s / 2) = Real.rpow (M : ℝ) (1 + s / (d : ℝ)) ∧ (M : ℝ) ^ 2 * Real.rpow T (-((d : ℝ) - s) / 2) = Real.rpow (M : ℝ) (1 + s / (d : ℝ)) ∧ (M : ℝ) ^ 2 * Real.rpow T (-(d : ℝ) / 2) = (M : ℝ) ∧ Real.log T = (2 / (d : ℝ)) * Real.log (M : ℝ) := by
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hd)
  have hMpos : (0 : ℝ) < (M : ℝ) := zero_lt_one.trans_le hMr
  have hpow (a b : ℝ) :
      Real.rpow (M : ℝ) a * Real.rpow (Real.rpow (M : ℝ) (2 / (d : ℝ))) b =
        Real.rpow (M : ℝ) (a + (2 / (d : ℝ)) * b) :=
    (congrArg (fun y : ℝ => Real.rpow (M : ℝ) a * y)
      (Real.rpow_mul hMpos.le (2 / (d : ℝ)) b).symm).trans
        (Real.rpow_add hMpos a ((2 / (d : ℝ)) * b)).symm
  refine ⟨Real.one_le_rpow hMr (div_nonneg (by norm_num) hdpos.le),
    ?_, ?_, ?_, Real.log_rpow hMpos _⟩
  · simpa only [show Real.rpow (M : ℝ) (1 : ℝ) = (M : ℝ) from Real.rpow_one _,
      show (1 : ℝ) + (2 / (d : ℝ)) * (s / 2) = 1 + s / (d : ℝ) by ring]
      using hpow 1 (s / 2)
  · simpa only [show Real.rpow (M : ℝ) (2 : ℝ) = (M : ℝ) ^ 2 from
        Real.rpow_natCast _ 2,
      show (2 : ℝ) + (2 / (d : ℝ)) * (-((d : ℝ) - s) / 2) =
        1 + s / (d : ℝ) by
          field_simp [hdpos.ne']
          ring]
      using hpow 2 (-((d : ℝ) - s) / 2)
  · simpa only [show Real.rpow (M : ℝ) (2 : ℝ) = (M : ℝ) ^ 2 from
        Real.rpow_natCast _ 2,
      show (2 : ℝ) + (2 / (d : ℝ)) * (-(d : ℝ) / 2) = 1 by
        field_simp [hdpos.ne']
        norm_num,
      show Real.rpow (M : ℝ) (1 : ℝ) = (M : ℝ) from Real.rpow_one _]
      using hpow 2 (-(d : ℝ) / 2)

/- lem:positive-energy-config -/
theorem part5_positive_energy_config (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (M : ℕ) (x : Config d M) (hx : Function.Injective x) : continuousEnergy d s * (M : ℝ) ^ 2 - part5_energy_constants_positive d s * Real.rpow (M : ℝ) (1 + s / (d : ℝ)) ≤ finiteEnergy s x := by
  have hexp : 0 < 1 + s / (d : ℝ) :=
    (part5_energy_constant_signs d hd).2.2.2 s (by linarith) hsd
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simpa only [Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
      sub_self, show Real.rpow (0 : ℝ) (1 + s / (d : ℝ)) = 0 from
        Real.zero_rpow hexp.ne'] using (finiteEnergy_zero d s x).symm.le
  have hcut := part5_energy_cutoff_powers d hd M hM s
  have htrunc := part5_positive_energy_truncation d hd s hs hsd M x hx _
    (zero_lt_one.trans_le hcut.1)
  have htail := part5_positive_energy_tail d hd s hs hsd _
    (zero_lt_one.trans_le hcut.1)
  have hweighted := mul_le_mul_of_nonneg_left htail
    (mul_nonneg (part5_riesz_gamma_positive s (Or.inl hs)).le (sq_nonneg (M : ℝ)))
  have hbound := (sub_le_sub_right (sub_le_sub_left hweighted
    (continuousEnergy d s * (M : ℝ) ^ 2)) _).trans htrunc
  convert hbound using 1
  · rfl
  dsimp only [part5_energy_constants_positive]
  linear_combination
    (2 * part5_riesz_gamma_coefficient s * gaussianAverageConstant d / ((d : ℝ) - s)) *
      hcut.2.2.1 + (2 * part5_riesz_gamma_coefficient s / s) * hcut.2.1

/- lem:negative-energy-threshold -/
theorem part5_negative_energy_threshold (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (hM : 1 ≤ M) (x : Config d M) : let T := Real.rpow (2 * gaussianAverageConstant d * (M : ℝ)) (2 / (d : ℝ)); 0 < T ∧ ∀ t : ℝ, T ≤ t → (M : ℝ) ^ 2 * gaussianAverage d t ≤ (M : ℝ) / 2 ∧ (M : ℝ) / 2 ≤ part5_gaussian_discrepancy x t := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hd)
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hM)
  have hCpos : 0 < gaussianAverageConstant d := (gaussian_average d hd).1
  have hbase : 0 < 2 * gaussianAverageConstant d * (M : ℝ) :=
    mul_pos (mul_pos (by norm_num) hCpos) hMpos
  have hT : 0 < Real.rpow (2 * gaussianAverageConstant d * (M : ℝ)) (2 / (d : ℝ)) :=
    Real.rpow_pos_of_pos hbase _
  have hprod : (2 / (d : ℝ)) * (-(d : ℝ) / 2) = -1 := by
    field_simp [hdpos.ne']
  have hTpow : Real.rpow
      (Real.rpow (2 * gaussianAverageConstant d * (M : ℝ)) (2 / (d : ℝ)))
      (-(d : ℝ) / 2) = (2 * gaussianAverageConstant d * (M : ℝ))⁻¹ :=
    (Real.rpow_mul hbase.le (2 / (d : ℝ)) (-(d : ℝ) / 2)).symm.trans
      ((congrArg (Real.rpow (2 * gaussianAverageConstant d * (M : ℝ))) hprod).trans
        (Real.rpow_neg_one _))
  have hcoeff : (M : ℝ) ^ 2 *
      (gaussianAverageConstant d * (2 * gaussianAverageConstant d * (M : ℝ))⁻¹) =
        (M : ℝ) / 2 := by
    field_simp [hCpos.ne', hMpos.ne']
  refine ⟨hT, fun t ht => ?_⟩
  have hpower : Real.rpow t (-(d : ℝ) / 2) ≤
      (2 * gaussianAverageConstant d * (M : ℝ))⁻¹ :=
    (show Real.rpow t (-(d : ℝ) / 2) ≤ Real.rpow
        (Real.rpow (2 * gaussianAverageConstant d * (M : ℝ)) (2 / (d : ℝ)))
        (-(d : ℝ) / 2) from
      Real.rpow_le_rpow_of_nonpos hT ht (by linarith)).trans_eq hTpow
  have hJ : (M : ℝ) ^ 2 * gaussianAverage d t ≤ (M : ℝ) / 2 :=
    (mul_le_mul_of_nonneg_left
      (((gaussian_average d hd).2.1 t (hT.trans_le ht)).2.trans
        (mul_le_mul_of_nonneg_left hpower hCpos.le))
      (sq_nonneg (M : ℝ))).trans_eq hcoeff
  exact ⟨hJ, by
    linarith only [hJ, (part5_gaussian_discrepancy_lower d hd M x t (hT.trans_le ht).le).1]⟩

/- lem:negative-energy-config -/
theorem part5_negative_energy_config (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : -2 < s) (hs0 : s < 0) (M : ℕ) (x : Config d M) (hx : Function.Injective x) : continuousEnergy d s * (M : ℝ) ^ 2 + part5_energy_constants_negative d s * Real.rpow (M : ℝ) (1 + s / (d : ℝ)) ≤ finiteEnergy s x := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hd)
  have hexp : 0 < 1 + s / (d : ℝ) :=
    (part5_energy_constant_signs d hd).2.2.2 s hs (hs0.trans hdpos)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simpa only [Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
      add_zero, show Real.rpow (0 : ℝ) (1 + s / (d : ℝ)) = 0 from
        Real.zero_rpow hexp.ne'] using (finiteEnergy_zero d s x).symm.le
  let T : ℝ := Real.rpow (2 * gaussianAverageConstant d * (M : ℝ)) (2 / (d : ℝ))
  have hthreshold := part5_negative_energy_threshold d hd M hM x
  have hT : 0 < T := hthreshold.1
  have hrep := part5_negative_discrepancy_identity d hd s hs hs0 M x hx
  have hpower := (part5_power_integrals (s / 2 - 1) T hT).2 (by linarith)
  have hnonneg (t : ℝ) (ht : 0 < t) :
      0 ≤ part5_gaussian_discrepancy x t * Real.rpow t (s / 2 - 1) :=
    mul_nonneg (part5_gaussian_positive d hd M x t ht.le).2
      (show 0 ≤ Real.rpow t (s / 2 - 1) from Real.rpow_nonneg ht.le _)
  have hrestrict :
      (∫ t in Set.Ioi T, part5_gaussian_discrepancy x t * Real.rpow t (s / 2 - 1)) ≤
        (∫ t in Set.Ioi (0 : ℝ), part5_gaussian_discrepancy x t * Real.rpow t (s / 2 - 1)) :=
    setIntegral_mono_set hrep.1
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hnonneg t ht))
      (Filter.Eventually.of_forall (fun t (ht : t ∈ Set.Ioi T) => hT.trans ht))
  have hcompare :
      (∫ t in Set.Ioi T, ((M : ℝ) / 2) * Real.rpow t (s / 2 - 1)) ≤
        (∫ t in Set.Ioi T, part5_gaussian_discrepancy x t * Real.rpow t (s / 2 - 1)) :=
    integral_mono_ae (hpower.1.const_mul ((M : ℝ) / 2))
      (hrep.1.mono_set (Set.Ioi_subset_Ioi hT.le))
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht =>
        mul_le_mul_of_nonneg_right (hthreshold.2 t ht.le).2
          (show 0 ≤ Real.rpow t (s / 2 - 1) from
            Real.rpow_nonneg (hT.trans ht).le _)))
  have hbound := mul_le_mul_of_nonneg_left (hcompare.trans hrestrict)
    (part5_riesz_gamma_positive s (Or.inr ⟨hs, hs0⟩)).le
  simp only [integral_const_mul, hpower.2, sub_add_cancel] at hbound
  rw [← hrep.2] at hbound
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hCpos : 0 < 2 * gaussianAverageConstant d :=
    mul_pos (by norm_num) (gaussian_average d hd).1
  have hTpow : Real.rpow T (s / 2) =
      Real.rpow (2 * gaussianAverageConstant d) (s / (d : ℝ)) *
        Real.rpow (M : ℝ) (s / (d : ℝ)) :=
    (show Real.rpow T (s / 2) =
        Real.rpow (2 * gaussianAverageConstant d * (M : ℝ))
          ((2 / (d : ℝ)) * (s / 2)) from
      (Real.rpow_mul (mul_nonneg hCpos.le hMpos.le) _ _).symm).trans
      ((congrArg (Real.rpow (2 * gaussianAverageConstant d * (M : ℝ)))
        (show (2 / (d : ℝ)) * (s / 2) = s / (d : ℝ) by ring)).trans
        (Real.mul_rpow hCpos.le hMpos.le))
  have hMpow : (M : ℝ) * Real.rpow (M : ℝ) (s / (d : ℝ)) =
      Real.rpow (M : ℝ) (1 + s / (d : ℝ)) :=
    (congrArg (fun a : ℝ => a * Real.rpow (M : ℝ) (s / (d : ℝ)))
      (show Real.rpow (M : ℝ) (1 : ℝ) = (M : ℝ) from Real.rpow_one _)).symm.trans
      (Real.rpow_add hMpos 1 (s / (d : ℝ))).symm
  have hscale : part5_riesz_gamma_coefficient s *
      ((M : ℝ) / 2 * (-Real.rpow T (s / 2) / (s / 2))) =
        part5_energy_constants_negative d s * Real.rpow (M : ℝ) (1 + s / (d : ℝ)) := by
    dsimp only [part5_energy_constants_negative]
    rw [hTpow]
    field_simp [hs0.ne]
    rw [show ((d : ℝ) + s) / (d : ℝ) = 1 + s / (d : ℝ) by field_simp [hdpos.ne']]
    linear_combination
      (-part5_riesz_gamma_coefficient s * Real.rpow (2 * gaussianAverageConstant d) (s / (d : ℝ))) * hMpow
  rw [hscale] at hbound
  nlinarith only [hbound]

/- lem:log-small-integral -/
theorem part5_log_small_integral (T : ℝ) (hT : 1 ≤ T) : IntegrableOn (fun t : ℝ => (1 - Real.exp (-t)) / t) (Set.Ioo 0 T) volume ∧ (∫ t in Set.Ioo (0 : ℝ) T, (1 - Real.exp (-t)) / t ∂volume) ≤ 1 + Real.log T := by
  let f : ℝ → ℝ := fun t => (1 - Real.exp (-t)) / t
  have hfmeas : Measurable f :=
    (measurable_const.sub (Real.measurable_exp.comp measurable_neg)).div measurable_id
  have hnonneg (t : ℝ) (ht : 0 < t) : 0 ≤ f t :=
    div_nonneg (part5_exp_difference_bound t ht.le).1 ht.le
  have hone (t : ℝ) (ht : 0 < t) : f t ≤ 1 :=
    (div_le_one ht).2 ((part5_exp_difference_bound t ht.le).2.trans (min_le_left _ _))
  have hinv (t : ℝ) (ht : 0 < t) : f t ≤ 1 / t :=
    (div_le_div_iff_of_pos_right ht).2
      ((part5_exp_difference_bound t ht.le).2.trans (min_le_right _ _))
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 T) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hfint : IntegrableOn f (Set.Ioo 0 T) volume :=
    hconst.mono_nonneg hfmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => hnonneg t ht.1))
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => hone t ht.1))
  have hi01 : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
      (hfint.mono_set (Set.Ioo_subset_Ioo le_rfl hT))
  have hi1T : IntervalIntegrable f volume 1 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).2
      (hfint.mono_set (Set.Ioo_subset_Ioo (by norm_num) le_rfl))
  have hiinv : IntervalIntegrable (fun t : ℝ => 1 / t) volume 1 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT
      (continuousOn_const.div continuousOn_id
        (fun t ht => ne_of_gt (zero_lt_one.trans_le ht.1)))
  have hnear : (∫ t in (0 : ℝ)..1, f t) ≤ 1 := by
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using
      (intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
        hi01 (intervalIntegrable_const (c := (1 : ℝ))) (fun t ht => hone t ht.1))
  have hfar : (∫ t in (1 : ℝ)..T, f t) ≤ Real.log T := by
    simpa only [integral_one_div_of_pos zero_lt_one (zero_lt_one.trans_le hT), div_one] using
      (intervalIntegral.integral_mono_on_of_le_Ioo hT hi1T hiinv
        (fun t ht => hinv t (zero_lt_one.trans ht.1)))
  refine ⟨hfint, ?_⟩
  simpa only [intervalIntegral.integral_add_adjacent_intervals hi01 hi1T,
    intervalIntegral.integral_of_le (zero_le_one.trans hT), integral_Ioc_eq_integral_Ioo]
    using add_le_add hnear hfar

/- lem:log-energy-tail -/
theorem part5_log_energy_tail (d : ℕ) (hd : 2 ≤ d) (T : ℝ) (hT : 0 < T) : IntegrableOn (fun t : ℝ => gaussianAverage d t / t) (Set.Ioi T) volume ∧ (∫ t in Set.Ioi T, gaussianAverage d t / t ∂volume) ≤ (2 * gaussianAverageConstant d / (d : ℝ)) * Real.rpow T (-(d : ℝ) / 2) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hpow := (part5_power_integrals (-(d : ℝ) / 2 - 1) T hT).2 (by linarith)
  have hmajor := hpow.1.const_mul (gaussianAverageConstant d)
  have hfmeas : Measurable (fun t : ℝ => gaussianAverage d t / t) :=
    (part5_J_continuous d hd).2.1.div measurable_id
  have hnonneg (t : ℝ) (ht : 0 < t) : 0 ≤ gaussianAverage d t / t :=
    div_nonneg ((gaussian_average d hd).2.1 t ht).1.le ht.le
  have hbound (t : ℝ) (ht : 0 < t) : gaussianAverage d t / t ≤
      gaussianAverageConstant d * Real.rpow t (-(d : ℝ) / 2 - 1) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_sub_one ht.ne', mul_div_assoc] using
      ((div_le_div_iff_of_pos_right ht).2 ((gaussian_average d hd).2.1 t ht).2)
  have hfint : IntegrableOn (fun t : ℝ => gaussianAverage d t / t) (Set.Ioi T) volume :=
    hmajor.mono_nonneg hfmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hnonneg t (hT.trans ht)))
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hbound t (hT.trans ht)))
  have hle := integral_mono_ae hfint hmajor
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hbound t (hT.trans ht)))
  rw [integral_const_mul, hpow.2, sub_add_cancel] at hle
  have hscale : gaussianAverageConstant d *
      (-Real.rpow T (-(d : ℝ) / 2) / (-(d : ℝ) / 2)) =
      (2 * gaussianAverageConstant d / (d : ℝ)) * Real.rpow T (-(d : ℝ) / 2) := by ring
  exact ⟨hfint, hle.trans_eq hscale⟩

/- lem:log-energy-truncation -/
theorem part5_log_energy_truncation (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (x : Config d M) (hx : Function.Injective x) (T : ℝ) (hT : 1 ≤ T) : -((M : ℝ) / 2) * (1 + Real.log T) - (gaussianAverageConstant d / (d : ℝ)) * (M : ℝ) ^ 2 * Real.rpow T (-(d : ℝ) / 2) ≤ finiteEnergy 0 x - (M : ℝ) ^ 2 * continuousEnergy d 0 := by
  let F : ℝ → ℝ := fun t =>
    (part5_gaussian_discrepancy x t - (M : ℝ) * (1 - Real.exp (-t))) / t
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hrepr := part5_log_discrepancy_identity d hd M x hx
  have hFint : IntegrableOn F (Set.Ioi 0) volume := hrepr.1
  have hnearint : IntegrableOn F (Set.Ioo 0 T) volume :=
    hFint.mono_set Set.Ioo_subset_Ioi_self
  have hfarint : IntegrableOn F (Set.Ioi T) volume :=
    hFint.mono_set (Set.Ioi_subset_Ioi hTpos.le)
  have hsmall := part5_log_small_integral T hT
  have htail := part5_log_energy_tail d hd T hTpos
  have hnpoint (t : ℝ) (ht : 0 < t) :
      -(M : ℝ) * ((1 - Real.exp (-t)) / t) ≤ F t := by
    simpa only [F, zero_sub, neg_div, mul_div_assoc, neg_mul] using
      ((div_le_div_iff_of_pos_right ht).2
        (sub_le_sub_right (part5_gaussian_positive d hd M x t ht.le).2
          ((M : ℝ) * (1 - Real.exp (-t)))))
  have hfnum (t : ℝ) (ht : 0 < t) :
      -(M : ℝ) ^ 2 * gaussianAverage d t ≤
      part5_gaussian_discrepancy x t - (M : ℝ) * (1 - Real.exp (-t)) := by
    nlinarith only [(part5_gaussian_discrepancy_lower d hd M x t ht.le).1,
      mul_nonneg (Nat.cast_nonneg M) (Real.exp_pos (-t)).le]
  have hfpoint (t : ℝ) (ht : 0 < t) :
      -(M : ℝ) ^ 2 * (gaussianAverage d t / t) ≤ F t := by
    simpa only [F, neg_div, mul_div_assoc, neg_mul] using
      ((div_le_div_iff_of_pos_right ht).2 (hfnum t ht))
  have hnearle := integral_mono_ae (hsmall.1.const_mul (-(M : ℝ))) hnearint
    (ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => hnpoint t ht.1))
  rw [integral_const_mul] at hnearle
  have hnear := (mul_le_mul_of_nonpos_left hsmall.2
    (neg_nonpos.mpr (Nat.cast_nonneg M))).trans hnearle
  have hfarle := integral_mono_ae (htail.1.const_mul (-(M : ℝ) ^ 2)) hfarint
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hfpoint t (hTpos.trans ht)))
  rw [integral_const_mul] at hfarle
  have hfar := (mul_le_mul_of_nonpos_left htail.2
    (neg_nonpos.mpr (sq_nonneg (M : ℝ)))).trans hfarle
  have hsplit : (∫ t in Set.Ioo (0 : ℝ) T, F t) +
      (∫ t in Set.Ioi T, F t) = ∫ t in Set.Ioi (0 : ℝ), F t := by
    simpa only [intervalIntegral.integral_of_le hTpos.le, integral_Ioc_eq_integral_Ioo] using
      (intervalIntegral.integral_interval_add_Ioi hFint hfarint)
  have henergy : finiteEnergy 0 x - (M : ℝ) ^ 2 * continuousEnergy d 0 =
      (1 / 2 : ℝ) * (∫ t in Set.Ioi (0 : ℝ), F t) := hrepr.2
  simp only [div_eq_mul_inv] at hnear hfar henergy ⊢
  nlinarith only [hnear, hfar, hsplit, henergy]

/- lem:log-energy-config -/
theorem part5_log_energy_config (d : ℕ) (hd : 2 ≤ d) (M : ℕ) (x : Config d M) (hx : Function.Injective x) : continuousEnergy d 0 * (M : ℝ) ^ 2 - ((M : ℝ) / (d : ℝ)) * Real.log (M : ℝ) - part5_energy_constants_log d * (M : ℝ) ≤ finiteEnergy 0 x := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [finiteEnergy_zero]
  have hp := part5_energy_cutoff_powers d hd M hM 0
  have hb := part5_log_energy_truncation d hd M x hx
    (Real.rpow (M : ℝ) (2 / (d : ℝ))) hp.1
  rw [hp.2.2.2.2] at hb
  have htail := congrArg (fun y : ℝ => (gaussianAverageConstant d / (d : ℝ)) * y)
    hp.2.2.2.1
  simp only [part5_energy_constants_log, div_eq_mul_inv] at hb htail ⊢
  nlinarith only [hb, htail]

/- lem:energy-infimum-transfer -/
theorem part5_energy_infimum_transfer (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (M : ℕ) (B : ℝ) (hB : ∀ x : Config d M, Function.Injective x → B ≤ finiteEnergy s x) : B ≤ minEnergy d s M := by
  apply (le_csInf_iff (part5_energy_order_interface d hd s M).2.1
    (part5_energy_order_interface d hd s M).1).2
  rintro a ⟨z, rfl⟩
  exact hB z.1 z.2

/- prop:energy-lower -/
theorem part5_energy_lower (d : ℕ) (hd : 2 ≤ d) : (∀ s : ℝ, 0 < s → s < (d : ℝ) → 0 < part5_energy_constants_positive d s ∧ ∀ M : ℕ, (continuousEnergy d s * (M : ℝ) ^ 2 - part5_energy_constants_positive d s * Real.rpow (M : ℝ) (1 + s / (d : ℝ)) ≤ minEnergy d s M) ∧ (∀ x : Config d M, Function.Injective x → continuousEnergy d s * (M : ℝ) ^ 2 - part5_energy_constants_positive d s * Real.rpow (M : ℝ) (1 + s / (d : ℝ)) ≤ finiteEnergy s x)) ∧ (∀ s : ℝ, -2 < s → s < 0 → 0 < part5_energy_constants_negative d s ∧ ∀ M : ℕ, (continuousEnergy d s * (M : ℝ) ^ 2 + part5_energy_constants_negative d s * Real.rpow (M : ℝ) (1 + s / (d : ℝ)) ≤ minEnergy d s M) ∧ (∀ x : Config d M, Function.Injective x → continuousEnergy d s * (M : ℝ) ^ 2 + part5_energy_constants_negative d s * Real.rpow (M : ℝ) (1 + s / (d : ℝ)) ≤ finiteEnergy s x)) ∧ (0 < part5_energy_constants_log d ∧ ∀ M : ℕ, (continuousEnergy d 0 * (M : ℝ) ^ 2 - ((M : ℝ) / (d : ℝ)) * Real.log (M : ℝ) - part5_energy_constants_log d * (M : ℝ) ≤ minEnergy d 0 M) ∧ (∀ x : Config d M, Function.Injective x → continuousEnergy d 0 * (M : ℝ) ^ 2 - ((M : ℝ) / (d : ℝ)) * Real.log (M : ℝ) - part5_energy_constants_log d * (M : ℝ) ≤ finiteEnergy 0 x)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun s hs hsd =>
      ⟨(part5_energy_constant_signs d hd).1 s hs hsd, fun M =>
        ⟨part5_energy_infimum_transfer d hd s M _
          (part5_positive_energy_config d hd s hs hsd M),
          part5_positive_energy_config d hd s hs hsd M⟩⟩
  · exact fun s hs hs0 =>
      ⟨(part5_energy_constant_signs d hd).2.1 s hs hs0, fun M =>
        ⟨part5_energy_infimum_transfer d hd s M _
          (part5_negative_energy_config d hd s hs hs0 M),
          part5_negative_energy_config d hd s hs hs0 M⟩⟩
  · exact ⟨(part5_energy_constant_signs d hd).2.2.1, fun M =>
      ⟨part5_energy_infimum_transfer d hd 0 M _ (part5_log_energy_config d hd M),
        part5_log_energy_config d hd M⟩⟩


end Problem1
