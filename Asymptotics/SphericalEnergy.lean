import Riesz.Asymptotics.SphericalReference
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The spherical Gaussian energy identity

The integral formulas retained from Problem 1 are transported to the exact
Showcase normalization. Only distinct spherical tuples are needed for the
near-minimizer route to the main theorem.
-/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Geometry
open scoped Topology ENNReal

namespace Riesz.Asymptotics

theorem problem1GammaCoefficient_eq (s : ℝ) (hs : s ≠ 0) :
    Problem1.part5_riesz_gamma_coefficient s = gamma_s s := by
  unfold Problem1.part5_riesz_gamma_coefficient gamma_s
  rw [show 1 + s / 2 = s / 2 + 1 by ring,
    Real.Gamma_add_one (div_ne_zero hs (by norm_num))]
  congr 1; ring

/-- The negative-exponent discrepancy formula with the exact Showcase energy. -/
theorem negative_spherical_discrepancy_identity (d N : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : -2 < s) (hs0 : s < 0) (hsd : s < (d : ℝ))
    (x : SphereConfiguration d N) :
    IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1) *
      Problem1.part5_gaussian_discrepancy (fun i => problem1SphereEquiv d (x.val i)) t)
      (Set.Ioi 0) volume ∧
    Riesz.Energy.kernelEnergy d s N x - V_K d s * (N : ℝ) ^ 2 =
      gamma_s s * ∫ t in Set.Ioi (0 : ℝ), t ^ (s / 2 - 1) *
        Problem1.part5_gaussian_discrepancy (fun i => problem1SphereEquiv d (x.val i)) t := by
  have hbase := Problem1.part5_negative_discrepancy_identity d hd s hs hs0 N
    (fun i => problem1SphereEquiv d (x.val i))
    ((problem1SphereEquiv d).injective.comp x.property)
  simpa only [problem1FiniteEnergy_eq d N s hs0.ne,
    problem1ContinuousEnergy_eq d hd s hsd hs0.ne,
    problem1GammaCoefficient_eq s hs0.ne, Real.rpow_eq_pow, mul_comm] using hbase

/-- Weighted scale substitution on the positive half-line. -/
theorem weighted_integral_comp_mul (f : ℝ → ℝ) (p a : ℝ) (ha : 0 < a) :
    (∫ u in Set.Ioi (0 : ℝ), u ^ p * f (u * a)) =
      a⁻¹ ^ (p + 1) * ∫ t in Set.Ioi (0 : ℝ), t ^ p * f t := by
  have hchange : (∫ u in Set.Ioi (0 : ℝ), u ^ p * f (u * a)) =
      a⁻¹ * ∫ t in Set.Ioi (0 : ℝ), (a⁻¹ * t) ^ p * f t := by
    simpa only [inv_mul_cancel_left₀ ha.ne', mul_zero, smul_eq_mul, mul_comm] using
      integral_comp_mul_left_Ioi (fun t : ℝ => (a⁻¹ * t) ^ p * f t) 0 ha
  have hfactor : (∫ t in Set.Ioi (0 : ℝ), (a⁻¹ * t) ^ p * f t) =
      a⁻¹ ^ p * ∫ t in Set.Ioi (0 : ℝ), t ^ p * f t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [Real.mul_rpow (inv_pos.mpr ha).le ht.le, mul_assoc]
  rw [hchange, hfactor, ← mul_assoc, mul_comm a⁻¹ (a⁻¹ ^ p),
    ← Real.rpow_add_one (inv_pos.mpr ha).ne']

theorem weighted_integral_comp_radius (f : ℝ → ℝ) (s R : ℝ) (hR : 0 < R) :
    (∫ u in Set.Ioi (0 : ℝ), u ^ (s / 2 - 1) * f (u * R ^ 2)) =
      R ^ (-s) * ∫ t in Set.Ioi (0 : ℝ), t ^ (s / 2 - 1) * f t := by
  rw [weighted_integral_comp_mul f (s / 2 - 1) (R ^ 2) (sq_pos_of_pos hR)]
  rw [sub_add_cancel, Real.inv_rpow (sq_nonneg R), ← Real.rpow_neg (sq_nonneg R),
    ← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * -(s / 2) = -s by ring]

theorem weighted_integrableOn_comp_mul (f : ℝ → ℝ) (p a : ℝ) (ha : 0 < a)
    (h : IntegrableOn (fun t => t ^ p * f t) (Set.Ioi 0) volume) :
    IntegrableOn (fun u => u ^ p * f (u * a)) (Set.Ioi 0) volume := by
  have hscaled : IntegrableOn (fun t => (a⁻¹ * t) ^ p * f t) (Set.Ioi 0) volume := by
    apply (h.const_mul (a⁻¹ ^ p)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Real.mul_rpow (inv_pos.mpr ha).le ht.le, mul_assoc]
  simpa only [inv_mul_cancel_left₀ ha.ne', mul_zero, mul_comm] using
    (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => (a⁻¹ * t) ^ p * f t) 0 ha).mpr
      (by simpa only [mul_zero] using hscaled)

/-- Restoring equal-index pairs gives the normalized negative Gaussian profile. -/
theorem sphericalGaussianDiscrepancy_eq (d N : ℕ) (hN : 0 < N)
    (x : Fin N → Sphere d) (u : ℝ) :
    (N : ℝ)⁻¹ * Problem1.part5_gaussian_discrepancy
      (fun i => problem1SphereEquiv d (x i)) (u * (sphericalRadius d N) ^ 2) =
      sphericalGaussianPairProfile d N x u + 1 - sphericalGaussianBackground d N u := by
  have hterm (i j : Fin N) :
      Real.exp (-(u * (sphericalRadius d N) ^ 2) * (chord d (x i) (x j)) ^ 2) =
        (if i = j then 1 else 0) +
        (if i = j then 0 else
          Real.exp (-(u * (sphericalRadius d N) ^ 2) * (chord d (x i) (x j)) ^ 2)) := by
    by_cases hij : i = j <;> simp [hij, chord]
  have hsum : (∑ i : Fin N, ∑ j : Fin N,
      Real.exp (-(u * (sphericalRadius d N) ^ 2) * (chord d (x i) (x j)) ^ 2)) =
      ∑ i : Fin N, ∑ j : Fin N,
        ((if i = j then 1 else 0) +
          (if i = j then 0 else
            Real.exp (-(u * (sphericalRadius d N) ^ 2) * (chord d (x i) (x j)) ^ 2))) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  simp only [Problem1.part5_gaussian_discrepancy, problem1SphereEquiv_dist,
    sphericalGaussianPairProfile, sphericalGaussianBackground, hsum]
  field_simp [(Nat.cast_pos.mpr hN : (0 : ℝ) < N).ne']
  ring

/-- The enlarged-sphere negative energy before separating its reference term. -/
theorem negative_spherical_scaled_identity (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (s : ℝ) (hs : -2 < s) (hs0 : s < 0) (hsd : s < (d : ℝ))
    (x : SphereConfiguration d N) :
    IntegrableOn (fun u : ℝ => u ^ (s / 2 - 1) *
      (sphericalGaussianPairProfile d N x.val u + 1 - sphericalGaussianBackground d N u))
      (Set.Ioi 0) volume ∧
    (sphericalRadius d N) ^ (-s) / (N : ℝ) *
      (Riesz.Energy.kernelEnergy d s N x - V_K d s * (N : ℝ) ^ 2) =
      gamma_s s * ∫ u in Set.Ioi (0 : ℝ), u ^ (s / 2 - 1) *
        (sphericalGaussianPairProfile d N x.val u + 1 - sphericalGaussianBackground d N u) := by
  have hbase := negative_spherical_discrepancy_identity d N hd s hs hs0 hsd x
  have hscaled := weighted_integrableOn_comp_mul
    (fun t => Problem1.part5_gaussian_discrepancy (fun i => problem1SphereEquiv d (x.val i)) t)
    (s / 2 - 1) ((sphericalRadius d N) ^ 2)
    (sq_pos_of_pos (sphericalRadius_pos d N hN)) hbase.1
  constructor
  · simpa only [IntegrableOn, ← sphericalGaussianDiscrepancy_eq d N hN x.val, mul_left_comm] using
      hscaled.const_mul (N : ℝ)⁻¹
  · rw [hbase.2]
    simp_rw [← sphericalGaussianDiscrepancy_eq d N hN x.val,
      mul_left_comm _ (N : ℝ)⁻¹]
    rw [integral_const_mul, weighted_integral_comp_radius _ s _ (sphericalRadius_pos d N hN)]
    ring

theorem weightedSphericalNegativeReference_integrable (d N : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : s < 0)
    (hcut : 1 ≤ sphericalGaussianBackground d N (Real.pi / 2)) :
    IntegrableOn (weightedSphericalNegativeReference d N s) (Set.Ioi 0) volume := by
  have hdom : IntegrableOn
      ((Set.Ioi (Real.pi / 2)).indicator (fun u : ℝ => u ^ (s / 2 - 1)))
      (Set.Ioi 0) volume :=
    ((integrableOn_Ioi_rpow_of_lt (by linarith : s / 2 - 1 < -1)
      (div_pos Real.pi_pos (by norm_num))).integrable_indicator measurableSet_Ioi).mono_measure
        Measure.restrict_le_self
  refine hdom.mono' (((measurable_id.pow_const _).mul
    ((measurable_const.sub (measurable_sphericalGaussianBackground d N hd)).max
      measurable_const)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [weightedSphericalNegativeReference, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.le _) (le_max_right _ _))]
  by_cases hlarge : Real.pi / 2 < u
  case neg =>
    have hbg : 1 ≤ sphericalGaussianBackground d N u :=
      hcut.trans (sphericalGaussianBackground_antitone d N hd (le_of_not_gt hlarge))
    simp [Set.indicator_of_notMem (show u ∉ Set.Ioi (Real.pi / 2) from hlarge),
      max_eq_right (sub_nonpos.mpr hbg)]
  case pos =>
    simpa only [Set.indicator_of_mem (show u ∈ Set.Ioi (Real.pi / 2) from hlarge), mul_one] using
      mul_le_mul_of_nonneg_left
        (max_le (sub_le_self 1 (sphericalGaussianBackground_nonneg d N u)) zero_le_one)
        (Real.rpow_nonneg hu.le (s / 2 - 1))

theorem negative_spherical_profile_decomposition (d N : ℕ) (s : ℝ)
    (x : Fin N → Sphere d) (u : ℝ) :
    u ^ (s / 2 - 1) *
        (sphericalGaussianPairProfile d N x u + 1 - sphericalGaussianBackground d N u) =
      u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x u +
        weightedSphericalNegativeReference d N s u := by
  unfold sphericalGaussianRemainder weightedSphericalNegativeReference
  by_cases hbg : 1 ≤ sphericalGaussianBackground d N u
  · rw [max_eq_left (sub_nonneg.mpr hbg), max_eq_right (sub_nonpos.mpr hbg)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hbg)),
      max_eq_left (sub_nonneg.mpr (le_of_not_ge hbg))]
    ring

/-- The full negative-exponent remainder identity whenever the reference cutoff holds. -/
theorem negative_spherical_remainder_identity (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (s : ℝ) (hs : -2 < s) (hs0 : s < 0) (hsd : s < (d : ℝ))
    (hcut : 1 ≤ sphericalGaussianBackground d N (Real.pi / 2))
    (x : SphereConfiguration d N) :
    IntegrableOn (fun u : ℝ => u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u)
      (Set.Ioi 0) volume ∧
    (sphericalRadius d N) ^ (-s) / (N : ℝ) *
      (Riesz.Energy.kernelEnergy d s N x - V_K d s * (N : ℝ) ^ 2) =
      sphericalReferenceConstant d N s +
        gamma_s s * ∫ u in Set.Ioi (0 : ℝ),
          u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u := by
  have hbase := negative_spherical_scaled_identity d N hd hN s hs hs0 hsd x
  have href := weightedSphericalNegativeReference_integrable d N hd s hs0 hcut
  have hrem : IntegrableOn
      (fun u : ℝ => u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u)
      (Set.Ioi 0) volume := by
    apply (hbase.1.sub href).congr
    exact Filter.Eventually.of_forall (fun u =>
      sub_eq_of_eq_add (negative_spherical_profile_decomposition d N s x.val u))
  refine ⟨hrem, ?_⟩
  simp_rw [hbase.2, negative_spherical_profile_decomposition]
  rw [integral_add hrem href, sphericalReferenceConstant, if_neg (not_lt_of_ge hs0.le)]
  ring

/-- The negative remainder identity holds for every distinct tuple at all
sufficiently large point counts, with no additional cutoff assumption. -/
theorem eventually_negative_spherical_remainder_identity (d : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : -2 < s) (hs0 : s < 0) (hsd : s < (d : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ x : SphereConfiguration d N,
      IntegrableOn (fun u : ℝ => u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u)
        (Set.Ioi 0) volume ∧
      (sphericalRadius d N) ^ (-s) / (N : ℝ) *
        (Riesz.Energy.kernelEnergy d s N x - V_K d s * (N : ℝ) ^ 2) =
        sphericalReferenceConstant d N s +
          gamma_s s * ∫ u in Set.Ioi (0 : ℝ),
            u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ),
    (tendsto_sphericalGaussianBackground d hd (Real.pi / 2)
      (div_pos Real.pi_pos (by norm_num))).eventually
        (lt_mem_nhds (one_lt_B_half_pi d hd))] with N hN hcut
  exact fun x => negative_spherical_remainder_identity d N hd hN s hs hs0 hsd hcut.le x

/-- The positive discrepancy subtracts the restored equal-index contribution
before integration, so no divergent constant term is separated. -/
theorem problem1_positive_discrepancy_identity (d N : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (x : Problem1.Config d N) (hx : Function.Injective x) :
    IntegrableOn (fun t : ℝ =>
      (Problem1.part5_gaussian_discrepancy x t - (N : ℝ)) * t ^ (s / 2 - 1))
      (Set.Ioi 0) volume ∧
    Problem1.finiteEnergy s x - (N : ℝ) ^ 2 * Problem1.continuousEnergy d s =
      Problem1.part5_riesz_gamma_coefficient s * ∫ t in Set.Ioi (0 : ℝ),
        (Problem1.part5_gaussian_discrepancy x t - (N : ℝ)) * t ^ (s / 2 - 1) := by
  let F : Fin N → Fin N → ℝ → ℝ := fun i j t =>
    if i = j then 0 else Real.exp (-t * dist (x i) (x j) ^ 2) * t ^ (s / 2 - 1)
  have hFint (i j : Fin N) : IntegrableOn (F i j) (Set.Ioi 0) volume := by
    by_cases hij : i = j
    · simp [F, hij]
    · simpa only [F, if_neg hij, Real.rpow_eq_pow] using
        (Problem1.part5_positive_pointwise s (dist (x i) (x j)) hs
          (dist_pos.mpr (hx.ne hij))).1
  have hFvalue (i j : Fin N) : (if i = j then 0 else Problem1.kernel d s (x i) (x j)) =
      Problem1.part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), F i j t) := by
    by_cases hij : i = j
    · simp [hij, F]
    · simpa only [F, if_neg hij, Problem1.kernel_ne_zero_offDiag hs.ne' (hx.ne hij),
        Real.rpow_eq_pow] using
        (Problem1.part5_positive_pointwise s (dist (x i) (x j)) hs
          (dist_pos.mpr (hx.ne hij))).2
  have hrow (i : Fin N) : IntegrableOn (fun t => ∑ j : Fin N, F i j t) (Set.Ioi 0) volume :=
    integrable_finsetSum Finset.univ (fun j _ => hFint i j)
  have hsum : IntegrableOn (fun t => ∑ i : Fin N, ∑ j : Fin N, F i j t)
      (Set.Ioi 0) volume := integrable_finsetSum Finset.univ (fun i _ => hrow i)
  have hFexpand (i j : Fin N) (t : ℝ) : F i j t =
      (Real.exp (-t * dist (x i) (x j) ^ 2) - if i = j then 1 else 0) *
        t ^ (s / 2 - 1) := by
    by_cases hij : i = j
    all_goals simp [F, hij]
  have hdecomp (t : ℝ) :
      (Problem1.part5_gaussian_discrepancy x t - (N : ℝ)) * t ^ (s / 2 - 1) =
        (∑ i : Fin N, ∑ j : Fin N, F i j t) -
          (N : ℝ) ^ 2 * (Problem1.gaussianAverage d t * t ^ (s / 2 - 1)) := by
    simp only [Problem1.part5_gaussian_discrepancy, hFexpand, ← Finset.sum_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hJ : IntegrableOn (fun t : ℝ => Problem1.gaussianAverage d t * t ^ (s / 2 - 1))
      (Set.Ioi 0) volume := by
    simpa only [Real.rpow_eq_pow] using Problem1.part5_positive_J_integrable d hd s hs hsd
  simp_rw [hdecomp]
  refine ⟨hsum.sub (hJ.const_mul ((N : ℝ) ^ (2 : ℕ))), ?_⟩
  rw [integral_sub hsum (hJ.const_mul ((N : ℝ) ^ (2 : ℕ))), integral_const_mul]
  have hrowvalue (i : Fin N) : (∫ t in Set.Ioi (0 : ℝ), ∑ j : Fin N, F i j t) =
      ∑ j : Fin N, ∫ t in Set.Ioi (0 : ℝ), F i j t :=
    integral_finsetSum Finset.univ (fun j _ => hFint i j)
  have henergy : Problem1.finiteEnergy s x = ∑ i : Fin N, ∑ j : Fin N,
      Problem1.part5_riesz_gamma_coefficient s * (∫ t in Set.Ioi (0 : ℝ), F i j t) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hij : i = j
    all_goals simpa [hij] using hFvalue i j
  have hcont : Problem1.continuousEnergy d s = Problem1.part5_riesz_gamma_coefficient s *
      ∫ t in Set.Ioi (0 : ℝ), Problem1.gaussianAverage d t * t ^ (s / 2 - 1) := by
    simpa only [Real.rpow_eq_pow] using Problem1.part5_positive_continuum d hd s hs hsd
  simp only [henergy, integral_finsetSum Finset.univ (fun i _ => hrow i), hrowvalue,
    hcont, ← Finset.mul_sum]
  ring

/-- The positive-exponent formula in the exact Showcase normalization. -/
theorem positive_spherical_discrepancy_identity (d N : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (x : SphereConfiguration d N) :
    IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1) *
      (Problem1.part5_gaussian_discrepancy (fun i => problem1SphereEquiv d (x.val i)) t -
        (N : ℝ))) (Set.Ioi 0) volume ∧
    Riesz.Energy.kernelEnergy d s N x - V_K d s * (N : ℝ) ^ 2 =
      gamma_s s * ∫ t in Set.Ioi (0 : ℝ), t ^ (s / 2 - 1) *
        (Problem1.part5_gaussian_discrepancy (fun i => problem1SphereEquiv d (x.val i)) t -
          (N : ℝ)) := by
  have hbase := problem1_positive_discrepancy_identity d N hd s hs hsd
    (fun i => problem1SphereEquiv d (x.val i))
    ((problem1SphereEquiv d).injective.comp x.property)
  simpa only [problem1FiniteEnergy_eq d N s hs.ne',
    problem1ContinuousEnergy_eq d hd s hsd hs.ne', problem1GammaCoefficient_eq s hs.ne',
    mul_comm] using hbase

/-- The positive energy on the enlarged sphere before separating its reference. -/
theorem positive_spherical_scaled_identity (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (x : SphereConfiguration d N) :
    IntegrableOn (fun u : ℝ => u ^ (s / 2 - 1) *
      (sphericalGaussianPairProfile d N x.val u - sphericalGaussianBackground d N u))
      (Set.Ioi 0) volume ∧
    (sphericalRadius d N) ^ (-s) / (N : ℝ) *
      (Riesz.Energy.kernelEnergy d s N x - V_K d s * (N : ℝ) ^ 2) =
      gamma_s s * ∫ u in Set.Ioi (0 : ℝ), u ^ (s / 2 - 1) *
        (sphericalGaussianPairProfile d N x.val u - sphericalGaussianBackground d N u) := by
  have hbase := positive_spherical_discrepancy_identity d N hd s hs hsd x
  have hprofile (u : ℝ) : (N : ℝ)⁻¹ *
      (Problem1.part5_gaussian_discrepancy (fun i => problem1SphereEquiv d (x.val i))
        (u * (sphericalRadius d N) ^ 2) - (N : ℝ)) =
      sphericalGaussianPairProfile d N x.val u - sphericalGaussianBackground d N u := by
    rw [mul_sub, sphericalGaussianDiscrepancy_eq d N hN x.val,
      inv_mul_cancel₀ (Nat.cast_pos.mpr hN : (0 : ℝ) < N).ne']
    ring
  have hscaled := weighted_integrableOn_comp_mul
    (fun t => Problem1.part5_gaussian_discrepancy (fun i => problem1SphereEquiv d (x.val i)) t -
      (N : ℝ)) (s / 2 - 1) ((sphericalRadius d N) ^ 2)
    (sq_pos_of_pos (sphericalRadius_pos d N hN)) hbase.1
  constructor
  · simpa only [IntegrableOn, ← hprofile, mul_left_comm] using hscaled.const_mul (N : ℝ)⁻¹
  · rw [hbase.2]
    simp_rw [← hprofile, mul_left_comm _ (N : ℝ)⁻¹]
    rw [integral_const_mul, weighted_integral_comp_radius
      (fun t => Problem1.part5_gaussian_discrepancy (fun i => problem1SphereEquiv d (x.val i)) t -
        (N : ℝ)) s _ (sphericalRadius_pos d N hN)]
    ring

theorem weightedSphericalPositiveReference_integrable (d N : ℕ) (hd : 2 ≤ d)
    (hN : 0 < N) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) :
    IntegrableOn (weightedSphericalPositiveReference d N s) (Set.Ioi 0) volume := by
  refine (Riesz.Stationary.weightedPositiveReference_integrable d s hs hsd).mono'
    (((measurable_id.pow_const _).mul
      (measurable_const.min (measurable_sphericalGaussianBackground d N hd))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa only [weightedSphericalPositiveReference, Riesz.Stationary.weightedPositiveReference,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.le _)
      (le_min zero_le_one (sphericalGaussianBackground_nonneg d N u)))] using
    mul_le_mul_of_nonneg_left (min_le_min_left 1 (sphericalGaussianBackground_le d N hd hN u hu))
      (Real.rpow_nonneg hu.le (s / 2 - 1))

theorem positive_spherical_profile_decomposition (d N : ℕ) (s : ℝ)
    (x : Fin N → Sphere d) (u : ℝ) :
    u ^ (s / 2 - 1) *
        (sphericalGaussianPairProfile d N x u - sphericalGaussianBackground d N u) =
      u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x u -
        weightedSphericalPositiveReference d N s u := by
  unfold sphericalGaussianRemainder weightedSphericalPositiveReference
  by_cases hbg : 1 ≤ sphericalGaussianBackground d N u
  · rw [max_eq_left (sub_nonneg.mpr hbg), min_eq_left hbg]
    ring
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hbg)), min_eq_right (le_of_not_ge hbg)]
    ring

/-- The full positive-exponent spherical remainder identity. -/
theorem positive_spherical_remainder_identity (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (x : SphereConfiguration d N) :
    IntegrableOn (fun u : ℝ => u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u)
      (Set.Ioi 0) volume ∧
    (sphericalRadius d N) ^ (-s) / (N : ℝ) *
      (Riesz.Energy.kernelEnergy d s N x - V_K d s * (N : ℝ) ^ 2) =
      sphericalReferenceConstant d N s + gamma_s s * ∫ u in Set.Ioi (0 : ℝ),
        u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u := by
  have hbase := positive_spherical_scaled_identity d N hd hN s hs hsd x
  have href := weightedSphericalPositiveReference_integrable d N hd hN s hs hsd
  have hrem : IntegrableOn
      (fun u : ℝ => u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u)
      (Set.Ioi 0) volume := by
    apply (hbase.1.add href).congr
    exact Filter.Eventually.of_forall (fun u =>
      eq_sub_iff_add_eq.mp (positive_spherical_profile_decomposition d N s x.val u))
  refine ⟨hrem, ?_⟩
  simp_rw [hbase.2, positive_spherical_profile_decomposition]
  rw [integral_sub hrem href, sphericalReferenceConstant, if_pos hs]
  ring

/-- Both exponent branches of the exact spherical remainder formula. -/
theorem eventually_spherical_remainder_identity (d : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : -2 < s) (hsd : s < (d : ℝ)) (hsne : s ≠ 0) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ x : SphereConfiguration d N,
      IntegrableOn (fun u : ℝ => u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u)
        (Set.Ioi 0) volume ∧
      (sphericalRadius d N) ^ (-s) / (N : ℝ) *
        (Riesz.Energy.kernelEnergy d s N x - V_K d s * (N : ℝ) ^ 2) =
        sphericalReferenceConstant d N s + gamma_s s * ∫ u in Set.Ioi (0 : ℝ),
          u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u := by
  rcases lt_or_gt_of_ne hsne with hsneg | hspos
  · exact eventually_negative_spherical_remainder_identity d hd s hs hsneg hsd
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with N hN
    exact fun x => positive_spherical_remainder_identity d N hd hN s hspos hsd x

/-- The nonnegative extended-integral representation used by Fatou's lemma.
The formula retains the extended integral until its finiteness is established. -/
theorem eventually_spherical_remainder_lintegral_identity (d : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : -2 < s) (hsd : s < (d : ℝ)) (hsne : s ≠ 0) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ x : SphereConfiguration d N,
      (((sphericalRadius d N) ^ (-s) / (N : ℝ) *
        (Riesz.Energy.kernelEnergy d s N x - V_K d s * (N : ℝ) ^ 2) : ℝ) : EReal) =
        (sphericalReferenceConstant d N s : EReal) +
          ((ENNReal.ofReal (gamma_s s) * ∫⁻ u in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (u ^ (s / 2 - 1)) *
              ENNReal.ofReal (sphericalGaussianRemainder d N x.val u) : ℝ≥0∞) : EReal) := by
  filter_upwards [eventually_spherical_remainder_identity d hd s hs hsd hsne,
    Filter.eventually_gt_atTop (0 : ℕ)] with N hidentity hN
  intro x
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun u => u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u) :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu =>
      mul_nonneg (Real.rpow_nonneg hu.le _) (sphericalGaussianRemainder_nonneg d N hd hN x.val u hu.le))
  have hlintegral : (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) *
      ENNReal.ofReal (sphericalGaussianRemainder d N x.val u)) =
      ENNReal.ofReal (∫ u in Set.Ioi (0 : ℝ),
        u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x.val u) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hidentity x).1 hnonneg]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _)).symm
  rw [(hidentity x).2, hlintegral, ← ENNReal.ofReal_mul (Riesz.Analysis.gamma_s_pos s hs).le,
    EReal.coe_ennreal_ofReal,
    max_eq_left (mul_nonneg (Riesz.Analysis.gamma_s_pos s hs).le (integral_nonneg_of_ae hnonneg)),
    EReal.coe_add]

end Riesz.Asymptotics
