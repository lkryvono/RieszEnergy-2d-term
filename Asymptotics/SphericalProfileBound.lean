import Riesz.Asymptotics.SphericalEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# A prescribed Gaussian scale from the spherical energy bound

The local second-moment estimate only needs the pair profile at scale one.
Integrating its monotonicity over `(1/2, 1]` gives this bound from the existing
nonnegative remainder identity, without selecting a good Gaussian scale.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Geometry
open scoped Topology Classical

namespace Riesz.Asymptotics

/-- The positive weight of the fixed scale interval used in the lower bound. -/
def sphericalProfileWeightMass (s : ℝ) : ℝ :=
  ∫ u in Set.Ioc (1 / 2 : ℝ) 1, u ^ (s / 2 - 1)

/-- The scaled energy of a concrete tuple, in the paper's enlarged-sphere units. -/
def scaledSphericalKernelEnergy (d N : ℕ) (s : ℝ)
    (x : SphereConfiguration d N) : ℝ :=
  (sphericalRadius d N) ^ (-s) / (N : ℝ) *
    (Riesz.Energy.kernelEnergy d s N x - V_K d s * (N : ℝ) ^ 2)

theorem sphericalProfileWeightMass_pos (s : ℝ) : 0 < sphericalProfileWeightMass s := by
  have hcont : ContinuousOn (fun u : ℝ => u ^ (s / 2 - 1)) (Set.Icc (1 / 2) 1) :=
    continuousOn_id.rpow_const (fun u hu =>
      Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hu.1)))
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on
    (hcont.intervalIntegrable_of_Icc (by norm_num))
    (fun u hu => Real.rpow_pos_of_pos
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hu.1) _) (by norm_num)
  simpa only [sphericalProfileWeightMass,
    intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using hpos

/-- Every finite spherical Gaussian pair profile is decreasing in the scale. -/
theorem sphericalGaussianPairProfile_antitone (d N : ℕ) (x : Fin N → Sphere d) :
    Antitone (sphericalGaussianPairProfile d N x) := by
  intro u v huv
  unfold sphericalGaussianPairProfile
  refine mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_)))
    (inv_nonneg.mpr (Nat.cast_nonneg N))
  split_ifs with hij
  case neg =>
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (neg_le_neg (mul_le_mul_of_nonneg_right huv (sq_nonneg _))) (sq_nonneg _))
  exact le_rfl

/-- The fixed-scale profile is bounded by the full nonnegative remainder integral. -/
theorem sphericalGaussianPairProfile_one_le_remainder_integral
    (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N) (s : ℝ) (x : Fin N → Sphere d)
    (hint : IntegrableOn
      (fun u : ℝ => u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x u)
      (Set.Ioi 0) volume) :
    sphericalGaussianPairProfile d N x 1 ≤
      (∫ u in Set.Ioi (0 : ℝ),
        u ^ (s / 2 - 1) * sphericalGaussianRemainder d N x u) /
          sphericalProfileWeightMass s + B d (1 / 2) := by
  have hsub : Set.Ioc (1 / 2 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) :=
    fun u hu => lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hu.1
  have hw : IntegrableOn (fun u : ℝ => u ^ (s / 2 - 1))
      (Set.Ioc (1 / 2 : ℝ) 1) volume :=
    (ContinuousOn.integrableOn_Icc
      (show ContinuousOn (fun u : ℝ => u ^ (s / 2 - 1)) (Set.Icc (1 / 2) 1) from
        continuousOn_id.rpow_const (fun u hu =>
          Or.inl (ne_of_gt (lt_of_lt_of_le
            (by norm_num : (0 : ℝ) < 1 / 2) hu.1))))).mono_set Set.Ioc_subset_Icc_self
  have hbg (u : ℝ) (hu : u ∈ Set.Ioc (1 / 2 : ℝ) 1) :
      sphericalGaussianBackground d N u ≤ B d (1 / 2) :=
    (sphericalGaussianBackground_antitone d N hd hu.1.le).trans
      (sphericalGaussianBackground_le d N hd hN (1 / 2) (by norm_num))
  have hmax (u : ℝ) (hu : u ∈ Set.Ioc (1 / 2 : ℝ) 1) :
      max (sphericalGaussianBackground d N u - 1) 0 ≤ B d (1 / 2) :=
    (max_le (sub_le_self _ zero_le_one) (sphericalGaussianBackground_nonneg d N u)).trans
      (hbg u hu)
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioc (1 / 2 : ℝ) 1) :
      sphericalGaussianPairProfile d N x 1 - B d (1 / 2) ≤
        sphericalGaussianRemainder d N x u :=
    (sub_le_sub_right (sphericalGaussianPairProfile_antitone d N x hu.2) _).trans
      (sub_le_sub_left (hmax u hu) _)
  have hloc := setIntegral_mono_on
    (hw.mul_const (sphericalGaussianPairProfile d N x 1 - B d (1 / 2)))
    (hint.mono_set hsub) measurableSet_Ioc
    (fun u hu => mul_le_mul_of_nonneg_left (hpoint u hu)
      (Real.rpow_nonneg (hsub hu).le _))
  have hfull := setIntegral_mono_set hint
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu =>
      mul_nonneg (Real.rpow_nonneg hu.le _)
        (sphericalGaussianRemainder_nonneg d N hd hN x u hu.le))) hsub.eventuallyLE
  rw [integral_mul_const] at hloc
  exact sub_le_iff_le_add.mp ((le_div_iff₀ (sphericalProfileWeightMass_pos s)).mpr
    (by simpa only [sphericalProfileWeightMass, mul_comm] using hloc.trans hfull))

/-- The actual spherical energy identity gives a prescribed-scale pair bound. -/
theorem eventually_sphericalGaussianPairProfile_one_le_scaledEnergy
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : -2 < s) (hsd : s < (d : ℝ)) (hsne : s ≠ 0) :
    ∀ᶠ N : ℕ in atTop, ∀ x : SphereConfiguration d N,
      sphericalGaussianPairProfile d N x.val 1 ≤
        (scaledSphericalKernelEnergy d N s x - sphericalReferenceConstant d N s) /
          (gamma_s s * sphericalProfileWeightMass s) + B d (1 / 2) := by
  filter_upwards [eventually_spherical_remainder_identity d hd s hs hsd hsne,
    eventually_gt_atTop (0 : ℕ)] with N hidentity hN
  intro x
  refine (sphericalGaussianPairProfile_one_le_remainder_integral
    d N hd hN s x.val (hidentity x).1).trans_eq ?_
  rw [scaledSphericalKernelEnergy, (hidentity x).2, add_sub_cancel_left]
  rw [mul_div_mul_left _ _ (Riesz.Analysis.gamma_s_pos s hs).ne']

/-- Eventual bounded scaled energies uniformly control the pair profile at scale one. -/
theorem eventually_sphericalGaussianPairProfile_one_bounded
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : -2 < s) (hsd : s < (d : ℝ)) (hsne : s ≠ 0)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (henergy : ∃ L : ℝ, ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N n) s (x n) ≤ L) :
    ∃ M : ℝ, ∀ᶠ n : ℕ in atTop,
      sphericalGaussianPairProfile d (N n) (x n).val 1 ≤ M := by
  obtain ⟨L, hL⟩ := henergy
  have href := ((tendsto_sphericalReferenceConstant d hd s hsd hsne).comp hN).eventually
    (lt_mem_nhds (show c0 d s - 1 < c0 d s by linarith))
  refine ⟨(L - c0 d s + 1) / (gamma_s s * sphericalProfileWeightMass s) + B d (1 / 2), ?_⟩
  filter_upwards [hN.eventually
    (eventually_sphericalGaussianPairProfile_one_le_scaledEnergy d hd s hs hsd hsne),
    hL, href] with n hprofile henergy href
  change c0 d s - 1 < sphericalReferenceConstant d (N n) s at href
  have hnum : scaledSphericalKernelEnergy d (N n) s (x n) -
      sphericalReferenceConstant d (N n) s ≤ L - c0 d s + 1 := by linarith
  exact (hprofile (x n)).trans (add_le_add
    (div_le_div_of_nonneg_right hnum
      (mul_pos (Riesz.Analysis.gamma_s_pos s hs) (sphericalProfileWeightMass_pos s)).le)
    (le_rfl : B d (1 / 2) ≤ B d (1 / 2)))

end Riesz.Asymptotics
