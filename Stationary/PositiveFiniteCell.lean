import Riesz.Configuration.PositiveFiniteCellLaws
import Riesz.Stationary.PositiveWindowConvergence
import Riesz.Stationary.NearIndicatorWindow
import Mathlib.Topology.UrysohnsLemma

/-! Positive finite-cell trials from the actual original-law window limit. -/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Negative Riesz.Stationary
open scoped ENNReal Topology CompactlySupported ContDiff

namespace Riesz.Configuration

def positiveCellKernel (d : ℕ) (s : ℝ) (p : Rd d × Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (K_s s ‖p.2 - p.1‖)

def positiveCellBackground (d : ℕ) (s L : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, positiveCellKernel d s p
    ∂(volume.restrict (cube d L)).prod (volume.restrict (cube d L))

theorem measurable_positiveCellKernel (d : ℕ) (s : ℝ) :
    Measurable (positiveCellKernel d s) := by
  exact (((measurable_snd.sub measurable_fst).norm.pow_const (-s)).div_const s).ennreal_ofReal

theorem positive_K_s_zero (s : ℝ) (hs : 0 < s) : K_s s 0 = 0 := by
  simp only [K_s, Real.zero_rpow (neg_ne_zero.mpr hs.ne'), zero_div]

theorem scaled_window_zero_off_cube (d : ℕ) (χ : C_c(Rd d, ℝ))
    (hzero : ∀ x ∉ cube d 1, χ x = 0) (L : ℝ) (hL : 0 < L) :
    ∀ x ∉ cube d L, χ (L⁻¹ • x) = 0 := by
  intro x hx
  apply hzero
  intro hy
  apply hx
  intro i
  have hi : 0 ≤ x i / L ∧ x i / L < 1 := by
    simpa only [PiLp.smul_apply, smul_eq_mul, inv_mul_eq_div] using hy i
  exact ⟨by simpa only [zero_mul] using (le_div_iff₀ hL).mp hi.1,
    by simpa only [one_mul] using (div_lt_iff₀ hL).mp hi.2⟩

theorem positiveCell_weightedKernel_eq (d : ℕ) (s : ℝ) (φ : Rd d → ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (p : Rd d × Rd d) :
    windowWeightedKernel d φ (positiveCellKernel d s) p =
      ENNReal.ofReal (φ p.1 * φ p.2 * K_s s ‖p.2-p.1‖) := by
  simp only [windowWeightedKernel, positiveCellKernel,
    ENNReal.ofReal_mul (mul_nonneg (hφ p.1) (hφ p.2)), ENNReal.ofReal_mul (hφ p.1)]

theorem positiveCell_thin_raw_eq (d : ℕ) (s : ℝ) (P : ConfigurationLaw d)
    (hP : Admissible d P) (χ : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hzero : ∀ x ∉ cube d 1, χ x = 0) (L : ℝ) (hL : 0 < L) :
    (∫⁻ ν, windowPairIntegral d (positiveCellKernel d s) ν
      ∂finiteWindowThinningLaw d P (closure (cube d L)) (fun x => χ (L⁻¹ • x))) =
      ∫⁻ μ, ∫⁻ x, ∫⁻ y, if x=y then 0 else
        ENNReal.ofReal (χ (L⁻¹ • x)*χ (L⁻¹ • y)*K_s s ‖y-x‖) ∂μ ∂μ ∂P := by
  rw [finiteWindowThinningLaw_pair_lintegral d P hP _
    (cube_isBounded d L).isCompact_closure (fun x => χ (L⁻¹ • x))
    (χ.continuous.measurable.comp (measurable_const_smul _))
    (fun x => hχ _) (fun x hx => scaled_window_zero_off_cube d χ hzero L hL x
      (fun h => hx (subset_closure h))) _ (measurable_positiveCellKernel d s)]
  simp only [windowPairIntegral,
    positiveCell_weightedKernel_eq d s (fun x => χ (L⁻¹ • x)) (fun x => (hχ _).1)]

theorem positiveCell_weighted_background_eq (d : ℕ) (s : ℝ) (hs : 0 < s)
    (φ : Rd d → ℝ) (hm : Measurable φ) (hφ : ∀ x, 0 ≤ φ x) :
    (∫⁻ p, positiveCellKernel d s p
      ∂(volume.withDensity (fun x => ENNReal.ofReal (φ x)) : Measure (Rd d)).prod
        (volume.withDensity (fun x => ENNReal.ofReal (φ x)) : Measure (Rd d))) =
      ∫⁻ p : Rd d × Rd d, if p.1=p.2 then 0 else
        ENNReal.ofReal (φ p.1*φ p.2*K_s s ‖p.2-p.1‖)
          ∂(volume : Measure (Rd d)).prod volume := by
  rw [prod_withDensity hm.ennreal_ofReal hm.ennreal_ofReal,
    lintegral_withDensity_eq_lintegral_mul ((volume : Measure (Rd d)).prod volume)
      (show Measurable (fun p : Rd d × Rd d =>
        ENNReal.ofReal (φ p.1) * ENNReal.ofReal (φ p.2)) from
        (hm.ennreal_ofReal.comp measurable_fst).mul
          (hm.ennreal_ofReal.comp measurable_snd)) (measurable_positiveCellKernel d s)]
  refine lintegral_congr (fun p => ?_)
  by_cases hp : p.1 = p.2
  case neg =>
    simpa only [Pi.mul_apply, if_neg hp, windowWeightedKernel] using
      positiveCell_weightedKernel_eq d s φ hφ p
  case pos => simp [positiveCellKernel, hp, positive_K_s_zero s hs]

theorem positiveCellBackground_ne_top
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (L : ℝ) : positiveCellBackground d s L ≠ ⊤ := by
  have hK : IsCompact (closure (cube d L)) := (cube_isBounded d L).isCompact_closure
  obtain ⟨f, hf, _, hc, h01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (by simp)
  let ψ : C_c(Rd d, ℝ) := ⟨f, hc⟩
  let H : Rd d × Rd d → ℝ≥0∞ := fun p => if p.1=p.2 then 0 else
    ENNReal.ofReal (ψ p.1*ψ p.2*K_s s ‖p.2-p.1‖)
  have hH : (∫⁻ p, H p ∂(volume : Measure (Rd d)).prod volume) ≠ ⊤ := by
    simpa only [H, inv_one, one_smul] using
      (originalPositiveFullWindow_raw_ne_top d s hs hsd P hP hW ψ
        (fun x => (h01 x).1) 1 zero_lt_one).2
  have hone : ∀ x ∈ cube d L, ψ x = 1 := fun x hx => hf (subset_closure hx)
  have heq : (∫⁻ p, positiveCellKernel d s p
      ∂((volume : Measure (Rd d)).prod volume).restrict (cube d L ×ˢ cube d L)) =
      ∫⁻ p, H p ∂((volume : Measure (Rd d)).prod volume).restrict
        (cube d L ×ˢ cube d L) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem ((measurableSet_cube d L).prod (measurableSet_cube d L))]
      with p hp
    by_cases hxy : p.1 = p.2
    case neg => simp only [H, if_neg hxy, hone p.1 hp.1, hone p.2 hp.2,
      one_mul, positiveCellKernel]
    case pos => simp [H, positiveCellKernel, hxy, positive_K_s_zero s hs]
  unfold positiveCellBackground
  rw [Measure.prod_restrict, heq]
  exact ne_top_of_le_ne_top hH (lintegral_mono' Measure.restrict_le_self le_rfl)

theorem positiveFilledCell_fixed_L
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hzero : ∀ x ∉ cube d 1, χ x = 0) (L : ℝ) (hL : 0 < L) :
    ∃ Λ : ConfigurationLaw d,
      IsProbabilityMeasure Λ ∧
      (∀ᵐ ζ ∂Λ, IsSimpleConfiguration d ζ ∧
        ζ (cube d L)ᶜ = 0 ∧ ζ Set.univ < ⊤) ∧
      (∀ D, MeasurableSet D → (∫⁻ ζ, ζ D ∂Λ) =
        (volume.restrict (cube d L)) D) ∧
      (∫⁻ ζ, (ζ Set.univ)^(2 : ℕ) ∂Λ) < ⊤ ∧
      (∫⁻ ζ, windowPairIntegral d (positiveCellKernel d s) ζ ∂Λ) ≠ ⊤ ∧
      positiveCellBackground d s L ≠ ⊤ ∧
      Integrable (cellRealEnergy d (positiveCellKernel d s)) Λ ∧
      (L^d)⁻¹ * ((∫ ζ, cellRealEnergy d (positiveCellKernel d s) ζ ∂Λ) -
        (positiveCellBackground d s L).toReal) ≤
          originalPositiveFullCenteredWindow d s P χ L := by
  have hd : 0 < d := by exact_mod_cast (lt_trans hs hsd)
  let φ : Rd d → ℝ := fun x => χ (L⁻¹ • x)
  have hm : Measurable φ := χ.continuous.measurable.comp (measurable_const_smul _)
  have hspec := filledWindowLaw_spec d hd P hP (cube d L) (closure (cube d L))
    (measurableSet_cube d L) subset_closure (cube_isBounded d L).isCompact_closure
    φ hm (fun x => hχ _) (scaled_window_zero_off_cube d χ hzero L hL)
  have hthinRaw := positiveCell_thin_raw_eq d s P hP χ hχ hzero L hL
  have hthin : (∫⁻ μ, windowPairIntegral d (positiveCellKernel d s) μ
      ∂finiteWindowThinningLaw d P (closure (cube d L)) φ) < ⊤ := by
    rw [hthinRaw]
    exact (originalPositiveFullWindow_raw_ne_top d s hs hsd P hP hW χ
      (fun x => (hχ x).1) L hL).1.lt_top
  have hbackground := positiveCellBackground_ne_top d s hs hsd P hP hW L
  have hcost := filledWindowLaw_centered_energy d hd P hP (cube d L) (closure (cube d L))
    (measurableSet_cube d L) subset_closure (cube_isBounded d L).isCompact_closure
    φ hm (fun x => hχ _) (scaled_window_zero_off_cube d χ hzero L hL)
    (positiveCellKernel d s) (measurable_positiveCellKernel d s) hthin hbackground.lt_top
  have hpairT := aemeasurable_windowPairIntegral_of_simple d _
    ((finiteWindowThinningLaw_good d P hP (closure (cube d L))
      (cube_isBounded d L).isCompact_closure φ hm).mono (fun μ hμ => hμ.1))
    (positiveCellKernel d s) (measurable_positiveCellKernel d s)
  have hthinReal : (∫ μ, cellRealEnergy d (positiveCellKernel d s) μ
      ∂finiteWindowThinningLaw d P (closure (cube d L)) φ) =
      (∫⁻ μ, ∫⁻ x, ∫⁻ y, if x=y then 0 else
        ENNReal.ofReal (χ (L⁻¹ • x)*χ (L⁻¹ • y)*K_s s ‖y-x‖) ∂μ ∂μ ∂P).toReal :=
    (integral_toReal hpairT (ae_lt_top' hpairT hthin.ne)).trans
      (congrArg ENNReal.toReal hthinRaw)
  have hcenter := hcost.2.2
  rw [hthinReal, positiveCell_weighted_background_eq d s hs φ hm (fun x => (hχ _).1)] at hcenter
  refine ⟨_, hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2,
    hcost.1, hbackground, hcost.2.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left hcenter
    (inv_nonneg.mpr (pow_pos hL d).le)).trans_eq
      (originalPositiveFullCenteredWindow_eq_physical d s P χ L hL).symm

/-- An actual finite-cube trial law whose normalized centered cost approaches
the energy of the given admissible original law. -/
theorem exists_positiveFilledCell_near_optimal
    (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∃ Λ : ConfigurationLaw d,
      IsProbabilityMeasure Λ ∧
      (∀ᵐ ζ ∂Λ, IsSimpleConfiguration d ζ ∧
        ζ (cube d L)ᶜ = 0 ∧ ζ Set.univ < ⊤) ∧
      (∀ D, MeasurableSet D → (∫⁻ ζ, ζ D ∂Λ) =
        (volume.restrict (cube d L)) D) ∧
      (∫⁻ ζ, (ζ Set.univ)^(2 : ℕ) ∂Λ) < ⊤ ∧
      (∫⁻ ζ, windowPairIntegral d (positiveCellKernel d s) ζ ∂Λ) ≠ ⊤ ∧
      positiveCellBackground d s L ≠ ⊤ ∧
      Integrable (cellRealEnergy d (positiveCellKernel d s)) Λ ∧
      (L^d)⁻¹ * ((∫ ζ, cellRealEnergy d (positiveCellKernel d s) ζ ∂Λ) -
        (positiveCellBackground d s L).toReal) ≤ (W d s P).toReal + ε := by
  let w : ℝ := (W d s P).toReal
  let δ : ℝ := ε / (2*(|w|+1))
  have hδpos : 0 < δ := by positivity
  obtain ⟨χ, hsm, hχ, hts, ha, hnear, hle⟩ :=
    exists_nearIndicator_smooth_cube_window d δ hδpos
  let a : ℝ := ∫ x : Rd d, (χ x)^2
  have hfull : Tendsto (fun n : ℕ =>
      originalPositiveFullCenteredWindow d s P χ ((n : ℝ)+1)) atTop (𝓝 (a*w)) :=
    (compactSmoothWindow_original_full_W_tendsto d s hs hsd P hP hW χ
      (fun x => (hχ x).1) hsm ha).2
  have hδeq : δ*(|w|+1) = ε/2 := by
    dsimp only [δ]
    field_simp [show |w|+1 ≠ 0 by positivity]
  have hnear' : 1-a ≤ δ := by linarith only [hnear]
  have herr : (1-a)*|w| < ε/2 :=
    (mul_le_mul_of_nonneg_right hnear' (abs_nonneg w)).trans_lt
      ((mul_lt_mul_of_pos_left (lt_add_one _) hδpos).trans_eq hδeq)
  have hprod : (a-1)*w ≤ (1-a)*|w| := by
    nlinarith only [mul_le_mul_of_nonneg_left (neg_le_abs w)
      (sub_nonneg.mpr (show a ≤ 1 from hle))]
  have haw : a*w < w+ε/2 := by nlinarith only [hprod, herr]
  have hev : ∀ᶠ n : ℕ in atTop,
      originalPositiveFullCenteredWindow d s P χ ((n : ℝ)+1) < w+ε :=
    (tendsto_order.mp hfull).2 _ (by linarith only [haw, hε])
  obtain ⟨n, hn⟩ := hev.exists
  have hL : 0 < (n : ℝ)+1 := by positivity
  have hzero : ∀ x ∉ cube d 1, χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hxt => hx (hts hxt))
  obtain ⟨Λ, hΛprob, hΛgood, hΛmean, hΛmoment, hΛenergy, hΛbackground,
    hΛintegrable, hΛcost⟩ := positiveFilledCell_fixed_L
      d s hs hsd P hP hW χ hχ hzero ((n : ℝ)+1) hL
  exact ⟨_, hL, Λ, hΛprob, hΛgood, hΛmean, hΛmoment, hΛenergy,
    hΛbackground, hΛintegrable, hΛcost.trans (le_of_lt hn)⟩

end Riesz.Configuration
