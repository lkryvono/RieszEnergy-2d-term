import Riesz.Asymptotics.SphericalSharpLower
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Stationary

/-- Nonnegative correlation of a measurable Euclidean window. -/
def nonnegativeWindowOverlap (d : ℕ) (c : Rd d → ℝ≥0∞) (z : Rd d) : ℝ≥0∞ :=
  ∫⁻ t, c t * c (t + z) ∂volume

theorem measurable_nonnegativeWindowOverlap
    (d : ℕ) (c : Rd d → ℝ≥0∞) (hc : Measurable c) :
    Measurable (nonnegativeWindowOverlap d c) := by
  exact ((hc.comp measurable_snd).mul
    (hc.comp (measurable_snd.add measurable_fst))).lintegral_prod_right'

/-- Exact stationary window identity, including possibly infinite integrals. -/
theorem lintegral_stationaryPair_window_eq_cube_overlap
    (d : ℕ) (Γ : Measure (Rd d × Rd d)) [SFinite Γ]
    (hΓ : ∀ a : Rd d,
      Γ.map (fun p : Rd d × Rd d => (a + p.1, a + p.2)) = Γ)
    (c g : Rd d → ℝ≥0∞) (hc : Measurable c) (hg : Measurable g) :
    (∫⁻ p, c p.1 * c p.2 * g (p.2 - p.1) ∂Γ) =
      ∫⁻ p, (cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
        nonnegativeWindowOverlap d c (p.2 - p.1) * g (p.2 - p.1) ∂Γ := by
  let b : Rd d → ℝ≥0∞ := (cube d 1).indicator (fun _ => 1)
  have hK : MeasurableSet (cube d 1) := Riesz.Negative.measurableSet_cube d 1
  have hb : Measurable b := measurable_const.indicator hK
  have hbvolume : (∫⁻ x, b x ∂volume) = 1 :=
    (lintegral_indicator_one hK).trans ((Riesz.Negative.volume_cube d 1).trans
      ((congrArg (fun a : ℝ≥0∞ => a ^ d) ENNReal.ofReal_one).trans (one_pow d)))
  have hshift (a : Rd d) :
      (∫⁻ p, b (a + p.1) * c p.1 * c p.2 * g (p.2 - p.1) ∂Γ) =
        ∫⁻ p, b p.1 * c (p.1 - a) * c (p.2 - a) * g (p.2 - p.1) ∂Γ := by
    let T : Rd d × Rd d → Rd d × Rd d := fun p => (a + p.1, a + p.2)
    let F : Rd d × Rd d → ℝ≥0∞ :=
      fun p => b p.1 * c (p.1 - a) * c (p.2 - a) * g (p.2 - p.1)
    have hT : Measurable T :=
      (measurable_const.add measurable_fst).prodMk
        (measurable_const.add measurable_snd)
    have hF : Measurable F :=
      (((hb.comp measurable_fst).mul
        (hc.comp (measurable_fst.sub measurable_const))).mul
        (hc.comp (measurable_snd.sub measurable_const))).mul
        (hg.comp (measurable_snd.sub measurable_fst))
    calc
      (∫⁻ p, b (a + p.1) * c p.1 * c p.2 * g (p.2 - p.1) ∂Γ) =
          ∫⁻ p, F (T p) ∂Γ := by
        simp only [F, T, add_sub_cancel_left, add_sub_add_left_eq_sub]
      _ = ∫⁻ p, F p ∂Γ.map T := (lintegral_map hF hT).symm
      _ = ∫⁻ p, F p ∂Γ := congrArg (fun M => ∫⁻ p, F p ∂M) (hΓ a)
      _ = _ := rfl
  have hkernel₁ : Measurable
      (fun q : Rd d × (Rd d × Rd d) =>
        b (q.1 + q.2.1) * c q.2.1 * c q.2.2 * g (q.2.2 - q.2.1)) :=
    (((hb.comp (measurable_fst.add (measurable_fst.comp measurable_snd))).mul
      (hc.comp (measurable_fst.comp measurable_snd))).mul
      (hc.comp (measurable_snd.comp measurable_snd))).mul
      (hg.comp ((measurable_snd.comp measurable_snd).sub
        (measurable_fst.comp measurable_snd)))
  have hkernel₂ : Measurable
      (fun q : Rd d × (Rd d × Rd d) =>
        b q.2.1 * c (q.2.1 - q.1) * c (q.2.2 - q.1) *
          g (q.2.2 - q.2.1)) :=
    (((hb.comp (measurable_fst.comp measurable_snd)).mul
      (hc.comp ((measurable_fst.comp measurable_snd).sub measurable_fst))).mul
      (hc.comp ((measurable_snd.comp measurable_snd).sub measurable_fst))).mul
      (hg.comp ((measurable_snd.comp measurable_snd).sub
        (measurable_fst.comp measurable_snd)))
  have hinner₁ (p : Rd d × Rd d) :
      (∫⁻ a, b (a + p.1) * c p.1 * c p.2 * g (p.2 - p.1) ∂volume) =
        c p.1 * c p.2 * g (p.2 - p.1) := by
    simpa only [mul_assoc, lintegral_add_right_eq_self, hbvolume, one_mul] using
      (lintegral_mul_const (μ := volume) (f := fun a : Rd d => b (a + p.1))
        (c p.1 * c p.2 * g (p.2 - p.1))
        (hb.comp (measurable_id.add measurable_const)))
  have htwist (p : Rd d × Rd d) :
      (∫⁻ a, c (p.1 - a) * c (p.2 - a) ∂volume) =
        nonnegativeWindowOverlap d c (p.2 - p.1) := by
    have hcancel (a : Rd d) : (p.1 - a) + (p.2 - p.1) = p.2 - a := by
      abel
    calc
      (∫⁻ a, c (p.1 - a) * c (p.2 - a) ∂volume) =
          ∫⁻ a, c (p.1 - a) * c ((p.1 - a) + (p.2 - p.1)) ∂volume := by
        simp only [hcancel]
      _ = _ := lintegral_sub_left_eq_self
        (μ := (volume : Measure (Rd d)))
        (fun t : Rd d => c t * c (t + (p.2 - p.1))) p.1
  have hinner₂ (p : Rd d × Rd d) :
      (∫⁻ a, b p.1 * c (p.1 - a) * c (p.2 - a) * g (p.2 - p.1) ∂volume) =
        b p.1 * nonnegativeWindowOverlap d c (p.2 - p.1) * g (p.2 - p.1) := by
    have hm : Measurable (fun a : Rd d => c (p.1 - a) * c (p.2 - a)) :=
      (hc.comp (measurable_const.sub measurable_id)).mul
        (hc.comp (measurable_const.sub measurable_id))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      ((lintegral_const_mul (μ := volume) (b p.1 * g (p.2 - p.1)) hm).trans
        (congrArg (fun r => (b p.1 * g (p.2 - p.1)) * r) (htwist p)))
  calc
    (∫⁻ p, c p.1 * c p.2 * g (p.2 - p.1) ∂Γ) =
        ∫⁻ p, ∫⁻ a,
          b (a + p.1) * c p.1 * c p.2 * g (p.2 - p.1) ∂volume ∂Γ :=
      lintegral_congr (fun p => (hinner₁ p).symm)
    _ = ∫⁻ a, ∫⁻ p,
        b (a + p.1) * c p.1 * c p.2 * g (p.2 - p.1) ∂Γ ∂volume :=
      (lintegral_lintegral_swap (μ := (volume : Measure (Rd d))) (ν := Γ)
        (f := fun a p => b (a + p.1) * c p.1 * c p.2 * g (p.2 - p.1))
        hkernel₁.aemeasurable).symm
    _ = ∫⁻ a, ∫⁻ p,
        b p.1 * c (p.1 - a) * c (p.2 - a) * g (p.2 - p.1) ∂Γ ∂volume :=
      lintegral_congr hshift
    _ = ∫⁻ p, ∫⁻ a,
        b p.1 * c (p.1 - a) * c (p.2 - a) * g (p.2 - p.1) ∂volume ∂Γ :=
      lintegral_lintegral_swap (μ := (volume : Measure (Rd d))) (ν := Γ)
        hkernel₂.aemeasurable
    _ = _ := lintegral_congr hinner₂

/-- The overlap scales by the exact Euclidean volume factor. -/
theorem nonnegativeWindowOverlap_comp_inv_smul
    (d : ℕ) (c : Rd d → ℝ≥0∞) (hc : Measurable c)
    (L : ℝ) (hL : 0 < L) (z : Rd d) :
    nonnegativeWindowOverlap d (fun x => c (L⁻¹ • x)) z =
      ENNReal.ofReal (L ^ d) * nonnegativeWindowOverlap d c (L⁻¹ • z) := by
  let f : Rd d → ℝ≥0∞ := fun t => c t * c (t + L⁻¹ • z)
  have hf : Measurable f := hc.mul (hc.comp (measurable_id.add measurable_const))
  calc
    (∫⁻ t, c (L⁻¹ • t) * c (L⁻¹ • (t + z)) ∂volume) =
        ∫⁻ t, f (L⁻¹ • t) ∂volume := by
      simp only [f, smul_add]
    _ = ∫⁻ t, f t ∂(volume : Measure (Rd d)).map (fun t => L⁻¹ • t) :=
      (lintegral_map hf (measurable_const_smul (L⁻¹))).symm
    _ = ENNReal.ofReal (L ^ d) * ∫⁻ t, f t ∂volume := by
      rw [Measure.map_addHaar_smul (volume : Measure (Rd d)) (inv_ne_zero hL.ne'),
        lintegral_smul_measure]
      simp only [Rd, finrank_euclideanSpace_fin, inv_pow, inv_inv,
        abs_of_nonneg (pow_nonneg hL.le d), smul_eq_mul]

/-- The normalized stationary window identity. -/
theorem lintegral_stationaryPair_scaled_window_eq_cube_overlap
    (d : ℕ) (Γ : Measure (Rd d × Rd d)) [SFinite Γ]
    (hΓ : ∀ a : Rd d,
      Γ.map (fun p : Rd d × Rd d => (a + p.1, a + p.2)) = Γ)
    (c g : Rd d → ℝ≥0∞) (hc : Measurable c) (hg : Measurable g)
    (L : ℝ) (hL : 0 < L) :
    (ENNReal.ofReal (L ^ d))⁻¹ *
        (∫⁻ p, c (L⁻¹ • p.1) * c (L⁻¹ • p.2) * g (p.2 - p.1) ∂Γ) =
      ∫⁻ p, (cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
        nonnegativeWindowOverlap d c (L⁻¹ • (p.2 - p.1)) * g (p.2 - p.1) ∂Γ := by
  have hcL : Measurable (fun x : Rd d => c (L⁻¹ • x)) :=
    hc.comp (measurable_const_smul (L⁻¹))
  have hA0 : ENNReal.ofReal (L ^ d) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hL d)).ne'
  rw [lintegral_stationaryPair_window_eq_cube_overlap d Γ hΓ _ g hcL hg]
  simp_rw [nonnegativeWindowOverlap_comp_inv_smul d c hc L hL]
  calc
    (ENNReal.ofReal (L ^ d))⁻¹ *
        (∫⁻ p, (cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
          (ENNReal.ofReal (L ^ d) *
            nonnegativeWindowOverlap d c (L⁻¹ • (p.2 - p.1))) * g (p.2 - p.1) ∂Γ) =
      (ENNReal.ofReal (L ^ d))⁻¹ * (ENNReal.ofReal (L ^ d) *
        (∫⁻ p, (cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
          nonnegativeWindowOverlap d c (L⁻¹ • (p.2 - p.1)) * g (p.2 - p.1) ∂Γ)) := by
      congr 1
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (lintegral_const_mul' (μ := Γ) (ENNReal.ofReal (L ^ d))
          (fun p : Rd d × Rd d =>
            (cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
              nonnegativeWindowOverlap d c (L⁻¹ • (p.2 - p.1)) * g (p.2 - p.1))
          ENNReal.ofReal_ne_top)
    _ = _ := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hA0 ENNReal.ofReal_ne_top, one_mul]

end Riesz.Stationary


namespace Riesz.Stationary

def compactWindowPairAnchor (d : ℕ) (φ : C_c(Rd d, ℝ)) :
    C_c(Rd d × Rd d, ℝ) := by
  refine ⟨⟨fun p => φ p.1 * φ p.2,
    (φ.continuous.comp continuous_fst).mul (φ.continuous.comp continuous_snd)⟩, ?_⟩
  refine HasCompactSupport.of_support_subset_isCompact
    (φ.hasCompactSupport.isCompact.prod φ.hasCompactSupport.isCompact) ?_
  exact fun p hp => ⟨subset_tsupport φ (mul_ne_zero_iff.mp hp).1,
    subset_tsupport φ (mul_ne_zero_iff.mp hp).2⟩

def compactGaussianWindowPairTest (d : ℕ) (φ : C_c(Rd d, ℝ)) (u : ℝ) :
    C_c(Rd d × Rd d, ℝ) :=
  Riesz.Asymptotics.compactGaussianFactorialTest d (compactWindowPairAnchor d φ) u

def compactGaussianWindowKernel (d : ℕ) (φ : C_c(Rd d, ℝ)) (u : ℝ)
    (p : Rd d × Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (φ p.1) * ENNReal.ofReal (φ p.2) *
    ENNReal.ofReal (Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ)))

theorem measurable_compactGaussianWindowKernel (d : ℕ)
    (φ : C_c(Rd d, ℝ)) (u : ℝ) :
    Measurable (compactGaussianWindowKernel d φ u) := by
  exact ((φ.continuous.measurable.ennreal_ofReal.comp measurable_fst).mul
    (φ.continuous.measurable.ennreal_ofReal.comp measurable_snd)).mul
    (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp
        (continuous_const.mul ((continuous_snd.sub continuous_fst).norm.pow 2))).measurable)

theorem compactGaussianWindowPairTest_nonneg (d : ℕ)
    (φ : C_c(Rd d, ℝ)) (hφ : ∀ x, 0 ≤ φ x) (u : ℝ) :
    ∀ p, 0 ≤ compactGaussianWindowPairTest d φ u p := by
  exact Riesz.Asymptotics.compactGaussianFactorialTest_nonneg d (compactWindowPairAnchor d φ)
    (fun p => mul_nonneg (hφ p.1) (hφ p.2)) u

theorem compactGaussianWindowKernel_eq_ofReal_test (d : ℕ)
    (φ : C_c(Rd d, ℝ)) (hφ : ∀ x, 0 ≤ φ x) (u : ℝ) (p : Rd d × Rd d) :
    compactGaussianWindowKernel d φ u p =
      ENNReal.ofReal (compactGaussianWindowPairTest d φ u p) := by
  change ENNReal.ofReal (φ p.1) * ENNReal.ofReal (φ p.2) *
    ENNReal.ofReal (Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ))) =
      ENNReal.ofReal (φ p.1 * φ p.2 * Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ)))
  rw [ENNReal.ofReal_mul (mul_nonneg (hφ p.1) (hφ p.2)), ENNReal.ofReal_mul (hφ p.1)]

theorem lintegral_gaussian_cutoff_product_eq
    (d : ℕ) (φ : C_c(Rd d, ℝ)) (u : ℝ)
    (μ ν : Measure (Rd d)) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    (∫⁻ p : Rd d × Rd d,
      ENNReal.ofReal (Real.exp (-u * ‖p.1 - p.2‖ ^ (2 : ℕ)))
        ∂(cutoffMeasure d μ φ : Measure (Rd d)).prod
          (cutoffMeasure d ν φ : Measure (Rd d))) =
      ∫⁻ p, compactGaussianWindowKernel d φ u p ∂μ.prod ν := by
  have hc : Measurable (fun x : Rd d => ENNReal.ofReal (φ x)) :=
    φ.continuous.measurable.ennreal_ofReal
  have hg : Measurable (fun p : Rd d × Rd d =>
      ENNReal.ofReal (Real.exp (-u * ‖p.1 - p.2‖ ^ (2 : ℕ)))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp
        (continuous_const.mul ((continuous_fst.sub continuous_snd).norm.pow 2))).measurable
  change (∫⁻ p : Rd d × Rd d,
      ENNReal.ofReal (Real.exp (-u * ‖p.1 - p.2‖ ^ (2 : ℕ)))
        ∂(μ.withDensity (fun x => ENNReal.ofReal (φ x))).prod
          (ν.withDensity (fun x => ENNReal.ofReal (φ x)))) = _
  rw [prod_withDensity hc hc]
  rw [lintegral_withDensity_eq_lintegral_mul (μ.prod ν)
    (f := fun p : Rd d × Rd d => ENNReal.ofReal (φ p.1) * ENNReal.ofReal (φ p.2))
    ((hc.comp measurable_fst).mul (hc.comp measurable_snd)) hg]
  simp only [Pi.mul_apply, compactGaussianWindowKernel, norm_sub_rev]

theorem countingGaussianWindow_allPair_eq_factorial_add_diagonal
    (d : ℕ) (μ : CountingConfiguration d)
    (φ : C_c(Rd d, ℝ)) (hφ : ∀ x, 0 ≤ φ x) (u : ℝ) :
    (∫⁻ p, compactGaussianWindowKernel d φ u p ∂μ.val.prod μ.val) =
      ENNReal.ofReal (countingFactorialIntegral d μ (compactGaussianWindowPairTest d φ u)) +
      ENNReal.ofReal (∫ x, (φ x) ^ 2 ∂μ.val) := by
  let f := compactGaussianWindowPairTest d φ u
  have hf : ∀ p, 0 ≤ f p := compactGaussianWindowPairTest_nonneg d φ hφ u
  have hdiag : (fun x : Rd d => f (x, x)) = (fun x => (φ x) ^ 2) := by
    change (fun x : Rd d => φ x * φ x * Real.exp (-u * ‖x - x‖ ^ (2 : ℕ))) = _
    simp only [sub_self, norm_zero, zero_pow (show (2 : ℕ) ≠ 0 from two_ne_zero),
      mul_zero, Real.exp_zero, mul_one, pow_two]
  have hsplit : (∫ p, f p ∂μ.val.prod μ.val) =
      countingFactorialIntegral d μ f + ∫ x, (φ x) ^ 2 ∂μ.val := by
    rw [countingFactorialIntegral, hdiag, sub_add_cancel]
  calc
    (∫⁻ p, compactGaussianWindowKernel d φ u p ∂μ.val.prod μ.val) =
        ∫⁻ p, ENNReal.ofReal (f p) ∂μ.val.prod μ.val :=
      lintegral_congr (compactGaussianWindowKernel_eq_ofReal_test d φ hφ u)
    _ = ENNReal.ofReal (∫ p, f p ∂μ.val.prod μ.val) :=
      (ofReal_integral_eq_lintegral_ofReal f.integrable
        (Filter.Eventually.of_forall hf)).symm
    _ = ENNReal.ofReal (countingFactorialIntegral d μ f + ∫ x, (φ x) ^ 2 ∂μ.val) :=
      congrArg ENNReal.ofReal hsplit
    _ = _ := ENNReal.ofReal_add (countingFactorialIntegral_nonneg d μ f hf)
      (integral_nonneg (fun x => sq_nonneg (φ x)))

/-- Finite Gaussian positivity in terms of factorial and diagonal contributions. -/
theorem countingGaussianWindow_mixed_le_factorial_diagonal_background
    (d : ℕ) (μ : CountingConfiguration d)
    (φ : C_c(Rd d, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
    (u : ℝ) (hu : 0 < u) :
    (2 : ℝ≥0∞) * (∫⁻ p, compactGaussianWindowKernel d φ u p
        ∂μ.val.prod (volume : Measure (Rd d))) ≤
      (ENNReal.ofReal (countingFactorialIntegral d μ (compactGaussianWindowPairTest d φ u)) +
        ENNReal.ofReal (∫ x, (φ x) ^ 2 ∂μ.val)) +
      ∫⁻ p, compactGaussianWindowKernel d φ u p
        ∂(volume : Measure (Rd d)).prod volume := by
  let μφ : Measure (Rd d) := cutoffMeasure d μ.val φ
  let νφ : Measure (Rd d) := cutoffMeasure d (volume : Measure (Rd d)) φ
  letI : IsFiniteMeasure μφ := inferInstanceAs
    (IsFiniteMeasure (cutoffMeasure d μ.val φ : Measure (Rd d)))
  letI : IsFiniteMeasure νφ := inferInstanceAs
    (IsFiniteMeasure (cutoffMeasure d (volume : Measure (Rd d)) φ : Measure (Rd d)))
  let g : Rd d × Rd d → ℝ := fun p => Real.exp (-u * ‖p.1 - p.2‖ ^ (2 : ℕ))
  have hconv (ρ σ : Measure (Rd d)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ] :
      ENNReal.ofReal (∫ p, g p ∂ρ.prod σ) =
        ∫⁻ p, ENNReal.ofReal (g p) ∂ρ.prod σ :=
    ofReal_integral_eq_lintegral_ofReal
      (Riesz.Analysis.integrable_gaussian_prod_measure u hu.le ρ σ)
      (Filter.Eventually.of_forall (fun p => (Real.exp_pos _).le))
  have hpos : 0 ≤ (∫ p, g p ∂μφ.prod μφ) -
      2 * (∫ p, g p ∂μφ.prod νφ) + (∫ p, g p ∂νφ.prod νφ) :=
    Riesz.Analysis.gaussian_quadratic_nonneg u hu μφ νφ
  have hquad : 2 * (∫ p, g p ∂μφ.prod νφ) ≤
      (∫ p, g p ∂μφ.prod μφ) + (∫ p, g p ∂νφ.prod νφ) := by
    linarith
  have hquadENN : (2 : ℝ≥0∞) *
      (∫⁻ p, ENNReal.ofReal (g p) ∂μφ.prod νφ) ≤
      (∫⁻ p, ENNReal.ofReal (g p) ∂μφ.prod μφ) +
      (∫⁻ p, ENNReal.ofReal (g p) ∂νφ.prod νφ) := by
    have h := ENNReal.ofReal_le_ofReal hquad
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 from zero_le_two),
      ENNReal.ofReal_add (integral_nonneg (fun _ => (Real.exp_pos _).le))
        (integral_nonneg (fun _ => (Real.exp_pos _).le)), hconv, hconv, hconv] at h
    simpa using h
  simpa only [μφ, νφ, g, lintegral_gaussian_cutoff_product_eq,
    countingGaussianWindow_allPair_eq_factorial_add_diagonal d μ φ hφ u] using hquadENN

end Riesz.Stationary
namespace Riesz.Configuration

theorem countingLawOfSimple_localSecond_of_admissible
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P) :
    ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2
        ∂countingLawOfSimple d P) < ∞ := by
  intro n
  have h := hP.2.2.2.2 (Metric.closedBall (0 : Rd d) (n : ℝ))
    measurableSet_closedBall Metric.isBounded_closedBall
  rw [← countingLawOfSimple_map_val d P hP.2.1,
    lintegral_map ((Measure.measurable_coe measurableSet_closedBall).pow_const 2)
      measurable_subtype_coe] at h
  exact h

theorem countingLawOfSimple_ae_simple_of_admissible
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P) :
    ∀ᵐ μ ∂countingLawOfSimple d P, IsSimpleConfiguration d μ.val := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_isSimpleConfiguration d)).mp
  simpa only [countingLawOfSimple_map_val d P hP.2.1] using hP.2.1

/-- The already constructed factorial measure of the original admissible law. -/
def originalAdmissibleFactorialMeasure
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P) :
    Measure (Rd d × Rd d) :=
  expectedFactorialMeasure d (countingLawOfSimple d P)
    (countingLawOfSimple_localSecond_of_admissible d P hP)

instance originalAdmissibleFactorialMeasure_regular
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P) :
    (originalAdmissibleFactorialMeasure d P hP).Regular :=
  expectedFactorialMeasure_regular d (countingLawOfSimple d P)
    (countingLawOfSimple_localSecond_of_admissible d P hP)

theorem originalAdmissibleFactorialMeasure_map_diagAdd_eq_self
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P) (a : Rd d) :
    (originalAdmissibleFactorialMeasure d P hP).map
      (fun p : Rd d × Rd d => (a + p.1, a + p.2)) =
        originalAdmissibleFactorialMeasure d P hP := by
  refine expectedFactorialMeasure_map_diagAdd_eq_self d (countingLawOfSimple d P)
    (countingLawOfSimple_localSecond_of_admissible d P hP)
    (countingLawOfSimple_ae_simple_of_admissible d P hP) ?_ a
  simpa only [countingLawOfSimple_map_val d P hP.2.1] using hP.2.2.1

theorem lintegral_originalAdmissibleFactorialMeasure_eq_pair_lintegral
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ p, k p ∂originalAdmissibleFactorialMeasure d P hP) =
      ∫⁻ μ, ∫⁻ x, ∫⁻ y, if x = y then 0 else k (x, y) ∂μ ∂μ ∂P := by
  let Qc := countingLawOfSimple d P
  have hmap : Qc.map Subtype.val = P := countingLawOfSimple_map_val d P hP.2.1
  let k₀ : Rd d × Rd d → ℝ≥0∞ := fun p => if p.1 = p.2 then 0 else k p
  have hk₀ : Measurable k₀ :=
    Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const hk
  have hF : AEMeasurable
      (fun μ : Measure (Rd d) => ∫⁻ x, ∫⁻ y, k₀ (x, y) ∂μ ∂μ)
      (Qc.map Subtype.val) := by
    simpa only [hmap] using aemeasurable_pair_lintegral_of_simple d P hP.2.1 k₀ hk₀
  calc
    (∫⁻ p, k p ∂originalAdmissibleFactorialMeasure d P hP) =
        ∫⁻ μ, ∫⁻ x, ∫⁻ y, k₀ (x, y) ∂μ.val ∂μ.val ∂Qc :=
      lintegral_expectedFactorialMeasure_eq_pair_lintegral d Qc
        (countingLawOfSimple_localSecond_of_admissible d P hP)
        (countingLawOfSimple_ae_simple_of_admissible d P hP) k hk
    _ = ∫⁻ μ, ∫⁻ x, ∫⁻ y, k₀ (x, y) ∂μ ∂μ ∂Qc.map Subtype.val :=
      (lintegral_map' hF measurable_subtype_coe.aemeasurable).symm
    _ = _ := congrArg (fun M => ∫⁻ μ, ∫⁻ x, ∫⁻ y, k₀ (x, y) ∂μ ∂μ ∂M) hmap

theorem Q_eq_originalAdmissibleFactorialMeasure
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P) (u : ℝ) :
    Q d P u = ∫⁻ p, Riesz.Stationary.anchoredGaussianKernel d u p
      ∂originalAdmissibleFactorialMeasure d P hP := by
  have h := Q_map_val_eq_expectedFactorialMeasure d (countingLawOfSimple d P)
    (countingLawOfSimple_localSecond_of_admissible d P hP)
    (countingLawOfSimple_ae_simple_of_admissible d P hP) u
  rwa [countingLawOfSimple_map_val d P hP.2.1] at h

end Riesz.Configuration

namespace Riesz.Stationary

/-- Exact window identity for the original admissible configuration law. -/
theorem originalAdmissible_scaled_window_factorial_eq_cube_overlap
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (c g : Rd d → ℝ≥0∞) (hc : Measurable c) (hg : Measurable g)
    (L : ℝ) (hL : 0 < L) :
    (ENNReal.ofReal (L ^ d))⁻¹ *
        (∫⁻ μ, ∫⁻ x, ∫⁻ y,
          if x = y then 0 else c (L⁻¹ • x) * c (L⁻¹ • y) * g (y - x) ∂μ ∂μ ∂P) =
      ∫⁻ p, (cube d 1).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
        nonnegativeWindowOverlap d c (L⁻¹ • (p.2 - p.1)) * g (p.2 - p.1)
          ∂originalAdmissibleFactorialMeasure d P hP := by
  let Γ := originalAdmissibleFactorialMeasure d P hP
  letI : SFinite Γ := by
    dsimp only [Γ, originalAdmissibleFactorialMeasure]
    infer_instance
  have hk : Measurable (fun p : Rd d × Rd d =>
      c (L⁻¹ • p.1) * c (L⁻¹ • p.2) * g (p.2 - p.1)) :=
    ((hc.comp ((measurable_const_smul (L⁻¹)).comp measurable_fst)).mul
      (hc.comp ((measurable_const_smul (L⁻¹)).comp measurable_snd))).mul
      (hg.comp (measurable_snd.sub measurable_fst))
  rw [← lintegral_originalAdmissibleFactorialMeasure_eq_pair_lintegral d P hP _ hk]
  exact lintegral_stationaryPair_scaled_window_eq_cube_overlap d Γ
    (originalAdmissibleFactorialMeasure_map_diagAdd_eq_self d P hP) c g hc hg L hL

/-- Real overlap of a compact window at a specified physical scale. -/
def compactWindowOverlap (d : ℕ) (χ : C_c(Rd d, ℝ)) (L : ℝ) (z : Rd d) : ℝ :=
  ∫ t, χ t * χ (t + L⁻¹ • z) ∂volume

theorem nonnegativeWindowOverlap_ofReal
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (z : Rd d) :
    nonnegativeWindowOverlap d (fun x => ENNReal.ofReal (χ x)) z =
      ENNReal.ofReal (∫ t, χ t * χ (t + z) ∂volume) := by
  let F : C_c(Rd d, ℝ) :=
    ⟨⟨fun t => χ t * χ (t + z),
      χ.continuous.mul (χ.continuous.comp (continuous_id.add continuous_const))⟩,
      χ.hasCompactSupport.mul_right⟩
  have hfi : Integrable (fun t => χ t * χ (t + z))
      (volume : Measure (Rd d)) := F.integrable
  exact ((ofReal_integral_eq_lintegral_ofReal hfi
    (Filter.Eventually.of_forall (fun t => mul_nonneg (hχ t) (hχ (t + z))))).trans
      (lintegral_congr (fun t => ENNReal.ofReal_mul (hχ t)))).symm

/-- Original-process overlap with precisely the Showcase Gaussian anchor. -/
theorem originalAdmissible_scaled_compactGaussian_factorial_eq_cube_overlap
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℝ) (hL : 0 < L) (u : ℝ) :
    (ENNReal.ofReal (L ^ d))⁻¹ *
        (∫⁻ μ, ∫⁻ x, ∫⁻ y, if x = y then 0 else
          ENNReal.ofReal (χ (L⁻¹ • x) * χ (L⁻¹ • y) *
            Real.exp (-(u * ‖y - x‖ ^ (2 : ℕ)))) ∂μ ∂μ ∂P) =
      ∫⁻ p, ENNReal.ofReal (compactWindowOverlap d χ L (p.2 - p.1)) *
        anchoredGaussianKernel d u p ∂originalAdmissibleFactorialMeasure d P hP := by
  have hc : Measurable (fun x : Rd d => ENNReal.ofReal (χ x)) :=
    ENNReal.measurable_ofReal.comp χ.continuous.measurable
  have hg : Measurable (fun z : Rd d =>
      ENNReal.ofReal (Real.exp (-(u * ‖z‖ ^ (2 : ℕ))))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp
        ((continuous_const.mul (continuous_id.norm.pow 2)).neg)).measurable
  have hprod (x y : Rd d) :
      ENNReal.ofReal (χ (L⁻¹ • x) * χ (L⁻¹ • y) *
        Real.exp (-(u * ‖y - x‖ ^ (2 : ℕ)))) =
      ENNReal.ofReal (χ (L⁻¹ • x)) * ENNReal.ofReal (χ (L⁻¹ • y)) *
        ENNReal.ofReal (Real.exp (-(u * ‖y - x‖ ^ (2 : ℕ)))) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (hχ _) (hχ _)), ENNReal.ofReal_mul (hχ _)]
  simp_rw [hprod]
  rw [originalAdmissible_scaled_window_factorial_eq_cube_overlap d P hP _ _ hc hg L hL]
  simp_rw [nonnegativeWindowOverlap_ofReal d χ hχ]
  simp only [compactWindowOverlap, anchoredGaussianKernel, Set.indicator_apply,
    ite_mul, mul_ite, one_mul, zero_mul, mul_comm]

end Riesz.Stationary

namespace Riesz.Stationary

/-- Compact Gaussian variance bound for the actual original admissible law. -/
theorem compactGaussian_background_le_factorial_add_diagonal_of_admissible
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (φ : C_c(Rd d, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
    (u : ℝ) (hu : 0 < u) :
    (∫⁻ p, compactGaussianWindowKernel d φ u p
      ∂(volume : Measure (Rd d)).prod volume) ≤
      (∫⁻ p, compactGaussianWindowKernel d φ u p
        ∂originalAdmissibleFactorialMeasure d P hP) +
      ∫⁻ x, ENNReal.ofReal ((φ x) ^ 2) ∂volume := by
  let Qc : Measure (CountingConfiguration d) := countingLawOfSimple d P
  letI : IsProbabilityMeasure P := hP.1
  letI : IsProbabilityMeasure Qc := inferInstanceAs
    (IsProbabilityMeasure (countingLawOfSimple d P))
  let Γ := originalAdmissibleFactorialMeasure d P hP
  let f := compactGaussianWindowPairTest d φ u
  let k := compactGaussianWindowKernel d φ u
  let C : CountingConfiguration d → ℝ≥0∞ :=
    fun μ => ∫⁻ p, k p ∂μ.val.prod (volume : Measure (Rd d))
  let F : CountingConfiguration d → ℝ≥0∞ :=
    fun μ => ENNReal.ofReal (countingFactorialIntegral d μ f)
  let Z : CountingConfiguration d → ℝ≥0∞ :=
    fun μ => ENNReal.ofReal (∫ x, (φ x) ^ 2 ∂μ.val)
  let D : ℝ≥0∞ := ∫⁻ p, k p ∂(volume : Measure (Rd d)).prod volume
  have hk : Measurable k := measurable_compactGaussianWindowKernel d φ u
  have hf : ∀ p, 0 ≤ f p := compactGaussianWindowPairTest_nonneg d φ hφ u
  have hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂Qc) < ∞ :=
    countingLawOfSimple_localSecond_of_admissible d P hP
  have hmap : Qc.map Subtype.val = P := countingLawOfSimple_map_val d P hP.2.1
  have hmean (a : Rd d → ℝ≥0∞) (ha : Measurable a) :
      (∫⁻ μ, ∫⁻ x, a x ∂μ.val ∂Qc) = ∫⁻ x, a x ∂volume :=
    calc
      (∫⁻ μ, ∫⁻ x, a x ∂μ.val ∂Qc) =
          ∫⁻ μ, ∫⁻ x, a x ∂μ ∂Qc.map Subtype.val :=
        (lintegral_map (Measure.measurable_lintegral ha) measurable_subtype_coe).symm
      _ = ∫⁻ μ, ∫⁻ x, a x ∂μ ∂P :=
        congrArg (fun M => ∫⁻ μ, ∫⁻ x, a x ∂μ ∂M) hmap
      _ = ∫⁻ x, a x ∂P.join := (Measure.lintegral_join ha.aemeasurable).symm
      _ = ∫⁻ x, a x ∂volume :=
        congrArg (fun ρ : Measure (Rd d) => ∫⁻ x, a x ∂ρ)
          (join_eq_volume_of_admissible d P hP)
  have hC : (∫⁻ μ, C μ ∂Qc) = D :=
    calc
      (∫⁻ μ, C μ ∂Qc) =
          ∫⁻ μ, ∫⁻ x, ∫⁻ y, k (x, y) ∂volume ∂μ.val ∂Qc :=
        lintegral_congr (fun μ => lintegral_prod k hk.aemeasurable)
      _ = ∫⁻ x, ∫⁻ y, k (x, y) ∂volume ∂volume :=
        hmean _ hk.lintegral_prod_right'
      _ = D := (lintegral_prod k hk.aemeasurable).symm
  have hFmeas : Measurable F :=
    (continuous_countingFactorialIntegral d f).measurable.ennreal_ofReal
  have hF : (∫⁻ μ, F μ ∂Qc) = ∫⁻ p, k p ∂Γ :=
    calc
      (∫⁻ μ, F μ ∂Qc) = ENNReal.ofReal (∫ μ, countingFactorialIntegral d μ f ∂Qc) :=
        (ofReal_integral_eq_lintegral_ofReal
          (integrable_countingFactorialIntegral d Qc hsecond f)
          (Filter.Eventually.of_forall (fun μ => countingFactorialIntegral_nonneg d μ f hf))).symm
      _ = ENNReal.ofReal (∫ p, f p ∂Γ) :=
        congrArg ENNReal.ofReal (integral_expectedFactorialMeasure d Qc hsecond f).symm
      _ = ∫⁻ p, ENNReal.ofReal (f p) ∂Γ :=
        ofReal_integral_eq_lintegral_ofReal f.integrable (Filter.Eventually.of_forall hf)
      _ = ∫⁻ p, k p ∂Γ :=
        lintegral_congr (fun p => (compactGaussianWindowKernel_eq_ofReal_test d φ hφ u p).symm)
  have hZpoint (μ : CountingConfiguration d) :
      Z μ = ∫⁻ x, ENNReal.ofReal ((φ x) ^ 2) ∂μ.val :=
    ofReal_integral_eq_lintegral_ofReal
      (((φ * φ : C_c(Rd d, ℝ)).integrable (μ := μ.val)).congr
        (Filter.Eventually.of_forall (fun x => (pow_two (φ x)).symm)))
      (Filter.Eventually.of_forall (fun x => sq_nonneg (φ x)))
  have hZ : (∫⁻ μ, Z μ ∂Qc) = ∫⁻ x, ENNReal.ofReal ((φ x) ^ 2) ∂volume :=
    (lintegral_congr hZpoint).trans (hmean _ (φ.continuous.pow 2).measurable.ennreal_ofReal)
  have hD : D ≠ ∞ :=
    (lintegral_gaussian_cutoff_product_eq d φ u (volume : Measure (Rd d)) volume).symm.trans_ne
      ((ofReal_integral_eq_lintegral_ofReal
        (Riesz.Analysis.integrable_gaussian_prod_measure u hu.le
          (cutoffMeasure d (volume : Measure (Rd d)) φ : Measure (Rd d))
          (cutoffMeasure d (volume : Measure (Rd d)) φ : Measure (Rd d)))
        (Filter.Eventually.of_forall (fun p => (Real.exp_pos _).le))).symm.trans_ne
          ENNReal.ofReal_ne_top)
  have hpoint (μ : CountingConfiguration d) :
      (2 : ℝ≥0∞) * C μ ≤ (F μ + Z μ) + D :=
    countingGaussianWindow_mixed_le_factorial_diagonal_background d μ φ hφ u hu
  have htotal : (2 : ℝ≥0∞) * D ≤
      ((∫⁻ p, k p ∂Γ) + ∫⁻ x, ENNReal.ofReal ((φ x) ^ 2) ∂volume) + D := by
    have h := lintegral_mono (μ := Qc) hpoint
    rw [lintegral_const_mul' (2 : ℝ≥0∞) C ENNReal.ofNat_ne_top,
      lintegral_add_right _ measurable_const, lintegral_add_left hFmeas Z,
      lintegral_const, measure_univ, mul_one, hC, hF, hZ] at h
    exact h
  rw [two_mul] at htotal
  exact ENNReal.le_of_add_le_add_right hD htotal

def compactAnchorSquareMass (d : ℕ) (χ : C_c(Rd d, ℝ)) : ℝ :=
  ∫ x, (χ x) ^ 2 ∂volume

theorem compactWindowOverlap_nonneg_le_norm_of_integral_one
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (hχnorm : (∫ x, χ x ∂volume) = 1) (L : ℝ) (z : Rd d) :
    0 ≤ compactWindowOverlap d χ L z ∧
      compactWindowOverlap d χ L z ≤ ‖χ.toBoundedContinuousFunction‖ := by
  let M : ℝ := ‖χ.toBoundedContinuousFunction‖
  let F : C_c(Rd d, ℝ) :=
    ⟨⟨fun t => χ t * χ (t + L⁻¹ • z),
      χ.continuous.mul (χ.continuous.comp (continuous_id.add continuous_const))⟩,
      χ.hasCompactSupport.mul_right⟩
  have hfi : Integrable (fun t => χ t * χ (t + L⁻¹ • z))
      (volume : Measure (Rd d)) := F.integrable
  have hbound (t : Rd d) : χ t * χ (t + L⁻¹ • z) ≤ M * χ t :=
    (mul_le_mul_of_nonneg_left
      ((Real.le_norm_self _).trans
        (χ.toBoundedContinuousFunction.norm_coe_le_norm (t + L⁻¹ • z)))
      (hχ t)).trans_eq (mul_comm _ _)
  refine ⟨integral_nonneg (fun t => mul_nonneg (hχ t) (hχ _)), ?_⟩
  calc
    compactWindowOverlap d χ L z ≤ ∫ t, M * χ t ∂volume :=
      integral_mono hfi (χ.integrable.const_mul M) hbound
    _ = M := (integral_const_mul M (fun t => χ t)).trans
      ((congrArg (fun a : ℝ => M * a) hχnorm).trans (mul_one M))
theorem compactWindowOverlap_tendsto_of_inv_tendsto_zero
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℕ → ℝ) (hLinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0))
    (z : Rd d) :
    Tendsto (fun n => compactWindowOverlap d χ (L n) z) atTop
      (𝓝 (compactAnchorSquareMass d χ)) := by
  let M : ℝ := ‖χ.toBoundedContinuousFunction‖
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun t : Rd d => χ t * χ (t + (L n)⁻¹ • z)) volume :=
    (χ.continuous.mul (χ.continuous.comp
      (continuous_id.add continuous_const))).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ t ∂(volume : Measure (Rd d)),
      ‖χ t * χ (t + (L n)⁻¹ • z)‖ ≤ M * χ t :=
    Filter.Eventually.of_forall (fun t =>
      calc
        ‖χ t * χ (t + (L n)⁻¹ • z)‖ = χ t * χ (t + (L n)⁻¹ • z) :=
          (Real.norm_eq_abs _).trans (abs_of_nonneg (mul_nonneg (hχ t) (hχ _)))
        _ ≤ M * χ t :=
          (mul_le_mul_of_nonneg_left
            ((Real.le_norm_self _).trans
              (χ.toBoundedContinuousFunction.norm_coe_le_norm (t + (L n)⁻¹ • z)))
            (hχ t)).trans_eq (mul_comm _ _))
  have harg (t : Rd d) : Tendsto (fun n => t + (L n)⁻¹ • z) atTop (𝓝 t) := by
    simpa only [zero_smul, add_zero] using
      ((tendsto_const_nhds (x := t) (f := (atTop : Filter ℕ))).add
        (hLinv.smul (tendsto_const_nhds (x := z))))
  have hpoint (t : Rd d) :
      Tendsto (fun n => χ t * χ (t + (L n)⁻¹ • z)) atTop (𝓝 ((χ t) ^ 2)) := by
    simpa only [pow_two, Function.comp_def, CompactlySupportedContinuousMap.coe_toContinuousMap] using
      ((tendsto_const_nhds (x := χ t)).mul ((χ.continuous.tendsto t).comp (harg t)))
  exact tendsto_integral_of_dominated_convergence (fun t => M * χ t)
    hmeas (χ.integrable.const_mul M) hbound
    (Filter.Eventually.of_forall hpoint)
theorem fixedGaussian_overlap_lintegral_tendsto
    (d : ℕ) (Γ : Measure (Rd d × Rd d)) (u : ℝ)
    (hfin : (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) ≠ ∞)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (hχnorm : (∫ x, χ x ∂volume) = 1)
    (L : ℕ → ℝ) (hLinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ p,
      ENNReal.ofReal (compactWindowOverlap d χ (L n) (p.2 - p.1)) *
        anchoredGaussianKernel d u p ∂Γ) atTop
      (𝓝 (ENNReal.ofReal (compactAnchorSquareMass d χ) *
        (∫⁻ p, anchoredGaussianKernel d u p ∂Γ))) := by
  let k : Rd d × Rd d → ℝ≥0∞ := anchoredGaussianKernel d u
  let ν : Measure (Rd d × Rd d) := Γ.withDensity k
  let M : ℝ := ‖χ.toBoundedContinuousFunction‖
  let F : ℕ → (Rd d × Rd d) → ℝ≥0∞ :=
    fun n p => ENNReal.ofReal (compactWindowOverlap d χ (L n) (p.2 - p.1))
  have hk : Measurable k := measurable_anchoredGaussianKernel d u
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfin
  have hmass : ν Set.univ = ∫⁻ p, anchoredGaussianKernel d u p ∂Γ := by
    change (Γ.withDensity k) Set.univ = ∫⁻ p, k p ∂Γ
    rw [withDensity_apply k MeasurableSet.univ, Measure.restrict_univ]
  have hF (n : ℕ) : Measurable (F n) := by
    have heq : F n = fun p : Rd d × Rd d =>
        nonnegativeWindowOverlap d (fun x => ENNReal.ofReal (χ x))
          ((L n)⁻¹ • (p.2 - p.1)) :=
      funext (fun p => (nonnegativeWindowOverlap_ofReal d χ hχ _).symm)
    rw [heq]
    exact (measurable_nonnegativeWindowOverlap d _
      χ.continuous.measurable.ennreal_ofReal).comp
      ((measurable_const_smul ((L n)⁻¹)).comp
        (measurable_snd.sub measurable_fst))
  have hbound (n : ℕ) : F n ≤ᵐ[ν] (fun _ => ENNReal.ofReal M) :=
    Filter.Eventually.of_forall (fun p => ENNReal.ofReal_le_ofReal
      (compactWindowOverlap_nonneg_le_norm_of_integral_one
        d χ hχ hχnorm (L n) (p.2 - p.1)).2)
  have hdom : (∫⁻ p, ENNReal.ofReal M ∂ν) ≠ ∞ := by
    rw [lintegral_const, hmass]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hpoint : ∀ᵐ p ∂ν,
      Tendsto (fun n => F n p) atTop
        (𝓝 (ENNReal.ofReal (compactAnchorSquareMass d χ))) :=
    Filter.Eventually.of_forall (fun p => ENNReal.tendsto_ofReal
      (compactWindowOverlap_tendsto_of_inv_tendsto_zero
        d χ hχ L hLinv (p.2 - p.1)))
  have hdct := tendsto_lintegral_of_dominated_convergence
    (μ := ν) (fun _ => ENNReal.ofReal M) hF hbound hdom hpoint
  have htransport (n : ℕ) : (∫⁻ p, F n p ∂ν) =
      ∫⁻ p, F n p * anchoredGaussianKernel d u p ∂Γ :=
    (lintegral_withDensity_eq_lintegral_mul Γ hk (hF n)).trans
      (lintegral_congr (fun p => mul_comm _ _))
  have htarget : (∫⁻ p, ENNReal.ofReal (compactAnchorSquareMass d χ) ∂ν) =
      ENNReal.ofReal (compactAnchorSquareMass d χ) *
        (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) :=
    (lintegral_const _).trans (congrArg (fun a : ℝ≥0∞ =>
      ENNReal.ofReal (compactAnchorSquareMass d χ) * a) hmass)
  simpa only [htransport, htarget] using hdct

theorem stationary_compactGaussianWindow_normalized_tendsto
    (d : ℕ) (Γ : Measure (Rd d × Rd d)) [SFinite Γ]
    (hΓ : ∀ a : Rd d,
      Γ.map (fun p : Rd d × Rd d => (a + p.1, a + p.2)) = Γ)
    (u : ℝ) (hfin : (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) ≠ ∞)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (hχnorm : (∫ x, χ x ∂volume) = 1)
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (hLinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun n => (ENNReal.ofReal ((L n) ^ d))⁻¹ *
      (∫⁻ p, ENNReal.ofReal (χ ((L n)⁻¹ • p.1)) *
        ENNReal.ofReal (χ ((L n)⁻¹ • p.2)) *
        ENNReal.ofReal (Real.exp (-(u * ‖p.2 - p.1‖ ^ (2 : ℕ)))) ∂Γ)) atTop
      (𝓝 (ENNReal.ofReal (compactAnchorSquareMass d χ) *
        (∫⁻ p, anchoredGaussianKernel d u p ∂Γ))) := by
  have hc : Measurable (fun x : Rd d => ENNReal.ofReal (χ x)) :=
    χ.continuous.measurable.ennreal_ofReal
  have hg : Measurable (fun z : Rd d =>
      ENNReal.ofReal (Real.exp (-(u * ‖z‖ ^ (2 : ℕ))))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp
        ((continuous_const.mul (continuous_id.norm.pow 2)).neg)).measurable
  have hdct := fixedGaussian_overlap_lintegral_tendsto d Γ u hfin χ hχ hχnorm L hLinv
  have heq (n : ℕ) : (ENNReal.ofReal ((L n) ^ d))⁻¹ *
      (∫⁻ p, ENNReal.ofReal (χ ((L n)⁻¹ • p.1)) *
        ENNReal.ofReal (χ ((L n)⁻¹ • p.2)) *
        ENNReal.ofReal (Real.exp (-(u * ‖p.2 - p.1‖ ^ (2 : ℕ)))) ∂Γ) =
        ∫⁻ p, ENNReal.ofReal (compactWindowOverlap d χ (L n) (p.2 - p.1)) *
          anchoredGaussianKernel d u p ∂Γ := by
    rw [lintegral_stationaryPair_scaled_window_eq_cube_overlap
      d Γ hΓ _ _ hc hg (L n) (hL n)]
    simp_rw [nonnegativeWindowOverlap_ofReal d χ hχ]
    simp only [compactWindowOverlap, anchoredGaussianKernel, Set.indicator_apply,
      ite_mul, mul_ite, one_mul, zero_mul, mul_comm]
  simpa only [← heq] using hdct

theorem compactAnchorSquareMass_pos_of_integral_one
    (d : ℕ) (χ : C_c(Rd d, ℝ))
    (hχnorm : (∫ x, χ x ∂volume) = 1) :
    0 < compactAnchorSquareMass d χ := by
  have hex : ∃ x : Rd d, χ x ≠ 0 := by
    by_contra h
    have hz : χ = 0 := CompactlySupportedContinuousMap.ext
      (fun x => not_not.mp (fun hx => h ⟨x, hx⟩))
    simp only [hz, CompactlySupportedContinuousMap.zero_apply, integral_zero,
      zero_ne_one] at hχnorm
  obtain ⟨x, hx⟩ := hex
  have hfi : Integrable (fun x : Rd d => (χ x) ^ 2) volume :=
    (((χ * χ : C_c(Rd d, ℝ)).integrable (μ := volume)).congr
      (Filter.Eventually.of_forall (fun x => (pow_two (χ x)).symm)))
  exact integral_pos_of_integrable_nonneg_nonzero (μ := volume) (x := x)
    (χ.continuous.pow 2) hfi (fun x => sq_nonneg (χ x)) (pow_ne_zero 2 hx)

theorem gaussian_covariance_bound_of_scaled_limit_ineq
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (q : ℝ≥0∞) (hq : q ≠ ∞)
    (h : ENNReal.ofReal (a * b) ≤ ENNReal.ofReal a * q + ENNReal.ofReal a) :
    ENNReal.ofReal (max (b - 1) 0) ≤ q := by
  have hright : ENNReal.ofReal a * q + ENNReal.ofReal a ≠ ∞ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq, ENNReal.ofReal_ne_top⟩
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hright).mpr h
  simp only [ENNReal.toReal_ofReal (mul_nonneg ha.le hb),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq)
      ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le] at hreal
  have hle : b - 1 ≤ q.toReal := by
    nlinarith
  exact (ENNReal.ofReal_le_iff_le_toReal hq).mpr
    (max_le hle ENNReal.toReal_nonneg)

theorem compactAnchorSquareMass_scaled_lintegral
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℝ) (hL : 0 < L) :
    (∫⁻ x, ENNReal.ofReal ((χ (L⁻¹ • x)) ^ 2) ∂volume) =
      ENNReal.ofReal (L ^ d) * ENNReal.ofReal (compactAnchorSquareMass d χ) := by
  have h := nonnegativeWindowOverlap_comp_inv_smul d
    (fun x => ENNReal.ofReal (χ x)) χ.continuous.measurable.ennreal_ofReal L hL 0
  rw [nonnegativeWindowOverlap_ofReal d χ hχ] at h
  simpa only [nonnegativeWindowOverlap, compactAnchorSquareMass, smul_zero, add_zero,
    ← ENNReal.ofReal_mul (hχ _), ← pow_two] using h

theorem compactAnchorSquareMass_normalized_diagonal
    (d : ℕ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (L : ℝ) (hL : 0 < L) :
    (ENNReal.ofReal (L ^ d))⁻¹ *
        (∫⁻ x, ENNReal.ofReal ((χ (L⁻¹ • x)) ^ 2) ∂volume) =
      ENNReal.ofReal (compactAnchorSquareMass d χ) := by
  rw [compactAnchorSquareMass_scaled_lintegral d χ hχ L hL, ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (pow_pos hL d)).ne'
      ENNReal.ofReal_ne_top, one_mul]
theorem gaussian_covariance_lower_bound_of_admissible
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (u : ℝ) (hu : 0 < u) :
    ENNReal.ofReal (max (B d u - 1) 0) ≤ Q d P u := by
  by_cases hQ : Q d P u = ∞
  · simp only [hQ, le_top]
  obtain ⟨χ, hχ, hχnorm⟩ := exists_nonneg_normalized_compact_anchor d
  let a : ℝ := compactAnchorSquareMass d χ
  have ha : 0 < a := compactAnchorSquareMass_pos_of_integral_one d χ hχnorm
  let L : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hL : ∀ n, 0 < L n := fun n => add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hLtop : Tendsto L atTop atTop := by
    simpa only [L, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hLinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hLtop
  let Γ : Measure (Rd d × Rd d) := originalAdmissibleFactorialMeasure d P hP
  let Δ : Measure (Rd d × Rd d) := (volume : Measure (Rd d)).prod volume
  letI : SFinite Γ := inferInstance
  have hΓ (v : Rd d) :
      Γ.map (fun p : Rd d × Rd d => (v + p.1, v + p.2)) = Γ :=
    originalAdmissibleFactorialMeasure_map_diagAdd_eq_self d P hP v
  have hΔ (v : Rd d) :
      Δ.map (fun p : Rd d × Rd d => (v + p.1, v + p.2)) = Δ :=
    map_add_left_eq_self Δ (v, v)
  have hΓmass : (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) = Q d P u :=
    (Q_eq_originalAdmissibleFactorialMeasure d P hP u).symm
  have hΓfin : (∫⁻ p, anchoredGaussianKernel d u p ∂Γ) ≠ ∞ := hΓmass.trans_ne hQ
  have hΔmass : (∫⁻ p, anchoredGaussianKernel d u p ∂Δ) = ENNReal.ofReal (B d u) :=
    anchoredGaussian_background_lintegral d u hu
  have hΔfin : (∫⁻ p, anchoredGaussianKernel d u p ∂Δ) ≠ ∞ :=
    hΔmass.trans_ne ENNReal.ofReal_ne_top
  let G : ℕ → Measure (Rd d × Rd d) → ℝ≥0∞ := fun n M =>
    (ENNReal.ofReal ((L n) ^ d))⁻¹ *
      (∫⁻ p, ENNReal.ofReal (χ ((L n)⁻¹ • p.1)) *
        ENNReal.ofReal (χ ((L n)⁻¹ • p.2)) *
        ENNReal.ofReal (Real.exp (-(u * ‖p.2 - p.1‖ ^ (2 : ℕ)))) ∂M)
  have hGΓ : Tendsto (fun n => G n Γ) atTop
      (𝓝 (ENNReal.ofReal a * Q d P u)) := by
    simpa only [G, a, hΓmass] using
      stationary_compactGaussianWindow_normalized_tendsto
        d Γ hΓ u hΓfin χ hχ hχnorm L hL hLinv
  have hGΔ : Tendsto (fun n => G n Δ) atTop
      (𝓝 (ENNReal.ofReal a * ENNReal.ofReal (B d u))) := by
    simpa only [G, a, hΔmass] using
      stationary_compactGaussianWindow_normalized_tendsto
        d Δ hΔ u hΔfin χ hχ hχnorm L hL hLinv
  have hGle (n : ℕ) : G n Δ ≤ G n Γ + ENNReal.ofReal a := by
    let φ : C_c(Rd d, ℝ) :=
      ⟨⟨fun x => χ ((L n)⁻¹ • x),
        χ.continuous.comp (continuous_const_smul _)⟩,
        χ.hasCompactSupport.comp_smul (inv_ne_zero (hL n).ne')⟩
    have hφ : ∀ x, 0 ≤ φ x := fun x => hχ _
    have hcompact := compactGaussian_background_le_factorial_add_diagonal_of_admissible
      d P hP φ hφ u hu
    have hscaled := mul_le_mul_right hcompact (ENNReal.ofReal ((L n) ^ d))⁻¹
    rw [mul_add] at hscaled
    have hdiag : (ENNReal.ofReal ((L n) ^ d))⁻¹ *
        (∫⁻ x, ENNReal.ofReal ((φ x) ^ 2) ∂volume) = ENNReal.ofReal a :=
      compactAnchorSquareMass_normalized_diagonal d χ hχ (L n) (hL n)
    rw [hdiag] at hscaled
    simpa only [G, Γ, Δ, compactGaussianWindowKernel, φ,
      CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, neg_mul] using hscaled
  have hlimit : ENNReal.ofReal a * ENNReal.ofReal (B d u) ≤
      ENNReal.ofReal a * Q d P u + ENNReal.ofReal a :=
    le_of_tendsto_of_tendsto hGΔ (hGΓ.add tendsto_const_nhds)
      (Filter.Eventually.of_forall hGle)
  rw [← ENNReal.ofReal_mul ha.le] at hlimit
  exact gaussian_covariance_bound_of_scaled_limit_ineq a (B d u) ha
    (Real.rpow_nonneg (div_nonneg Real.pi_pos.le hu.le) _) (Q d P u) hQ hlimit

theorem antitone_Q (d : ℕ) (P : ConfigurationLaw d) : Antitone (Q d P) := by
  intro u v huv
  unfold Q
  refine lintegral_mono (fun μ => lintegral_mono (fun x => lintegral_mono (fun y => ?_)))
  by_cases hxy : x = y
  · simp only [if_pos hxy, le_refl]
  simp only [if_neg hxy]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg huv) (sq_nonneg ‖y - x‖)))

theorem weighted_gaussianRemainder_lintegral_ne_top_of_W_ne_top_pos
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hW : W d s P ≠ ⊤) :
    (∫⁻ u in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (u ^ (s / 2 - 1)) * gaussianRemainder d P u) ≠ ∞ := by
  intro hI
  have hγ : ENNReal.ofReal (gamma_s s) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr
      (Riesz.Analysis.gamma_s_pos s (lt_trans (by norm_num : (-2 : ℝ) < 0) hs))
  apply hW
  unfold W
  rw [hI, ENNReal.mul_top hγ, EReal.coe_ennreal_top]
  exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)

theorem Q_ne_top_of_W_ne_top_pos
    (d : ℕ) (s : ℝ) (hs : 0 < s) (P : ConfigurationLaw d)
    (hW : W d s P ≠ ⊤) (u : ℝ) (hu : 0 < u) : Q d P u ≠ ∞ := by
  intro hQu
  have hI := weighted_gaussianRemainder_lintegral_ne_top_of_W_ne_top_pos d s hs P hW
  have hpoint (v : ℝ) (hv : v ∈ Set.Ioo (u / 2) u) :
      ENNReal.ofReal (v ^ (s / 2 - 1)) * gaussianRemainder d P v = ∞ := by
    have hvpos : 0 < v := lt_trans (half_pos hu) hv.1
    have hQv : Q d P v = ∞ :=
      top_unique (hQu ▸ (antitone_Q d P hv.2.le))
    have hw : ENNReal.ofReal (v ^ (s / 2 - 1)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hvpos _)
    rw [gaussianRemainder, hQv, ENNReal.top_sub ENNReal.ofReal_ne_top,
      ENNReal.mul_top hw]
  have hinterval : (volume : Measure ℝ) (Set.Ioo (u / 2) u) ≠ 0 :=
    Real.volume_Ioo.trans_ne (ENNReal.ofReal_ne_zero_iff.mpr
      (sub_pos.mpr (half_lt_self hu)))
  have hle : (∞ : ℝ≥0∞) ≤
      ∫⁻ v in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (v ^ (s / 2 - 1)) * gaussianRemainder d P v :=
    calc
      (∞ : ℝ≥0∞) = ∫⁻ _v in Set.Ioo (u / 2) u, (∞ : ℝ≥0∞) :=
        ((setLIntegral_const (Set.Ioo (u / 2) u) ∞).trans
          (ENNReal.top_mul hinterval)).symm
      _ = ∫⁻ v in Set.Ioo (u / 2) u,
          ENNReal.ofReal (v ^ (s / 2 - 1)) * gaussianRemainder d P v :=
        setLIntegral_congr_fun measurableSet_Ioo (fun v hv => (hpoint v hv).symm)
      _ ≤ _ := lintegral_mono_set (fun v hv => lt_trans (half_pos hu) hv.1)
  exact hI (top_unique hle)

end Riesz.Stationary

