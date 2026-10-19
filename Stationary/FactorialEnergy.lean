import Riesz.Stationary.NegativeDisplacement

/-!
Multiplicity-aware factorial energy and the negative spherical Fatou bound.

The canonical factorial profile and energy use the original expected factorial
measure and Showcase normalization. Agreement with the original Q and W is
proved for almost-everywhere simple input laws. Gaussian-anchor identities use
stationarity and local second moments; finite factorial energy supplies the
finite nonnegative envelope before real integration.

For negative exponents, the actual spherical weak-limit endpoint derives its
moment, profile and Fatou bounds from bounded spherical energy, retaining
coincident unequal labels without assuming simplicity of the limiting law.
-/

noncomputable section
open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry Riesz.Stationary
open scoped ENNReal Topology Classical CompactlySupported
namespace Riesz.Stationary

/-- Multiplicity-aware factorial Gaussian profile; no coordinate diagonal is removed. -/
def factorialQ (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, anchoredGaussianKernel d u p ∂expectedFactorialMeasure d P hsecond

/-- The original nonnegative truncation applied to the factorial profile. -/
def factorialGaussianRemainder (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (u : ℝ) : ℝ≥0∞ :=
  factorialQ d P hsecond u - ENNReal.ofReal (max (B d u - 1) 0)

/-- Internal factorial energy, retaining the exact Showcase normalization. -/
def factorialW (d : ℕ) (s : ℝ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞) : EReal :=
  (c0 d s : EReal) +
    ((ENNReal.ofReal (gamma_s s) *
      ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) *
        factorialGaussianRemainder d P hsecond u) : ℝ≥0∞)

theorem factorialQ_eq_Q_of_ae_simple
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val) (u : ℝ) :
    factorialQ d P hsecond u = Q d (P.map Subtype.val) u := by
  exact (Q_map_val_eq_expectedFactorialMeasure d P hsecond hsimple u).symm

theorem factorialGaussianRemainder_eq_gaussianRemainder_of_ae_simple
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val) (u : ℝ) :
    factorialGaussianRemainder d P hsecond u =
      gaussianRemainder d (P.map Subtype.val) u := by
  unfold factorialGaussianRemainder gaussianRemainder
  rw [factorialQ_eq_Q_of_ae_simple d P hsecond hsimple u]

theorem factorialW_eq_W_of_ae_simple
    (d : ℕ) (s : ℝ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val) :
    factorialW d s P hsecond = W d s (P.map Subtype.val) := by
  unfold factorialW W
  simp_rw [factorialGaussianRemainder_eq_gaussianRemainder_of_ae_simple
    d P hsecond hsimple]

private theorem antitone_factorialQ
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞) :
    Antitone (factorialQ d P hsecond) := by
  intro u v huv
  unfold factorialQ
  refine lintegral_mono (fun p => ?_)
  by_cases hp : p.1 ∈ cube d 1
  · simp only [anchoredGaussianKernel, if_pos hp]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_right huv (sq_nonneg ‖p.2 - p.1‖))))
  · simp only [anchoredGaussianKernel, if_neg hp, le_refl]

theorem weighted_factorialGaussianRemainder_lintegral_ne_top_of_factorialW_ne_top
    (d : ℕ) (s : ℝ) (hs_lower : -2 < s)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hW : factorialW d s P hsecond ≠ ⊤) :
    (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) *
      factorialGaussianRemainder d P hsecond u) ≠ ∞ := by
  intro hI
  have hγ : ENNReal.ofReal (gamma_s s) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Riesz.Analysis.gamma_s_pos s hs_lower)
  apply hW
  unfold factorialW
  rw [hI, ENNReal.mul_top hγ, EReal.coe_ennreal_top]
  exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)

theorem factorialQ_ne_top_of_factorialW_ne_top
    (d : ℕ) (s : ℝ) (hs_lower : -2 < s)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hW : factorialW d s P hsecond ≠ ⊤) (u : ℝ) (hu : 0 < u) :
    factorialQ d P hsecond u ≠ ∞ := by
  intro hQu
  have hI := weighted_factorialGaussianRemainder_lintegral_ne_top_of_factorialW_ne_top
    d s hs_lower P hsecond hW
  have hpoint (v : ℝ) (hv : v ∈ Set.Ioo (u / 2) u) :
      ENNReal.ofReal (v ^ (s / 2 - 1)) * factorialGaussianRemainder d P hsecond v = ∞ := by
    have hvpos : 0 < v := lt_trans (half_pos hu) hv.1
    have hQv : factorialQ d P hsecond v = ∞ :=
      top_unique (hQu ▸ (antitone_factorialQ d P hsecond hv.2.le))
    have hw : ENNReal.ofReal (v ^ (s / 2 - 1)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hvpos _)
    rw [factorialGaussianRemainder, hQv, ENNReal.top_sub ENNReal.ofReal_ne_top,
      ENNReal.mul_top hw]
  have hinterval : (volume : Measure ℝ) (Set.Ioo (u / 2) u) ≠ 0 :=
    Real.volume_Ioo.trans_ne (ENNReal.ofReal_ne_zero_iff.mpr
      (sub_pos.mpr (half_lt_self hu)))
  have hle : (∞ : ℝ≥0∞) ≤
      ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (v ^ (s / 2 - 1)) *
        factorialGaussianRemainder d P hsecond v := by
    calc
      (∞ : ℝ≥0∞) = ∫⁻ _v in Set.Ioo (u / 2) u, (∞ : ℝ≥0∞) :=
        ((setLIntegral_const (Set.Ioo (u / 2) u) ∞).trans
          (ENNReal.top_mul hinterval)).symm
      _ = ∫⁻ v in Set.Ioo (u / 2) u, ENNReal.ofReal (v ^ (s / 2 - 1)) *
          factorialGaussianRemainder d P hsecond v :=
        setLIntegral_congr_fun measurableSet_Ioo (fun v hv => (hpoint v hv).symm)
      _ ≤ _ := lintegral_mono_set (fun v hv => lt_trans (half_pos hu) hv.1)
  exact hI (top_unique hle)

private theorem gaussianAnchorMeasure_unitCube_eq_factorialQ
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (u : ℝ) :
    gaussianAnchorMeasure d (expectedFactorialMeasure d P hsecond) u (cube d 1) =
      factorialQ d P hsecond u := by
  have hK := Riesz.Negative.measurableSet_cube d 1
  rw [gaussianAnchorMeasure, Measure.map_apply measurable_fst hK,
    withDensity_apply _ (hK.preimage measurable_fst), factorialQ,
    ← lintegral_indicator (hK.preimage measurable_fst)]
  apply lintegral_congr
  intro p
  by_cases hp : p.1 ∈ cube d 1
  all_goals simp [Set.indicator, anchoredGaussianKernel, gaussianDifferenceWeight, hp]

/-- The actual extended Gaussian identity for every nonnegative compact first anchor. -/
theorem factorialGaussian_compactAnchor_lintegral
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hstationary : IsStationary d (P.map Subtype.val))
    (u : ℝ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) :
    (∫⁻ p, ENNReal.ofReal (χ p.1) * gaussianDifferenceWeight d u p
      ∂expectedFactorialMeasure d P hsecond) =
        factorialQ d P hsecond u * ENNReal.ofReal (∫ x, χ x ∂volume) := by
  let Γ : Measure (Rd d × Rd d) := expectedFactorialMeasure d P hsecond
  let A : Measure (Rd d) := gaussianAnchorMeasure d Γ u
  letI : SFinite Γ := inferInstance
  letI : SFinite A := inferInstanceAs (SFinite
    ((Γ.withDensity (gaussianDifferenceWeight d u)).map Prod.fst))
  have hΓ : ∀ a : Rd d, Γ.map
      (fun p : Rd d × Rd d => (a + p.1, a + p.2)) = Γ :=
    expectedFactorialMeasure_stationary_allCounting d P hsecond hstationary
  letI : A.IsAddLeftInvariant := gaussianAnchorMeasure_isAddLeftInvariant d Γ u hΓ
  have hχmeas : Measurable (fun x : Rd d => ENNReal.ofReal (χ x)) :=
    χ.continuous.measurable.ennreal_ofReal
  have hχintegral : (∫⁻ x, ENNReal.ofReal (χ x) ∂volume) =
      ENNReal.ofReal (∫ x, χ x ∂volume) :=
    (ofReal_integral_eq_lintegral_ofReal χ.integrable
      (Filter.Eventually.of_forall hχ)).symm
  calc
    _ = ∫⁻ x, ENNReal.ofReal (χ x) ∂A :=
      (lintegral_gaussianAnchorMeasure d Γ u _ hχmeas).symm
    _ = A (cube d 1) * (∫⁻ x, ENNReal.ofReal (χ x) ∂volume) :=
      lintegral_eq_unitCube_mul_lintegral_of_addLeftInvariant d A _ hχmeas
    _ = _ := by rw [hχintegral, gaussianAnchorMeasure_unitCube_eq_factorialQ d P hsecond u]

/-- Finite internal energy supplies a finite NN Gaussian envelope, before any toReal. -/
theorem factorialGaussian_compactAnchor_lintegral_lt_top
    (d : ℕ) (s : ℝ) (hs_lower : -2 < s)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hstationary : IsStationary d (P.map Subtype.val))
    (hW : factorialW d s P hsecond ≠ ⊤)
    (u : ℝ) (hu : 0 < u) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) :
    (∫⁻ p, ENNReal.ofReal (χ p.1) * gaussianDifferenceWeight d u p
      ∂expectedFactorialMeasure d P hsecond) < ∞ := by
  rw [factorialGaussian_compactAnchor_lintegral d P hsecond hstationary u χ hχ]
  exact ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (factorialQ_ne_top_of_factorialW_ne_top
      d s hs_lower P hsecond hW u hu)) ENNReal.ofReal_lt_top

/-- The real Gaussian profile is integrable and agrees with the finite NN profile. -/
theorem factorialGaussian_compactAnchor_integrable_and_integral
    (d : ℕ) (s : ℝ) (hs_lower : -2 < s)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hstationary : IsStationary d (P.map Subtype.val))
    (hW : factorialW d s P hsecond ≠ ⊤)
    (u : ℝ) (hu : 0 < u) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) :
    Integrable (fun p : Rd d × Rd d =>
      χ p.1 * Real.exp (-(u * ‖p.2 - p.1‖ ^ 2)))
        (expectedFactorialMeasure d P hsecond) ∧
      (∫ p : Rd d × Rd d, χ p.1 * Real.exp (-(u * ‖p.2 - p.1‖ ^ 2))
        ∂expectedFactorialMeasure d P hsecond) =
          (factorialQ d P hsecond u).toReal * (∫ x, χ x ∂volume) := by
  let Γ : Measure (Rd d × Rd d) := expectedFactorialMeasure d P hsecond
  let g : Rd d × Rd d → ℝ := fun p =>
    χ p.1 * Real.exp (-(u * ‖p.2 - p.1‖ ^ 2))
  have hg : Continuous g := (χ.continuous.comp continuous_fst).mul
    (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_snd.sub continuous_fst).norm.pow 2)).neg)
  have hgnonneg : ∀ p, 0 ≤ g p := fun p =>
    mul_nonneg (hχ p.1) (Real.exp_pos _).le
  have hNNeq : (∫⁻ p, ENNReal.ofReal (g p) ∂Γ) =
      ∫⁻ p, ENNReal.ofReal (χ p.1) * gaussianDifferenceWeight d u p ∂Γ :=
    lintegral_congr (fun p => ENNReal.ofReal_mul (hχ p.1))
  have hfinite : (∫⁻ p, ENNReal.ofReal (g p) ∂Γ) < ∞ := by
    rw [hNNeq]
    exact factorialGaussian_compactAnchor_lintegral_lt_top
      d s hs_lower P hsecond hstationary hW u hu χ hχ
  have hgi : Integrable g Γ :=
    ⟨hg.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hgnonneg)).2 hfinite⟩
  refine ⟨hgi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hgnonneg)
      hgi.aestronglyMeasurable, hNNeq,
    factorialGaussian_compactAnchor_lintegral d P hsecond hstationary u χ hχ,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg hχ)]

end Riesz.Stationary

namespace Riesz.Asymptotics

private theorem factorialQ_le_of_compactSecondAnchor_gaussian_bound
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hstationary : IsStationary d (P.map Subtype.val))
    (u : ℝ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (hχmass : (∫ x, χ x ∂volume) = 1) (C : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ p, ENNReal.ofReal
        (compactGaussianFactorialTest d (gaussianCompactSecondAnchor d χ n) u p)
        ∂expectedFactorialMeasure d P hsecond) ≤ C) :
    factorialQ d P hsecond u ≤ C := by
  have hanchor :
      (∫⁻ p, ENNReal.ofReal (χ p.1) * gaussianDifferenceWeight d u p
        ∂expectedFactorialMeasure d P hsecond) = factorialQ d P hsecond u := by
    simpa only [hχmass, ENNReal.ofReal_one, mul_one] using
      factorialGaussian_compactAnchor_lintegral d P hsecond hstationary u χ hχ
  refine hanchor.symm.trans_le
    (gaussian_anchor_lintegral_le_of_compactSecondAnchor_bound
      d (expectedFactorialMeasure d P hsecond) χ u C ?_)
  intro n
  have hident (p : Rd d × Rd d) :
      ENNReal.ofReal (gaussianCompactSecondAnchor d χ n p) * gaussianDifferenceWeight d u p =
        ENNReal.ofReal
          (compactGaussianFactorialTest d (gaussianCompactSecondAnchor d χ n) u p) := by
    change ENNReal.ofReal (gaussianCompactSecondAnchor d χ n p) *
        ENNReal.ofReal (Real.exp (-(u * ‖p.2 - p.1‖ ^ (2 : ℕ)))) =
      ENNReal.ofReal (gaussianCompactSecondAnchor d χ n p *
        Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ)))
    simpa only [neg_mul] using
      (ENNReal.ofReal_mul (gaussianCompactSecondAnchor_bounds d χ hχ n p).1).symm
  exact (lintegral_congr hident).trans_le (hbound n)

private theorem factorialQ_actual_spherical_limit_le_profile_liminf
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto (fun n => sphereLocalCountingProbability d (N n)
      (sphericalRadius d (N n)) (x n)) atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(sphereLocalCountingProbability d (N n)
          (sphericalRadius d (N n)) (x n)).toMeasure) ≤ C)
    (hsecondQ : ∀ m : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (m : ℝ))) ^ 2 ∂Q.toMeasure) < ∞)
    (u : ℝ) :
    factorialQ d Q.toMeasure hsecondQ u ≤
      atTop.liminf (fun n => ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n) u)) := by
  obtain ⟨χ, hχ, hχmass⟩ := exists_nonneg_normalized_compact_anchor d
  apply factorialQ_le_of_compactSecondAnchor_gaussian_bound
    d Q.toMeasure hsecondQ
    (sphereLocalCountingProbability_limit_stationary d hd N hN x Q hQ) u χ hχ hχmass
  exact fun k => compactGaussianFactorial_limit_le_sphericalProfile_liminf
    d hd N hN x Q hQ hball hsecondQ (gaussianCompactSecondAnchor d χ k)
    (fun p => (gaussianCompactSecondAnchor_bounds d χ hχ k p).1)
    χ hχ hχmass (fun p => (gaussianCompactSecondAnchor_bounds d χ hχ k p).2) u

private theorem factorialGaussianRemainder_le_liminf_sphericalRemainder
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (u : ℝ) (hu : 0 < u)
    (hsharp : factorialQ d P hsecond u ≤ atTop.liminf (fun n : ℕ =>
      ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u))) :
    factorialGaussianRemainder d P hsecond u ≤ atTop.liminf (fun n : ℕ =>
      ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)) := by
  let b : ℝ≥0∞ := ENNReal.ofReal (max (B d u - 1) 0)
  have hcomparison : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u) - b ≤
        ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u) := by
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    have hbg : max (sphericalGaussianBackground d (N n) u - 1) 0 ≤ max (B d u - 1) 0 :=
      max_le_max (sub_le_sub_right
        (sphericalGaussianBackground_le d (N n) hd hn u hu) 1) le_rfl
    exact (tsub_le_tsub_left (ENNReal.ofReal_le_ofReal hbg) _).trans_eq
      (ENNReal.ofReal_sub _ (le_max_right _ _)).symm
  calc
    factorialGaussianRemainder d P hsecond u = factorialQ d P hsecond u - b := rfl
    _ ≤ (atTop.liminf (fun n : ℕ =>
        ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u))) - b :=
      tsub_le_tsub_right hsharp b
    _ = atTop.liminf (fun n : ℕ =>
        ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u) - b) :=
      (ENNReal.liminf_sub_const atTop _ b).symm
    _ ≤ atTop.liminf (fun n : ℕ =>
        ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)) :=
      Filter.liminf_le_liminf hcomparison

private theorem negative_factorialW_le_liminf_of_profile_bound
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs_lower : -2 < s) (hs_neg : s < 0)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsharp : ∀ u : ℝ, 0 < u → factorialQ d P hsecond u ≤ atTop.liminf (fun n : ℕ =>
      ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u))) :
    factorialW d s P hsecond ≤ atTop.liminf (fun n : ℕ =>
      (scaledSphericalKernelEnergy d (N n) s (x n) : EReal)) := by
  have hsd : s < (d : ℝ) := hs_neg.trans_le (Nat.cast_nonneg d)
  let g : ℝ≥0∞ := ENNReal.ofReal (gamma_s s)
  let w : ℝ → ℝ≥0∞ := fun u => g * ENNReal.ofReal (u ^ (s / 2 - 1))
  let A : ℕ → ℝ≥0∞ := fun n => g * ∫⁻ u in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (u ^ (s / 2 - 1)) *
      ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)
  let I : ℝ≥0∞ := g * ∫⁻ u in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (u ^ (s / 2 - 1)) * factorialGaussianRemainder d P hsecond u
  have hw : Measurable w :=
    measurable_const.mul (measurable_id.pow_const (s / 2 - 1)).ennreal_ofReal
  have hmeas (n : ℕ) : Measurable (fun u : ℝ => w u *
      ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)) :=
    hw.mul (((measurable_sphericalGaussianPairProfile d (N n) (x n).val).sub
      (((measurable_sphericalGaussianBackground d (N n) hd).sub
        measurable_const).max measurable_const)).ennreal_ofReal)
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) :
      w u * factorialGaussianRemainder d P hsecond u ≤ atTop.liminf (fun n : ℕ =>
        w u * ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)) := by
    have hmul : w u * atTop.liminf (fun n : ℕ =>
        ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)) ≤
        atTop.liminf (fun n : ℕ => w u *
          ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)) := by
      simpa only [Pi.mul_def, Filter.liminf_const] using
        (ENNReal.le_liminf_mul (u := fun _n : ℕ => w u)
          (v := fun n : ℕ => ENNReal.ofReal
            (sphericalGaussianRemainder d (N n) (x n).val u)) (f := atTop))
    exact (mul_le_mul_right
      (factorialGaussianRemainder_le_liminf_sphericalRemainder
        d hd N hN x P hsecond u hu (hsharp u hu)) (w u)).trans hmul
  have hFatouRaw :
      (∫⁻ u in Set.Ioi (0 : ℝ), w u * factorialGaussianRemainder d P hsecond u) ≤
        atTop.liminf (fun n : ℕ => ∫⁻ u in Set.Ioi (0 : ℝ), w u *
          ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)) :=
    (setLIntegral_mono' measurableSet_Ioi hpoint).trans (lintegral_liminf_le hmeas)
  have hIntegral (f : ℝ → ℝ≥0∞) :
      (∫⁻ u in Set.Ioi (0 : ℝ), w u * f u) =
        g * ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (s / 2 - 1)) * f u := by
    simp only [w, mul_assoc]
    exact lintegral_const_mul' g _ ENNReal.ofReal_ne_top
  have hFatou : I ≤ atTop.liminf A := by
    simpa only [hIntegral, I, A] using hFatouRaw
  have hcoe : ((atTop.liminf A : ℝ≥0∞) : EReal) =
      atTop.liminf (fun n : ℕ => (A n : EReal)) := by
    simpa only [Function.comp_def] using
      (EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt
        (F := (atTop : Filter ℕ)) A continuous_coe_ennreal_ereal.continuousAt)
  have hFatouE : (I : EReal) ≤ atTop.liminf (fun n : ℕ => (A n : EReal)) :=
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hFatou).trans_eq hcoe
  have hc : atTop.liminf
      (fun n : ℕ => (sphericalReferenceConstant d (N n) s : EReal)) = (c0 d s : EReal) :=
    (EReal.tendsto_coe.mpr
      ((tendsto_sphericalReferenceConstant d hd s hsd hs_neg.ne).comp hN)).liminf_eq
  have hidentity : ∀ᶠ n : ℕ in atTop,
      (scaledSphericalKernelEnergy d (N n) s (x n) : EReal) =
        (sphericalReferenceConstant d (N n) s : EReal) + (A n : EReal) :=
    (hN.eventually
      (eventually_spherical_remainder_lintegral_identity d hd s hs_lower hsd hs_neg.ne)).mono
      (fun n hn => hn (x n))
  have hadd : atTop.liminf
        (fun n : ℕ => (sphericalReferenceConstant d (N n) s : EReal)) +
        atTop.liminf (fun n : ℕ => (A n : EReal)) ≤
      atTop.liminf (fun n : ℕ =>
        (sphericalReferenceConstant d (N n) s : EReal) + (A n : EReal)) :=
    EReal.le_liminf_add
      (u := fun n : ℕ => (sphericalReferenceConstant d (N n) s : EReal))
      (v := fun n : ℕ => (A n : EReal)) (f := atTop)
  calc
    factorialW d s P hsecond = (c0 d s : EReal) + (I : EReal) := rfl
    _ ≤ atTop.liminf (fun n : ℕ => (sphericalReferenceConstant d (N n) s : EReal)) +
        atTop.liminf (fun n : ℕ => (A n : EReal)) :=
      add_le_add (le_of_eq hc.symm) hFatouE
    _ ≤ atTop.liminf (fun n : ℕ =>
        (sphericalReferenceConstant d (N n) s : EReal) + (A n : EReal)) := hadd
    _ = atTop.liminf (fun n : ℕ => (scaledSphericalKernelEnergy d (N n) s (x n) : EReal)) :=
      Filter.liminf_congr (Filter.EventuallyEq.symm hidentity)

/-- Actual nonsimple negative weak limits have finite factorial energy and its sharp Fatou bound. -/
theorem sphereLocalCountingProbability_limit_factorialW_le_liminf_of_negative_energy_bound
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs_lower : -2 < s) (hs_neg : s < 0)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (henergy : ∃ L : ℝ, ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N n) s (x n) ≤ L)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto (fun n => sphereLocalCountingProbability d (N n)
      (sphericalRadius d (N n)) (x n).val) atTop (𝓝 Q)) :
    ∃ hsecondQ : (∀ m : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (m : ℝ))) ^ 2 ∂Q.toMeasure) < ∞),
      factorialW d s Q.toMeasure hsecondQ ≤ atTop.liminf (fun n : ℕ =>
        (scaledSphericalKernelEnergy d (N n) s (x n) : EReal)) ∧
      factorialW d s Q.toMeasure hsecondQ ≠ ⊤ := by
  have hsd : s < (d : ℝ) := hs_neg.trans_le (Nat.cast_nonneg d)
  have hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(sphereLocalCountingProbability d (N n)
          (sphericalRadius d (N n)) (x n).val).toMeasure) ≤ C :=
    fun T hT => exists_sphereLocalCountingProbability_ball_second_moment_bound_of_energy_bound
      d hd s hs_lower hsd hs_neg.ne N hN x henergy T hT
  have hsecondQ : ∀ m : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (m : ℝ))) ^ 2 ∂Q.toMeasure) < ∞ :=
    fun m => countingLaw_limit_local_second_moments d _ Q hQ hball
      (Metric.closedBall (0 : Rd d) (m : ℝ)) measurableSet_closedBall
      (isCompact_closedBall (0 : Rd d) (m : ℝ)).isBounded
  have hbound : factorialW d s Q.toMeasure hsecondQ ≤ atTop.liminf (fun n : ℕ =>
      (scaledSphericalKernelEnergy d (N n) s (x n) : EReal)) :=
    negative_factorialW_le_liminf_of_profile_bound
      d hd s hs_lower hs_neg N hN x Q.toMeasure hsecondQ (fun u _hu =>
        factorialQ_actual_spherical_limit_le_profile_liminf
          d hd N hN (fun n => (x n).val) Q hQ hball hsecondQ u)
  refine ⟨hsecondQ, hbound, ?_⟩
  obtain ⟨L, hL⟩ := henergy
  have hlim : atTop.liminf (fun n : ℕ =>
      (scaledSphericalKernelEnergy d (N n) s (x n) : EReal)) ≤ (L : EReal) :=
    Filter.liminf_le_of_frequently_le'
      (hL.mono (fun n hn => EReal.coe_le_coe_iff.mpr hn)).frequently
  intro htop
  exact not_le_of_gt (EReal.coe_lt_top L) (htop ▸ hbound.trans hlim)

end Riesz.Asymptotics
