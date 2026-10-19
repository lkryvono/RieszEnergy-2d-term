import Riesz.Asymptotics.SphericalAdmissible
import Riesz.Configuration.ExpectedOffDiagonal
import Riesz.Configuration.Translations
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Sharp Gaussian comparison for spherical weak limits

Stationarity identifies normalized compact first-point anchors with the exact
unit-cube profile in the Showcase. Weighted Haar averaging then preserves the
coefficient needed for the sharp lower energy comparison.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Geometry
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Stationary

/-- An extended invariant measure is normalized by its mass on the unit cube. -/
theorem lintegral_eq_unitCube_mul_lintegral_of_addLeftInvariant
    (d : ℕ) (A : Measure (Rd d)) [SFinite A] [A.IsAddLeftInvariant]
    (χ : Rd d → ℝ≥0∞) (hχ : Measurable χ) :
    (∫⁻ x, χ x ∂A) = A (cube d 1) * (∫⁻ x, χ x ∂volume) := by
  let b : Rd d → ℝ≥0∞ := (cube d 1).indicator (fun _ => 1)
  have hK : MeasurableSet (cube d 1) := Riesz.Negative.measurableSet_cube d 1
  have hb : Measurable b := measurable_const.indicator hK
  have hbA : (∫⁻ x, b x ∂A) = A (cube d 1) := lintegral_indicator_one hK
  have hbvolume : (∫⁻ x, b x ∂volume) = 1 :=
    (lintegral_indicator_one hK).trans ((Riesz.Negative.volume_cube d 1).trans
      ((congrArg (fun a : ℝ≥0∞ => a ^ d) ENNReal.ofReal_one).trans (one_pow d)))
  have hshift (f : Rd d → ℝ≥0∞) (a : Rd d) :
      (∫⁻ x, f (x - a) ∂A) = ∫⁻ x, f x ∂A := by
    simpa only [sub_eq_add_neg, add_comm] using
      (lintegral_add_left_eq_self (μ := A) f (-a))
  have htwist (x : Rd d) :
      (∫⁻ a, b a * χ (x - a) ∂volume) =
        ∫⁻ z, χ z * b (x - z) ∂volume := by
    simpa only [sub_sub_self, mul_comm] using
      (lintegral_sub_left_eq_self (μ := (volume : Measure (Rd d)))
        (fun z : Rd d => χ z * b (x - z)) x)
  have hkernel₁ : Measurable (fun p : Rd d × Rd d => b p.1 * χ (p.2 - p.1)) :=
    (hb.comp measurable_fst).mul (hχ.comp (measurable_snd.sub measurable_fst))
  have hkernel₂ : Measurable (fun p : Rd d × Rd d => χ p.2 * b (p.1 - p.2)) :=
    (hχ.comp measurable_snd).mul (hb.comp (measurable_fst.sub measurable_snd))
  calc
    (∫⁻ x, χ x ∂A) = ∫⁻ a, b a * (∫⁻ x, χ (x - a) ∂A) ∂volume :=
      ((lintegral_mul_const (∫⁻ x, χ x ∂A) hb).trans
        ((congrArg (fun r => r * (∫⁻ x, χ x ∂A)) hbvolume).trans (one_mul _))).symm.trans
          (lintegral_congr (fun a => congrArg (fun r => b a * r) (hshift χ a).symm))
    _ = ∫⁻ a, ∫⁻ x, b a * χ (x - a) ∂A ∂volume :=
      lintegral_congr (fun a => (lintegral_const_mul (μ := A) (b a)
        (hχ.comp (measurable_id.sub measurable_const))).symm)
    _ = ∫⁻ x, ∫⁻ a, b a * χ (x - a) ∂volume ∂A :=
      lintegral_lintegral_swap (μ := (volume : Measure (Rd d))) (ν := A)
        hkernel₁.aemeasurable
    _ = ∫⁻ x, ∫⁻ z, χ z * b (x - z) ∂volume ∂A := lintegral_congr htwist
    _ = ∫⁻ z, ∫⁻ x, χ z * b (x - z) ∂A ∂volume :=
      lintegral_lintegral_swap (μ := A) (ν := (volume : Measure (Rd d)))
        hkernel₂.aemeasurable
    _ = ∫⁻ z, χ z * A (cube d 1) ∂volume :=
      lintegral_congr (fun z => (lintegral_const_mul (χ z)
        (hb.comp (measurable_id.sub measurable_const))).trans
          (congrArg (fun r => χ z * r) ((hshift b z).trans hbA)))
    _ = A (cube d 1) * (∫⁻ z, χ z ∂volume) :=
      (lintegral_mul_const (A (cube d 1)) hχ).trans (mul_comm _ _)

end Riesz.Stationary

namespace Riesz.Configuration

theorem map_countingConfiguration_val_injective (d : ℕ) :
    Function.Injective (fun P : Measure (CountingConfiguration d) =>
      P.map (Subtype.val : CountingConfiguration d → Measure (Rd d))) := by
  intro P Q h
  ext S hS
  change MeasurableSet[MeasurableSpace.comap
    (Subtype.val : CountingConfiguration d → Measure (Rd d)) inferInstance] S at hS
  rcases MeasurableSpace.measurableSet_comap.mp hS with ⟨T, hT, rfl⟩
  simpa only [Measure.map_apply measurable_subtype_coe hT] using
    congrArg (fun M : Measure (Measure (Rd d)) => M T) h

theorem map_translateCounting_eq_of_isStationary (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hstationary : IsStationary d (P.map Subtype.val)) (a : Rd d) :
    P.map (translateCounting d a) = P := by
  apply map_countingConfiguration_val_injective d
  simpa only [Measure.map_map
      (Measure.measurable_map (fun z : Rd d => a + z)
        (measurable_const.add measurable_id)) measurable_subtype_coe,
    Measure.map_map measurable_subtype_coe (measurable_translateCounting d a),
    Function.comp_def, translateCounting] using hstationary a

theorem offDiagonalPairs_translateCounting (d : ℕ) (a : Rd d)
    (μ : CountingConfiguration d) :
    offDiagonalPairs d (translateCounting d a μ).val =
      (offDiagonalPairs d μ.val).map
        (fun p : Rd d × Rd d => (a + p.1, a + p.2)) := by
  letI : SFinite μ.val := inferInstance
  let t : Rd d → Rd d := fun z => a + z
  let D : Set (Rd d × Rd d) := {p | p.1 ≠ p.2}
  have ht : Measurable t := measurable_const.add measurable_id
  have hD : MeasurableSet D :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hpre : (Prod.map t t) ⁻¹' D = D :=
    Set.ext (fun _ => not_congr add_left_cancel_iff)
  change ((μ.val.map t).prod (μ.val.map t)).restrict D =
    ((μ.val.prod μ.val).restrict D).map (Prod.map t t)
  rw [Measure.map_prod_map μ.val μ.val ht ht,
    Measure.restrict_map (ht.prodMap ht) hD, hpre]

theorem countingOffDiagonalPairMean_map_diagAdd_eq_self (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val)
    (hstationary : IsStationary d (P.map Subtype.val)) (a : Rd d) :
    (countingOffDiagonalPairMean d P).map
      (fun p : Rd d × Rd d => (a + p.1, a + p.2)) =
        countingOffDiagonalPairMean d P := by
  have hP : P.map (translateCounting d a) = P :=
    map_translateCounting_eq_of_isStationary d P hstationary a
  have hF : AEMeasurable
      (fun μ : CountingConfiguration d => offDiagonalPairs d μ.val) P :=
    aemeasurable_counting_offDiagonalPairs_of_simple d P hsimple
  have hT : Measurable (fun p : Rd d × Rd d => (a + p.1, a + p.2)) :=
    (measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd)
  ext E hE
  have hEvalMap : AEMeasurable
      (fun μ : CountingConfiguration d => offDiagonalPairs d μ.val E)
      (P.map (translateCounting d a)) :=
    hP.symm ▸ (Measure.measurable_coe hE).comp_aemeasurable hF
  calc
    (countingOffDiagonalPairMean d P).map
        (fun p : Rd d × Rd d => (a + p.1, a + p.2)) E =
        ∫⁻ μ, offDiagonalPairs d μ.val
          ((fun p : Rd d × Rd d => (a + p.1, a + p.2)) ⁻¹' E) ∂P :=
      (Measure.map_apply hT hE).trans (Measure.bind_apply (hE.preimage hT) hF)
    _ = ∫⁻ μ, offDiagonalPairs d (translateCounting d a μ).val E ∂P :=
      lintegral_congr (fun μ => ((congrArg (fun ν : Measure (Rd d × Rd d) => ν E)
        (offDiagonalPairs_translateCounting d a μ)).trans (Measure.map_apply hT hE)).symm)
    _ = ∫⁻ μ, offDiagonalPairs d μ.val E ∂P.map (translateCounting d a) :=
      (lintegral_map' hEvalMap (measurable_translateCounting d a).aemeasurable).symm
    _ = ∫⁻ μ, offDiagonalPairs d μ.val E ∂P :=
      congrArg (fun M : Measure (CountingConfiguration d) =>
        ∫⁻ μ, offDiagonalPairs d μ.val E ∂M) hP
    _ = countingOffDiagonalPairMean d P E := (Measure.bind_apply hE hF).symm

theorem expectedFactorialMeasure_map_diagAdd_eq_self (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val)
    (hstationary : IsStationary d (P.map Subtype.val)) (a : Rd d) :
    (expectedFactorialMeasure d P hsecond).map
      (fun p : Rd d × Rd d => (a + p.1, a + p.2)) =
        expectedFactorialMeasure d P hsecond := by
  simpa only [expectedFactorialMeasure_eq_countingOffDiagonalPairMean d P hsecond hsimple] using
    countingOffDiagonalPairMean_map_diagAdd_eq_self d P hsimple hstationary a

end Riesz.Configuration

namespace Riesz.Stationary

def gaussianDifferenceWeight (d : ℕ) (u : ℝ) (p : Rd d × Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(u * ‖p.2 - p.1‖ ^ (2 : ℕ))))

theorem measurable_gaussianDifferenceWeight (d : ℕ) (u : ℝ) :
    Measurable (gaussianDifferenceWeight d u) := by
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_snd.sub continuous_fst).norm.pow 2)).neg).measurable

def gaussianAnchorMeasure (d : ℕ) (Γ : Measure (Rd d × Rd d)) (u : ℝ) :
    Measure (Rd d) := (Γ.withDensity (gaussianDifferenceWeight d u)).map Prod.fst

theorem lintegral_gaussianAnchorMeasure (d : ℕ) (Γ : Measure (Rd d × Rd d)) (u : ℝ)
    (f : Rd d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂gaussianAnchorMeasure d Γ u) =
      ∫⁻ p, f p.1 * gaussianDifferenceWeight d u p ∂Γ := by
  rw [gaussianAnchorMeasure, lintegral_map hf measurable_fst,
    lintegral_withDensity_eq_lintegral_mul Γ
      (measurable_gaussianDifferenceWeight d u)
      (show Measurable (fun p : Rd d × Rd d => f p.1) from hf.comp measurable_fst)]
  exact lintegral_congr (fun p => mul_comm _ _)

theorem gaussianAnchorMeasure_isAddLeftInvariant (d : ℕ)
    (Γ : Measure (Rd d × Rd d)) (u : ℝ)
    (hΓ : ∀ a : Rd d, Γ.map
      (fun p : Rd d × Rd d => (a + p.1, a + p.2)) = Γ) :
    (gaussianAnchorMeasure d Γ u).IsAddLeftInvariant := by
  constructor
  intro a
  apply Measure.ext_of_lintegral (gaussianAnchorMeasure d Γ u)
  intro f hf
  have hadd : Measurable (fun x : Rd d => a + x) := measurable_const.add measurable_id
  rw [lintegral_map hf hadd,
    lintegral_gaussianAnchorMeasure d Γ u (fun x => f (a + x)) (hf.comp hadd),
    lintegral_gaussianAnchorMeasure d Γ u f hf]
  let T : Rd d × Rd d → Rd d × Rd d := fun p => (a + p.1, a + p.2)
  have hT : Measurable T :=
    (measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd)
  have hweight (p : Rd d × Rd d) :
      gaussianDifferenceWeight d u (T p) = gaussianDifferenceWeight d u p := by
    simp only [T, gaussianDifferenceWeight, add_sub_add_left_eq_sub]
  have hF : Measurable (fun p : Rd d × Rd d =>
      f p.1 * gaussianDifferenceWeight d u p) :=
    (hf.comp measurable_fst).mul (measurable_gaussianDifferenceWeight d u)
  have hmap : Γ.map T = Γ := hΓ a
  calc
    (∫⁻ p, f (a + p.1) * gaussianDifferenceWeight d u p ∂Γ) =
        ∫⁻ p, f (T p).1 * gaussianDifferenceWeight d u (T p) ∂Γ :=
      lintegral_congr (fun p => congrArg (fun r => f (a + p.1) * r) (hweight p).symm)
    _ = ∫⁻ p, f p.1 * gaussianDifferenceWeight d u p ∂Γ.map T :=
      (lintegral_map hF hT).symm
    _ = ∫⁻ p, f p.1 * gaussianDifferenceWeight d u p ∂Γ :=
      congrArg (fun M => ∫⁻ p, f p.1 * gaussianDifferenceWeight d u p ∂M) hmap

theorem gaussianAnchorMeasure_unitCube_eq_Q (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val) (u : ℝ) :
    gaussianAnchorMeasure d (expectedFactorialMeasure d P hsecond) u (cube d 1) =
      Q d (P.map Subtype.val) u := by
  have hK := Riesz.Negative.measurableSet_cube d 1
  rw [gaussianAnchorMeasure, Measure.map_apply measurable_fst hK,
    withDensity_apply _ (hK.preimage measurable_fst),
    Q_map_val_eq_expectedFactorialMeasure d P hsecond hsimple u,
    ← lintegral_indicator (hK.preimage measurable_fst)]
  apply lintegral_congr
  intro p
  by_cases hp : p.1 ∈ cube d 1
  all_goals simp [Set.indicator, anchoredGaussianKernel, gaussianDifferenceWeight, hp]

theorem expectedFactorialMeasure_gaussian_normalized_compact_anchor_eq_Q
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val)
    (hstationary : IsStationary d (P.map Subtype.val))
    (u : ℝ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (hχnorm : (∫ x, χ x ∂volume) = 1) :
    (∫⁻ p, ENNReal.ofReal (χ p.1) * gaussianDifferenceWeight d u p
      ∂expectedFactorialMeasure d P hsecond) = Q d (P.map Subtype.val) u := by
  let Γ : Measure (Rd d × Rd d) := expectedFactorialMeasure d P hsecond
  let A : Measure (Rd d) := gaussianAnchorMeasure d Γ u
  letI : SFinite Γ := inferInstance
  letI : SFinite A := inferInstanceAs (SFinite
    ((Γ.withDensity (gaussianDifferenceWeight d u)).map Prod.fst))
  have hΓ : ∀ a : Rd d, Γ.map
      (fun p : Rd d × Rd d => (a + p.1, a + p.2)) = Γ :=
    expectedFactorialMeasure_map_diagAdd_eq_self d P hsecond hsimple hstationary
  letI : A.IsAddLeftInvariant := gaussianAnchorMeasure_isAddLeftInvariant d Γ u hΓ
  have hχmeas : Measurable (fun x : Rd d => ENNReal.ofReal (χ x)) :=
    χ.continuous.measurable.ennreal_ofReal
  have hχone : (∫⁻ x, ENNReal.ofReal (χ x) ∂volume) = 1 :=
    (ofReal_integral_eq_lintegral_ofReal χ.integrable
      (Filter.Eventually.of_forall hχ)).symm.trans
        ((congrArg ENNReal.ofReal hχnorm).trans ENNReal.ofReal_one)
  calc
    (∫⁻ p, ENNReal.ofReal (χ p.1) * gaussianDifferenceWeight d u p ∂Γ) =
        ∫⁻ x, ENNReal.ofReal (χ x) ∂A :=
      (lintegral_gaussianAnchorMeasure d Γ u _ hχmeas).symm
    _ = A (cube d 1) * (∫⁻ x, ENNReal.ofReal (χ x) ∂volume) :=
      lintegral_eq_unitCube_mul_lintegral_of_addLeftInvariant d A _ hχmeas
    _ = A (cube d 1) := (congrArg (fun r => A (cube d 1) * r) hχone).trans (mul_one _)
    _ = Q d (P.map Subtype.val) u :=
      gaussianAnchorMeasure_unitCube_eq_Q d P hsecond hsimple u

/-- Clipping retains compact support and supplies the upper bound by one. -/
def gaussianSecondCutoff (d n : ℕ) : C_c(Rd d, ℝ) := by
  refine ⟨⟨fun y => min (countingMassCutoff d n y) 1,
    (countingMassCutoff d n).continuous.min continuous_const⟩, ?_⟩
  change HasCompactSupport ((fun r : ℝ => min r 1) ∘ countingMassCutoff d n)
  exact (countingMassCutoff d n).hasCompactSupport.comp_left (min_eq_left zero_le_one)

theorem gaussianSecondCutoff_bounds (d n : ℕ) (y : Rd d) :
    0 ≤ gaussianSecondCutoff d n y ∧ gaussianSecondCutoff d n y ≤ 1 := by
  exact ⟨le_min ((countingMassCutoff_spec d n).1 y) zero_le_one, min_le_right _ _⟩

theorem gaussianSecondCutoff_eq_one_of_mem_closedBall (d n : ℕ) (y : Rd d)
    (hy : y ∈ Metric.closedBall (0 : Rd d) (n : ℝ)) :
    gaussianSecondCutoff d n y = 1 := by
  change min (countingMassCutoff d n y) 1 = 1
  exact (congrArg (fun r : ℝ => min r 1) ((countingMassCutoff_spec d n).2 hy)).trans
    (min_self 1)

theorem eventually_gaussianSecondCutoff_eq_one (d : ℕ) (y : Rd d) :
    ∀ᶠ n : ℕ in atTop, gaussianSecondCutoff d n y = 1 := by
  have hN : ∀ᶠ n : ℕ in atTop, ‖y‖ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop ‖y‖)
  filter_upwards [hN] with n hn
  exact gaussianSecondCutoff_eq_one_of_mem_closedBall d n y
    ((mem_closedBall_zero_iff).mpr hn)

/-- Cutting off both coordinates gives genuine compact support on the pair space. -/
def gaussianCompactSecondAnchor (d : ℕ) (χ : C_c(Rd d, ℝ)) (n : ℕ) :
    C_c(Rd d × Rd d, ℝ) := by
  refine ⟨⟨fun p => χ p.1 * gaussianSecondCutoff d n p.2,
    (χ.continuous.comp continuous_fst).mul
      ((gaussianSecondCutoff d n).continuous.comp continuous_snd)⟩, ?_⟩
  refine HasCompactSupport.of_support_subset_isCompact
    (χ.hasCompactSupport.isCompact.prod
      (gaussianSecondCutoff d n).hasCompactSupport.isCompact) ?_
  intro p hp
  change χ p.1 * gaussianSecondCutoff d n p.2 ≠ 0 at hp
  exact ⟨subset_tsupport χ (mul_ne_zero_iff.mp hp).1,
    subset_tsupport (gaussianSecondCutoff d n) (mul_ne_zero_iff.mp hp).2⟩

theorem gaussianCompactSecondAnchor_bounds (d : ℕ) (χ : C_c(Rd d, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) (n : ℕ) (p : Rd d × Rd d) :
    0 ≤ gaussianCompactSecondAnchor d χ n p ∧
      gaussianCompactSecondAnchor d χ n p ≤ χ p.1 := by
  exact ⟨mul_nonneg (hχ p.1) (gaussianSecondCutoff_bounds d n p.2).1,
    mul_le_of_le_one_right (hχ p.1) (gaussianSecondCutoff_bounds d n p.2).2⟩

theorem eventually_gaussianCompactSecondAnchor_eq (d : ℕ)
    (χ : C_c(Rd d, ℝ)) (p : Rd d × Rd d) :
    ∀ᶠ n : ℕ in atTop, gaussianCompactSecondAnchor d χ n p = χ p.1 := by
  filter_upwards [eventually_gaussianSecondCutoff_eq_one d p.2] with n hn
  exact (congrArg (fun r : ℝ => χ p.1 * r) hn).trans (mul_one _)

/-- Fatou removes the second-point cutoff, retaining infinite bounds. -/
theorem gaussian_anchor_lintegral_le_of_compactSecondAnchor_bound
    (d : ℕ) (Γ : Measure (Rd d × Rd d)) (χ : C_c(Rd d, ℝ)) (u : ℝ)
    (C : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ p, ENNReal.ofReal (gaussianCompactSecondAnchor d χ n p) *
        gaussianDifferenceWeight d u p ∂Γ) ≤ C) :
    (∫⁻ p, ENNReal.ofReal (χ p.1) * gaussianDifferenceWeight d u p ∂Γ) ≤ C := by
  let F : ℕ → Rd d × Rd d → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (gaussianCompactSecondAnchor d χ n p) * gaussianDifferenceWeight d u p
  have hmeas (n : ℕ) : Measurable (F n) :=
    (gaussianCompactSecondAnchor d χ n).continuous.measurable.ennreal_ofReal.mul
      (measurable_gaussianDifferenceWeight d u)
  have hpoint (p : Rd d × Rd d) :
      atTop.liminf (fun n : ℕ => F n p) =
        ENNReal.ofReal (χ p.1) * gaussianDifferenceWeight d u p := by
    exact (Filter.liminf_congr
      ((eventually_gaussianCompactSecondAnchor_eq d χ p).mono (fun n hn =>
        congrArg (fun r : ℝ => ENNReal.ofReal r * gaussianDifferenceWeight d u p) hn))).trans
      (Filter.liminf_const _)
  calc
    (∫⁻ p, ENNReal.ofReal (χ p.1) * gaussianDifferenceWeight d u p ∂Γ) =
        ∫⁻ p, atTop.liminf (fun n : ℕ => F n p) ∂Γ :=
      lintegral_congr (fun p => (hpoint p).symm)
    _ ≤ atTop.liminf (fun n : ℕ => ∫⁻ p, F n p ∂Γ) := lintegral_liminf_le hmeas
    _ ≤ C := Filter.liminf_le_of_frequently_le'
      (Filter.Eventually.of_forall hbound).frequently

theorem Q_le_of_compactSecondAnchor_gaussian_bound
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hsimple : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val)
    (hstationary : IsStationary d (P.map Subtype.val))
    (u : ℝ) (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x)
    (hχnorm : (∫ x, χ x ∂volume) = 1) (C : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ p, ENNReal.ofReal
        (Riesz.Asymptotics.compactGaussianFactorialTest d (gaussianCompactSecondAnchor d χ n) u p)
        ∂expectedFactorialMeasure d P hsecond) ≤ C) :
    Q d (P.map Subtype.val) u ≤ C := by
  refine (expectedFactorialMeasure_gaussian_normalized_compact_anchor_eq_Q
    d P hsecond hsimple hstationary u χ hχ hχnorm).symm.trans_le
      (gaussian_anchor_lintegral_le_of_compactSecondAnchor_bound
        d (expectedFactorialMeasure d P hsecond) χ u C ?_)
  intro n
  have hident (p : Rd d × Rd d) :
      ENNReal.ofReal (gaussianCompactSecondAnchor d χ n p) * gaussianDifferenceWeight d u p =
        ENNReal.ofReal (Riesz.Asymptotics.compactGaussianFactorialTest d
          (gaussianCompactSecondAnchor d χ n) u p) := by
    change ENNReal.ofReal (gaussianCompactSecondAnchor d χ n p) *
        ENNReal.ofReal (Real.exp (-(u * ‖p.2 - p.1‖ ^ (2 : ℕ)))) =
      ENNReal.ofReal (gaussianCompactSecondAnchor d χ n p *
        Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ)))
    simpa only [neg_mul] using (ENNReal.ofReal_mul
      (gaussianCompactSecondAnchor_bounds d χ hχ n p).1).symm
  exact (lintegral_congr hident).trans_le (hbound n)

end Riesz.Stationary

namespace Riesz.Asymptotics

/-- Local second moments pass normalized compact-anchor expectations to the limit. -/
theorem countingLaw_normalized_compact_anchor_lintegral_tendsto
    (d : ℕ) (P : ℕ → ProbabilityMeasure (CountingConfiguration d))
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto P atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2 ∂(P n).toMeasure) ≤ C)
    (hmean : (Q.toMeasure.map Subtype.val).join = volume)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ z, 0 ≤ χ z)
    (hχmass : (∫ z, χ z ∂(volume : Measure (Rd d))) = 1) :
    Tendsto (fun n => ∫⁻ μ, ENNReal.ofReal (∫ z, χ z ∂μ.val)
      ∂(P n).toMeasure) atTop (𝓝 (1 : ℝ≥0∞)) := by
  let F : CountingConfiguration d → ℝ := fun μ => ∫ z, χ z ∂μ.val
  have hF : Continuous F := continuous_countingIntegral d χ
  have hF0 : ∀ μ, 0 ≤ F μ := fun μ => integral_nonneg hχ
  obtain ⟨C, hC, hpre, _hlimit⟩ :=
    exists_countingLaw_nonneg_test_second_moment_bound d P Q hQ hball χ hχ
  have hFi (n : ℕ) : Integrable F (P n).toMeasure := by
    have hsq : Integrable (fun μ => F μ ^ (2 : ℕ)) (P n).toMeasure :=
      (lintegral_ofReal_ne_top_iff_integrable
        (hF.pow 2).measurable.aestronglyMeasurable
        (Eventually.of_forall (fun μ => sq_nonneg (F μ)))).mp
          (ne_top_of_le_ne_top hC (hpre n))
    refine ((integrable_const (1 : ℝ)).add hsq).mono_nonneg
      hF.measurable.aestronglyMeasurable (Eventually.of_forall hF0)
      (Eventually.of_forall (fun μ => ?_))
    change F μ ≤ 1 + F μ ^ (2 : ℕ)
    nlinarith [sq_nonneg (F μ - 1)]
  have hlimit : (∫ μ, F μ ∂Q.toMeasure) = 1 :=
    (countingLaw_nonneg_test_expectation_eq_meanIntegral d Q χ hχ).trans
      ((congrArg (fun M => ∫ z, χ z ∂M) hmean).trans hχmass)
  have hreal : Tendsto (fun n => ∫ μ, F μ ∂(P n).toMeasure) atTop (𝓝 (1 : ℝ)) :=
    hlimit ▸ countingLaw_nonneg_test_expectations_tendsto d P Q hQ hball χ hχ
  have heq (n : ℕ) : ENNReal.ofReal (∫ μ, F μ ∂(P n).toMeasure) =
      ∫⁻ μ, ENNReal.ofReal (F μ) ∂(P n).toMeasure :=
    ofReal_integral_eq_lintegral_ofReal (hFi n) (Eventually.of_forall hF0)
  simpa only [heq, ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hreal

/-- The compact first anchor, extended by zero over the southern hemisphere. -/
def sphereCompactAnchor (d : ℕ) (R : ℝ) (χ : C_c(Rd d, ℝ))
    (y : Sphere d) : ℝ≥0∞ := ENNReal.ofReal (hemisphereChartTest d R χ y)

theorem measurable_sphereCompactAnchor (d : ℕ) (R : ℝ)
    (χ : C_c(Rd d, ℝ)) : Measurable (sphereCompactAnchor d R χ) := by
  have hchart : Measurable (fun y : Sphere d => χ (normalInverse d R y.val)) :=
    χ.continuous.measurable.comp
      ((normalInverse_continuous d R).measurable.comp measurable_subtype_coe)
  exact (Measurable.ite (northHemisphere_isOpen d).measurableSet
    hchart measurable_const).ennreal_ofReal

/-- Exact first-label averaging, also valid for zero particles. -/
theorem sphereLocalCountingProbability_compact_anchor_prefactor_eq
    (d N : ℕ) (R : ℝ) (x : Fin N → Sphere d)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ z, 0 ≤ χ z) :
    (∫⁻ μ, ENNReal.ofReal (∫ z, χ z ∂μ.val)
      ∂(sphereLocalCountingProbability d N R x).toMeasure) =
        (N : ℝ≥0∞) * ∫⁻ y, sphereCompactAnchor d R χ y ∂sphericalMeasure d := by
  have hχChart : ∀ y : Sphere d, 0 ≤ hemisphereChartTest d R χ y :=
    fun y => ite_nonneg (hχ _) le_rfl
  have hpoint (U : Problem1.Orthogonal d) :
      ENNReal.ofReal (∫ z, χ z ∂(sphereLocalConfiguration d N R x U).val) =
        ∑ i : Fin N, sphereCompactAnchor d R χ (rotateSphere d U (x i)) := by
    change ENNReal.ofReal (∫ z, χ z ∂sphereLocalCounting d N R x U) = _
    exact (congrArg ENNReal.ofReal (integral_sphereLocalCounting_eq_sum d N R x U χ)).trans
      (ENNReal.ofReal_sum_of_nonneg (fun i _ => hχChart (rotateSphere d U (x i))))
  have hw : Measurable (sphereCompactAnchor d R χ) := measurable_sphereCompactAnchor d R χ
  have heval (i : Fin N) :
      (∫⁻ U, sphereCompactAnchor d R χ (rotateSphere d U (x i)) ∂uniformRotationLaw d) =
        ∫⁻ y, sphereCompactAnchor d R χ y ∂sphericalMeasure d :=
    (uniformRotationLaw_measurePreserving d (x i)).lintegral_comp hw
  change (∫⁻ μ, ENNReal.ofReal (∫ z, χ z ∂μ.val)
    ∂(uniformRotationLaw d).map (sphereLocalConfiguration d N R x)) = _
  rw [lintegral_map (continuous_countingIntegral d χ).measurable.ennreal_ofReal
    (measurable_sphereLocalConfiguration_fixed d N R x)]
  simp_rw [hpoint]
  rw [lintegral_finsetSum Finset.univ (fun i _ =>
    (show Measurable (fun U => sphereCompactAnchor d R χ (rotateSphere d U (x i))) from
      hw.comp (uniformRotationLaw_measurePreserving d (x i)).measurable))]
  simp only [heval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem sphereLocalCountingProbability_normalized_compact_anchor_lintegral_tendsto
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto (fun n => sphereLocalCountingProbability d (N n)
      (sphericalRadius d (N n)) (x n)) atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(sphereLocalCountingProbability d (N n)
          (sphericalRadius d (N n)) (x n)).toMeasure) ≤ C)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ z, 0 ≤ χ z)
    (hχmass : (∫ z, χ z ∂(volume : Measure (Rd d))) = 1) :
    Tendsto (fun n => ∫⁻ μ, ENNReal.ofReal (∫ z, χ z ∂μ.val)
      ∂(sphereLocalCountingProbability d (N n)
        (sphericalRadius d (N n)) (x n)).toMeasure) atTop (𝓝 (1 : ℝ≥0∞)) := by
  exact countingLaw_normalized_compact_anchor_lintegral_tendsto d _ Q hQ hball
    (sphereLocalCountingProbability_limit_mean_eq_volume_unconditional
      d hd N hN x Q hQ hball) χ hχ hχmass

/-- The exact first-anchor factor in spherical Haar averaging tends to one. -/
theorem sphereCompactAnchor_normalized_prefactor_tendsto
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto (fun n => sphereLocalCountingProbability d (N n)
      (sphericalRadius d (N n)) (x n)) atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(sphereLocalCountingProbability d (N n)
          (sphericalRadius d (N n)) (x n)).toMeasure) ≤ C)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ z, 0 ≤ χ z)
    (hχmass : (∫ z, χ z ∂(volume : Measure (Rd d))) = 1) :
    Tendsto (fun n => (N n : ℝ≥0∞) *
      ∫⁻ y, sphereCompactAnchor d (sphericalRadius d (N n)) χ y ∂sphericalMeasure d)
      atTop (𝓝 (1 : ℝ≥0∞)) := by
  simpa only [sphereLocalCountingProbability_compact_anchor_prefactor_eq d _ _ _ χ hχ] using
    sphereLocalCountingProbability_normalized_compact_anchor_lintegral_tendsto
      d hd N hN x Q hQ hball χ hχ hχmass

/-- Weight the first original label and retain every unequal second label. -/
def sphereWeightedAnchoredGaussianPairSum (d N : ℕ) (R u : ℝ)
    (x : Fin N → Sphere d) (w : Sphere d → ℝ≥0∞)
    (U : Problem1.Orthogonal d) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else
    w (rotateSphere d U (x i)) * ENNReal.ofReal
      (Real.exp (-(u * R ^ (2 : ℕ)) *
        (chord d (rotateSphere d U (x i)) (rotateSphere d U (x j))) ^ (2 : ℕ)))

theorem sphereWeightedAnchoredGaussianPairSum_mean (d N : ℕ) (hN : 0 < N)
    (u : ℝ) (x : Fin N → Sphere d) (w : Sphere d → ℝ≥0∞)
    (hw : Measurable w) :
    (∫⁻ U, sphereWeightedAnchoredGaussianPairSum d N
      (sphericalRadius d N) u x w U ∂uniformRotationLaw d) =
      ((N : ℝ≥0∞) * ∫⁻ y, w y ∂sphericalMeasure d) *
        ENNReal.ofReal (sphericalGaussianPairProfile d N x u) := by
  let q : Fin N → Fin N → ℝ≥0∞ := fun i j =>
    if i = j then 0 else ENNReal.ofReal (Real.exp
      (-(u * (sphericalRadius d N) ^ (2 : ℕ)) * (chord d (x i) (x j)) ^ (2 : ℕ)))
  have hsum (U : Problem1.Orthogonal d) :
      sphereWeightedAnchoredGaussianPairSum d N (sphericalRadius d N) u x w U =
        ∑ i : Fin N, w (rotateSphere d U (x i)) * ∑ j : Fin N, q i j := by
    simp only [sphereWeightedAnchoredGaussianPairSum, rotateSphere_chord, q,
      Finset.mul_sum, mul_ite, mul_zero]
  have heval (i : Fin N) :
      (∫⁻ U, w (rotateSphere d U (x i)) * ∑ j : Fin N, q i j ∂uniformRotationLaw d) =
        (∫⁻ y, w y ∂sphericalMeasure d) * ∑ j : Fin N, q i j :=
    (lintegral_mul_const _
      (show Measurable (fun U => w (rotateSphere d U (x i))) from
        hw.comp (uniformRotationLaw_measurePreserving d (x i)).measurable)).trans
      (congrArg (fun r => r * ∑ j : Fin N, q i j)
        ((uniformRotationLaw_measurePreserving d (x i)).lintegral_comp hw))
  have hnormal : (N : ℝ) * sphericalGaussianPairProfile d N x u =
      ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else Real.exp
        (-(u * (sphericalRadius d N) ^ (2 : ℕ)) * (chord d (x i) (x j)) ^ (2 : ℕ)) := by
    simp only [sphericalGaussianPairProfile, ← mul_assoc,
      mul_inv_cancel₀ (show (N : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hN.ne'), one_mul]
  have hterm (i j : Fin N) : 0 ≤ (if i = j then 0 else Real.exp
      (-(u * (sphericalRadius d N) ^ (2 : ℕ)) * (chord d (x i) (x j)) ^ (2 : ℕ))) :=
    ite_nonneg le_rfl (Real.exp_pos _).le
  have hnormalENN : (N : ℝ≥0∞) * ENNReal.ofReal (sphericalGaussianPairProfile d N x u) =
      ∑ i : Fin N, ∑ j : Fin N, q i j := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N), hnormal,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hterm i j))]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [apply_ite, ENNReal.ofReal_zero, q] using
      ENNReal.ofReal_sum_of_nonneg (fun j _ => hterm i j)
  simp_rw [hsum]
  rw [lintegral_finsetSum Finset.univ (fun i _ =>
    (show Measurable (fun U => w (rotateSphere d U (x i)) * ∑ j : Fin N, q i j) from
      (hw.comp (uniformRotationLaw_measurePreserving d (x i)).measurable).mul measurable_const))]
  simp only [heval, ← Finset.mul_sum, ← hnormalENN]
  ac_rfl

theorem sphereWeightedAnchoredGaussianPairSum_compact_anchor_mean
    (d N : ℕ) (hN : 0 < N) (u : ℝ) (x : Fin N → Sphere d)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ z, 0 ≤ χ z) :
    (∫⁻ U, sphereWeightedAnchoredGaussianPairSum d N
      (sphericalRadius d N) u x
      (sphereCompactAnchor d (sphericalRadius d N) χ) U ∂uniformRotationLaw d) =
      (∫⁻ μ, ENNReal.ofReal (∫ z, χ z ∂μ.val)
        ∂(sphereLocalCountingProbability d N (sphericalRadius d N) x).toMeasure) *
          ENNReal.ofReal (sphericalGaussianPairProfile d N x u) := by
  exact (sphereWeightedAnchoredGaussianPairSum_mean d N hN u x
    (sphereCompactAnchor d (sphericalRadius d N) χ)
    (measurable_sphereCompactAnchor d (sphericalRadius d N) χ)).trans
      (congrArg (fun r => r * ENNReal.ofReal (sphericalGaussianPairProfile d N x u))
        (sphereLocalCountingProbability_compact_anchor_prefactor_eq
          d N (sphericalRadius d N) x χ hχ).symm)

/-- A factor tending to one can be removed even for an infinite liminf. -/
theorem liminf_mul_le_of_tendsto_one
    (a g : ℕ → ℝ≥0∞) (ha : Tendsto a atTop (𝓝 1)) :
    Filter.liminf (fun n => a n * g n) atTop ≤ Filter.liminf g atTop := by
  have hs : Filter.limsup a atTop = 1 := ha.limsup_eq
  have h := ENNReal.liminf_mul_le (f := atTop) (u := a) (v := g)
    (Or.inl (hs.symm ▸ one_ne_zero)) (Or.inl (hs.symm ▸ ENNReal.one_ne_top))
  simpa only [Pi.mul_def, hs, one_mul] using h

/-- The sharp compact comparison keeps every unequal original label. -/
theorem eventually_compactGaussianFactorial_le_weightedAnchored
    (d : ℕ) (b : C_c(Rd d × Rd d, ℝ)) (χ : C_c(Rd d, ℝ))
    (hχ : ∀ z, 0 ≤ χ z) (hbχ : ∀ p, b p ≤ χ p.1)
    (u T ε : ℝ) (hε : 0 < ε)
    (hsupport : tsupport b ⊆ Metric.closedBall (0 : Rd d) T ×ˢ
      Metric.closedBall (0 : Rd d) T) :
    ∀ᶠ R : ℝ in atTop, ∀ (N : ℕ) (x : Fin N → Sphere d) (U : Problem1.Orthogonal d),
      ENNReal.ofReal (countingFactorialIntegral d
        (sphereLocalConfiguration d N R x U) (compactGaussianFactorialTest d b u)) ≤
        ENNReal.ofReal (1 + ε) * sphereWeightedAnchoredGaussianPairSum d N R u x
          (sphereCompactAnchor d R χ) U := by
  filter_upwards [eventually_normalGaussian_le_sphericalGaussian d u T ε hε,
    eventually_gt_atTop (0 : ℝ)] with R hgaussian hR N x U
  let y : Fin N → Sphere d := fun i => rotateSphere d U (x i)
  let z : Fin N → Rd d := fun i => normalInverse d R (y i).val
  let F : Fin N → Fin N → ℝ := fun i j =>
    if i = j then 0 else
      if y i ∈ northHemisphere d ∧ y j ∈ northHemisphere d then
        compactGaussianFactorialTest d b u (z i, z j) else 0
  let G : Fin N → Fin N → ℝ := fun i j =>
    if i = j then 0 else if y i ∈ northHemisphere d then
      χ (z i) * Real.exp (-(u * R ^ (2 : ℕ)) * chord d (y i) (y j) ^ (2 : ℕ)) else 0
  have hGnonneg (i j : Fin N) : 0 ≤ G i j :=
    ite_nonneg le_rfl (ite_nonneg (mul_nonneg (hχ _) (Real.exp_nonneg _)) le_rfl)
  have hfactor : 0 ≤ 1 + ε := add_nonneg zero_le_one hε.le
  have hterm (i j : Fin N) : F i j ≤ (1 + ε) * G i j := by
    by_cases hij : i = j
    · simp [F, G, hij]
    · by_cases hnorth : y i ∈ northHemisphere d ∧ y j ∈ northHemisphere d
      · by_cases hs : (z i, z j) ∈ tsupport b
        · have hnormal : normalPoint d R (z i) = y i ∧ normalPoint d R (z j) = y j :=
            ⟨normalPoint_normalInverse d hR hnorth.1, normalPoint_normalInverse d hR hnorth.2⟩
          have he : Real.exp (-u * ‖z j - z i‖ ^ (2 : ℕ)) ≤
              (1 + ε) * Real.exp (-(u * R ^ (2 : ℕ)) * chord d (y i) (y j) ^ (2 : ℕ)) := by
            simpa only [hnormal.1, hnormal.2, norm_sub_rev] using
              hgaussian (z i) (hsupport hs).1 (z j) (hsupport hs).2
          have hweight : b (z i, z j) * Real.exp (-u * ‖z j - z i‖ ^ (2 : ℕ)) ≤
              (1 + ε) * (χ (z i) *
                Real.exp (-(u * R ^ (2 : ℕ)) * chord d (y i) (y j) ^ (2 : ℕ))) :=
            (mul_le_mul_of_nonneg_right (hbχ (z i, z j)) (Real.exp_nonneg _)).trans
              ((mul_le_mul_of_nonneg_left he (hχ (z i))).trans_eq (mul_left_comm _ _ _))
          simpa [F, G, hij, hnorth, hnorth.1, compactGaussianFactorialTest] using hweight
        · simpa [F, hij, hnorth, compactGaussianFactorialTest,
            image_eq_zero_of_notMem_tsupport hs] using mul_nonneg hfactor (hGnonneg i j)
      · simpa [F, hij, hnorth] using mul_nonneg hfactor (hGnonneg i j)
  have hsum : (∑ i : Fin N, ∑ j : Fin N, F i j) ≤
      (1 + ε) * (∑ i : Fin N, ∑ j : Fin N, G i j) := by
    simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm i j))
  have hFsum : countingFactorialIntegral d (sphereLocalConfiguration d N R x U)
      (compactGaussianFactorialTest d b u) = ∑ i : Fin N, ∑ j : Fin N, F i j :=
    countingFactorialIntegral_sphereLocalConfiguration_eq_sum d N R x U
      (compactGaussianFactorialTest d b u)
  have hGterm (i j : Fin N) : ENNReal.ofReal (G i j) =
      (if i = j then 0 else sphereCompactAnchor d R χ (y i) * ENNReal.ofReal
        (Real.exp (-(u * R ^ (2 : ℕ)) * chord d (y i) (y j) ^ (2 : ℕ)))) := by
    by_cases hij : i = j
    · simp [G, hij]
    · by_cases hi : y i ∈ northHemisphere d
      all_goals simp [G, hij, hi, sphereCompactAnchor, hemisphereChartTest, z,
        ENNReal.ofReal_mul (hχ (z i))]
  have hGsum : ENNReal.ofReal (∑ i : Fin N, ∑ j : Fin N, G i j) =
      sphereWeightedAnchoredGaussianPairSum d N R u x (sphereCompactAnchor d R χ) U :=
    (ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hGnonneg i j))).trans
      (Finset.sum_congr rfl (fun i _ =>
        (ENNReal.ofReal_sum_of_nonneg (fun j _ => hGnonneg i j)).trans
          (Finset.sum_congr rfl (fun j _ => hGterm i j))))
  simpa only [hFsum, ENNReal.ofReal_mul hfactor, hGsum] using ENNReal.ofReal_le_ofReal hsum

theorem eventually_compactGaussianFactorial_mean_le_weightedAnchor
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d)
    (b : C_c(Rd d × Rd d, ℝ)) (χ : C_c(Rd d, ℝ))
    (hχ : ∀ z, 0 ≤ χ z) (hbχ : ∀ p, b p ≤ χ p.1)
    (u T ε : ℝ) (hε : 0 < ε)
    (hsupport : tsupport b ⊆ Metric.closedBall (0 : Rd d) T ×ˢ
      Metric.closedBall (0 : Rd d) T) :
    ∀ᶠ n : ℕ in atTop,
      (∫⁻ μ, ENNReal.ofReal (countingFactorialIntegral d μ (compactGaussianFactorialTest d b u))
        ∂(sphereLocalCountingProbability d (N n) (sphericalRadius d (N n)) (x n)).toMeasure) ≤
        ENNReal.ofReal (1 + ε) *
          (((N n : ℝ≥0∞) * ∫⁻ y, sphereCompactAnchor d (sphericalRadius d (N n)) χ y
              ∂sphericalMeasure d) *
            ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n) u)) := by
  have hR : Tendsto (fun n => sphericalRadius d (N n)) atTop atTop :=
    (sphericalRadius_tendsto_atTop d ((Nat.zero_lt_succ 1).trans_le hd)).comp hN
  filter_upwards [hR.eventually
      (eventually_compactGaussianFactorial_le_weightedAnchored d b χ hχ hbχ u T ε hε hsupport),
    hN.eventually_gt_atTop 0] with n hpath hn
  change (∫⁻ μ, ENNReal.ofReal (countingFactorialIntegral d μ (compactGaussianFactorialTest d b u))
    ∂(uniformRotationLaw d).map
      (sphereLocalConfiguration d (N n) (sphericalRadius d (N n)) (x n))) ≤ _
  rw [lintegral_map
    ((continuous_countingFactorialIntegral d (compactGaussianFactorialTest d b u)).measurable.ennreal_ofReal)
    (measurable_sphereLocalConfiguration_fixed d (N n) (sphericalRadius d (N n)) (x n))]
  exact (lintegral_mono (μ := uniformRotationLaw d) (hpath (N n) (x n))).trans_eq
    ((lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
      (congrArg (fun r => ENNReal.ofReal (1 + ε) * r)
        (sphereWeightedAnchoredGaussianPairSum_mean d (N n) hn u (x n)
          (sphereCompactAnchor d (sphericalRadius d (N n)) χ)
          (measurable_sphereCompactAnchor d (sphericalRadius d (N n)) χ))))

theorem ennreal_le_of_forall_pos_one_add_mul_le
    (A B : ℝ≥0∞) (h : ∀ ε : ℝ, 0 < ε → A ≤ ENNReal.ofReal (1 + ε) * B) :
    A ≤ B := by
  have hreal : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [id_eq, add_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ε : ℝ => (1 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ))).add (tendsto_id.mono_left nhdsWithin_le_nhds))
  have hcoeff : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hreal
  have hprod : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε) * B)
      (𝓝[>] (0 : ℝ)) (𝓝 B) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hcoeff (Or.inl one_ne_zero)
  exact ge_of_tendsto hprod
    ((show ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioi 0 from self_mem_nhdsWithin).mono
      (fun ε hε => h ε hε))

theorem compactGaussianFactorial_limit_le_sphericalProfile_liminf
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
    (b : C_c(Rd d × Rd d, ℝ)) (hb : ∀ p, 0 ≤ b p)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ z, 0 ≤ χ z)
    (hχmass : (∫ z, χ z ∂(volume : Measure (Rd d))) = 1)
    (hbχ : ∀ p, b p ≤ χ p.1) (u : ℝ) :
    (∫⁻ p, ENNReal.ofReal (compactGaussianFactorialTest d b u p)
      ∂expectedFactorialMeasure d Q.toMeasure hsecondQ) ≤
        atTop.liminf (fun n => ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n) u)) := by
  let P : ℕ → ProbabilityMeasure (CountingConfiguration d) := fun n =>
    sphereLocalCountingProbability d (N n) (sphericalRadius d (N n)) (x n)
  let a : ℕ → ℝ≥0∞ := fun n => (N n : ℝ≥0∞) * ∫⁻ y,
    sphereCompactAnchor d (sphericalRadius d (N n)) χ y ∂sphericalMeasure d
  let g : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n) u)
  have ha : Tendsto a atTop (𝓝 1) :=
    sphereCompactAnchor_normalized_prefactor_tendsto d hd N hN x Q hQ hball χ hχ hχmass
  obtain ⟨T, hT⟩ := ((b.hasCompactSupport.image continuous_fst).union
    (b.hasCompactSupport.image continuous_snd)).isBounded.exists_norm_le
  have hsupport : tsupport b ⊆ Metric.closedBall (0 : Rd d) T ×ˢ
      Metric.closedBall (0 : Rd d) T := fun p hp =>
    ⟨mem_closedBall_zero_iff.mpr (hT p.1 (Or.inl ⟨p, hp, rfl⟩)),
      mem_closedBall_zero_iff.mpr (hT p.2 (Or.inr ⟨p, hp, rfl⟩))⟩
  apply ennreal_le_of_forall_pos_one_add_mul_le
  intro ε hε
  have hport := lintegral_expectedFactorialMeasure_le_liminf d P Q hQ hsecondQ
    (compactGaussianFactorialTest d b u) (compactGaussianFactorialTest_nonneg d b hb u)
  have hlim : (∫⁻ p, ENNReal.ofReal (compactGaussianFactorialTest d b u p)
      ∂expectedFactorialMeasure d Q.toMeasure hsecondQ) ≤
        atTop.liminf (fun n => ENNReal.ofReal (1 + ε) * (a n * g n)) :=
    hport.trans (Filter.liminf_le_liminf
      (eventually_compactGaussianFactorial_mean_le_weightedAnchor
        d hd N hN x b χ hχ hbχ u T ε hε hsupport))
  rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top] at hlim
  exact hlim.trans
    (mul_le_mul_right (liminf_mul_le_of_tendsto_one a g ha) (ENNReal.ofReal (1 + ε)))

theorem Q_actual_spherical_limit_le_profile_liminf_of_simple
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, Fin (N n) → Sphere d)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto (fun n => sphereLocalCountingProbability d (N n)
      (sphericalRadius d (N n)) (x n)) atTop (𝓝 Q))
    (hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(sphereLocalCountingProbability d (N n)
          (sphericalRadius d (N n)) (x n)).toMeasure) ≤ C)
    (hsimple : ∀ᵐ μ ∂Q.toMeasure, IsSimpleConfiguration d μ.val)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ z, 0 ≤ χ z)
    (hχmass : (∫ z, χ z ∂(volume : Measure (Rd d))) = 1) (u : ℝ) :
    RieszShowcase.Q d (Q.toMeasure.map Subtype.val) u ≤
      atTop.liminf (fun n => ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n) u)) := by
  have hsecondQ : ∀ m : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (m : ℝ))) ^ 2 ∂Q.toMeasure) < ∞ :=
    fun m => countingLaw_limit_local_second_moments d _ Q hQ hball
      (Metric.closedBall (0 : Rd d) (m : ℝ)) measurableSet_closedBall
      (isCompact_closedBall (0 : Rd d) (m : ℝ)).isBounded
  apply Riesz.Stationary.Q_le_of_compactSecondAnchor_gaussian_bound
    d Q.toMeasure hsecondQ hsimple
    (sphereLocalCountingProbability_limit_stationary d hd N hN x Q hQ) u χ hχ hχmass
  exact fun k => compactGaussianFactorial_limit_le_sphericalProfile_liminf
    d hd N hN x Q hQ hball hsecondQ (Riesz.Stationary.gaussianCompactSecondAnchor d χ k)
    (fun p => (Riesz.Stationary.gaussianCompactSecondAnchor_bounds d χ hχ k p).1)
    χ hχ hχmass (fun p => (Riesz.Stationary.gaussianCompactSecondAnchor_bounds d χ hχ k p).2) u

end Riesz.Asymptotics

namespace Riesz.Stationary

theorem exists_nonneg_normalized_compact_anchor (d : ℕ) :
    ∃ χ : C_c(Rd d, ℝ), (∀ x, 0 ≤ χ x) ∧ (∫ x, χ x ∂volume) = 1 := by
  let φ : C_c(Rd d, ℝ) := countingMassCutoff d 1
  have hφnonneg : ∀ x, 0 ≤ φ x := (countingMassCutoff_spec d 1).1
  have hφone : φ (0 : Rd d) = 1 := (countingMassCutoff_spec d 1).2
    (mem_closedBall_zero_iff.mpr ((norm_zero : ‖(0 : Rd d)‖ = 0).le.trans (Nat.cast_nonneg 1)))
  have hI : 0 < ∫ x, φ x ∂volume :=
    integral_pos_of_integrable_nonneg_nonzero (μ := volume) (x := (0 : Rd d))
      φ.continuous φ.integrable hφnonneg (hφone.symm ▸ one_ne_zero)
  exact ⟨(∫ x, φ x ∂volume)⁻¹ • φ,
    fun x => mul_nonneg (inv_nonneg.mpr hI.le) (hφnonneg x),
    (integral_const_mul _ _).trans (inv_mul_cancel₀ hI.ne')⟩

end Riesz.Stationary

namespace Riesz.Asymptotics

/-- The original positive energy bound supplies all moments and simplicity. -/
theorem Q_actual_spherical_positive_energy_limit_le_profile_liminf
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (henergy : ∃ L : ℝ, ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N n) s (x n) ≤ L)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto (fun n => sphereLocalCountingProbability d (N n)
      (sphericalRadius d (N n)) (x n).val) atTop (𝓝 Q)) (u : ℝ) :
    RieszShowcase.Q d (Q.toMeasure.map Subtype.val) u ≤
      atTop.liminf (fun n => ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u)) := by
  have hsfull : -2 < s := by linarith
  have hball : ∀ T : ℝ, 0 < T → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) T)) ^ 2
        ∂(sphereLocalCountingProbability d (N n)
          (sphericalRadius d (N n)) (x n).val).toMeasure) ≤ C :=
    fun T hT => exists_sphereLocalCountingProbability_ball_second_moment_bound_of_energy_bound
      d hd s hsfull hsd hs.ne' N hN x henergy T hT
  obtain ⟨χ, hχ, hχmass⟩ := Riesz.Stationary.exists_nonneg_normalized_compact_anchor d
  exact Q_actual_spherical_limit_le_profile_liminf_of_simple d hd N hN
    (fun n => (x n).val) Q hQ hball
    (sphereLocalCountingProbability_limit_ae_simple_of_positive_energy_bound
      d hd s hs hsd N hN x henergy Q hQ).1 χ hχ hχmass u

theorem gaussianRemainder_le_liminf_sphericalRemainder_of_Q_le_liminf
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n)) (P : ConfigurationLaw d)
    (u : ℝ) (hu : 0 < u)
    (hsharp : RieszShowcase.Q d P u ≤ atTop.liminf (fun n : ℕ =>
      ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u))) :
    gaussianRemainder d P u ≤ atTop.liminf (fun n : ℕ =>
      ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)) := by
  let b : ℝ≥0∞ := ENNReal.ofReal (max (B d u - 1) 0)
  have hcomparison : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u) - b ≤
        ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u) := by
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    have hbg : max (sphericalGaussianBackground d (N n) u - 1) 0 ≤ max (B d u - 1) 0 :=
      max_le_max (sub_le_sub_right (sphericalGaussianBackground_le d (N n) hd hn u hu) 1) le_rfl
    exact (tsub_le_tsub_left (ENNReal.ofReal_le_ofReal hbg) _).trans_eq
      (ENNReal.ofReal_sub _ (le_max_right _ _)).symm
  calc
    gaussianRemainder d P u = RieszShowcase.Q d P u - b := rfl
    _ ≤ (atTop.liminf (fun n : ℕ =>
        ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u))) - b :=
      tsub_le_tsub_right hsharp b
    _ = atTop.liminf (fun n : ℕ =>
        ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u) - b) :=
      (ENNReal.liminf_sub_const atTop _ b).symm
    _ ≤ atTop.liminf (fun n : ℕ =>
        ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)) :=
      Filter.liminf_le_liminf hcomparison

theorem positive_W_le_liminf_scaledSphericalKernelEnergy_of_Q_le_liminf
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n)) (P : ConfigurationLaw d)
    (hsharp : ∀ u : ℝ, 0 < u → RieszShowcase.Q d P u ≤ atTop.liminf (fun n : ℕ =>
      ENNReal.ofReal (sphericalGaussianPairProfile d (N n) (x n).val u))) :
    W d s P ≤ atTop.liminf (fun n : ℕ =>
      (scaledSphericalKernelEnergy d (N n) s (x n) : EReal)) := by
  let g : ℝ≥0∞ := ENNReal.ofReal (gamma_s s)
  let w : ℝ → ℝ≥0∞ := fun u => g * ENNReal.ofReal (u ^ (s / 2 - 1))
  let A : ℕ → ℝ≥0∞ := fun n => g * ∫⁻ u in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (u ^ (s / 2 - 1)) *
      ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)
  let I : ℝ≥0∞ := g * ∫⁻ u in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (u ^ (s / 2 - 1)) * gaussianRemainder d P u
  have hw : Measurable w :=
    measurable_const.mul (measurable_id.pow_const (s / 2 - 1)).ennreal_ofReal
  have hmeas (n : ℕ) : Measurable (fun u : ℝ => w u *
      ENNReal.ofReal (sphericalGaussianRemainder d (N n) (x n).val u)) :=
    hw.mul (((measurable_sphericalGaussianPairProfile d (N n) (x n).val).sub
      (((measurable_sphericalGaussianBackground d (N n) hd).sub
        measurable_const).max measurable_const)).ennreal_ofReal)
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) :
      w u * gaussianRemainder d P u ≤ atTop.liminf (fun n : ℕ =>
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
      (gaussianRemainder_le_liminf_sphericalRemainder_of_Q_le_liminf
        d hd N hN x P u hu (hsharp u hu)) (w u)).trans hmul
  have hFatouRaw : (∫⁻ u in Set.Ioi (0 : ℝ), w u * gaussianRemainder d P u) ≤
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
      ((tendsto_sphericalReferenceConstant d hd s hsd hs.ne').comp hN)).liminf_eq
  have hsfull : -2 < s := by linarith
  have hidentity : ∀ᶠ n : ℕ in atTop,
      (scaledSphericalKernelEnergy d (N n) s (x n) : EReal) =
        (sphericalReferenceConstant d (N n) s : EReal) + (A n : EReal) :=
    (hN.eventually (eventually_spherical_remainder_lintegral_identity d hd s hsfull hsd hs.ne')).mono
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
    W d s P = (c0 d s : EReal) + (I : EReal) := rfl
    _ ≤ atTop.liminf (fun n : ℕ => (sphericalReferenceConstant d (N n) s : EReal)) +
        atTop.liminf (fun n : ℕ => (A n : EReal)) :=
      add_le_add (le_of_eq hc.symm) hFatouE
    _ ≤ atTop.liminf (fun n : ℕ =>
        (sphericalReferenceConstant d (N n) s : EReal) + (A n : EReal)) := hadd
    _ = atTop.liminf (fun n : ℕ => (scaledSphericalKernelEnergy d (N n) s (x n) : EReal)) :=
      Filter.liminf_congr (Filter.EventuallyEq.symm hidentity)

/-- Sharp positive lower bound for the actual limiting law, with no auxiliary anchor assumptions. -/
theorem sphereLocalCountingProbability_limit_W_le_liminf_of_positive_energy_bound
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (x : ∀ n, SphereConfiguration d (N n))
    (henergy : ∃ L : ℝ, ∀ᶠ n : ℕ in atTop,
      scaledSphericalKernelEnergy d (N n) s (x n) ≤ L)
    (Q : ProbabilityMeasure (CountingConfiguration d))
    (hQ : Tendsto (fun n => sphereLocalCountingProbability d (N n)
      (sphericalRadius d (N n)) (x n).val) atTop (𝓝 Q)) :
    W d s (Q.toMeasure.map Subtype.val) ≤ atTop.liminf (fun n : ℕ =>
      (scaledSphericalKernelEnergy d (N n) s (x n) : EReal)) := by
  exact positive_W_le_liminf_scaledSphericalKernelEnergy_of_Q_le_liminf
    d hd s hs hsd N hN x (Q.toMeasure.map Subtype.val)
    (fun u _hu => Q_actual_spherical_positive_energy_limit_le_profile_liminf
      d hd s hs hsd N hN x henergy Q hQ u)

end Riesz.Asymptotics
