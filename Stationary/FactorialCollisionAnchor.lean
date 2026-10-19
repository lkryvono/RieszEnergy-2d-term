import Riesz.Stationary.FactorialEnergy

/-!
Stationary diagonal intensity for the original RMK
factorial measure. This supplies the collision floor used by strict negative
displacement; it does not assert or assume a strict energy comparison.
-/

noncomputable section
open MeasureTheory Filter RieszShowcase Riesz.Configuration
open scoped ENNReal Topology Classical CompactlySupported
namespace Riesz.Stationary

/-- First-coordinate anchor of the actual expected coincident unequal pairs. -/
def factorialCollisionAnchor (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞) :
    Measure (Rd d) :=
  ((expectedFactorialMeasure d P hsecond).restrict {p | p.1 = p.2}).map Prod.fst

private theorem lintegral_factorialCollisionAnchor
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (f : Rd d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂factorialCollisionAnchor d P hsecond) =
      ∫⁻ p, ({p : Rd d × Rd d | p.1 = p.2}).indicator
        (fun p => f p.1) p ∂expectedFactorialMeasure d P hsecond := by
  rw [factorialCollisionAnchor, lintegral_map hf measurable_fst,
    ← lintegral_indicator (measurableSet_eq_fun measurable_fst measurable_snd)]

theorem factorialCollisionAnchor_isAddLeftInvariant
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hstationary : IsStationary d (P.map Subtype.val)) :
    (factorialCollisionAnchor d P hsecond).IsAddLeftInvariant := by
  constructor
  intro a
  apply Measure.ext_of_lintegral (factorialCollisionAnchor d P hsecond)
  intro f hf
  have hadd : Measurable (fun x : Rd d => a + x) := measurable_const.add measurable_id
  rw [lintegral_map hf hadd,
    lintegral_factorialCollisionAnchor d P hsecond (fun x : Rd d => f (a + x)) (hf.comp hadd),
    lintegral_factorialCollisionAnchor d P hsecond f hf]
  let T : Rd d × Rd d → Rd d × Rd d := fun p => (a + p.1, a + p.2)
  let D : Set (Rd d × Rd d) := {p | p.1 = p.2}
  let g : Rd d × Rd d → ℝ≥0∞ := D.indicator (fun p => f p.1)
  have hT : Measurable T :=
    (measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd)
  have hg : Measurable g := (hf.comp measurable_fst).indicator
    (measurableSet_eq_fun measurable_fst measurable_snd)
  have hpoint (p : Rd d × Rd d) :
      D.indicator (fun p => f (a + p.1)) p = g (T p) := by
    simp only [D, g, T, Set.indicator, Set.mem_setOf_eq, add_left_cancel_iff]
  calc
    _ = ∫⁻ p, g (T p) ∂expectedFactorialMeasure d P hsecond := lintegral_congr hpoint
    _ = ∫⁻ p, g p ∂(expectedFactorialMeasure d P hsecond).map T :=
      (lintegral_map hg hT).symm
    _ = _ := by rw [expectedFactorialMeasure_stationary_allCounting d P hsecond hstationary a]

/-- The collision anchor has the actual unit-cube Haar normalization. -/
theorem factorialCollisionAnchor_eq_smul_volume
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hstationary : IsStationary d (P.map Subtype.val)) :
    factorialCollisionAnchor d P hsecond =
      (factorialCollisionAnchor d P hsecond (cube d 1)) • (volume : Measure (Rd d)) := by
  let A := factorialCollisionAnchor d P hsecond
  letI : SFinite A := inferInstanceAs (SFinite
    (((expectedFactorialMeasure d P hsecond).restrict {p | p.1 = p.2}).map Prod.fst))
  letI : A.IsAddLeftInvariant := factorialCollisionAnchor_isAddLeftInvariant d P hsecond hstationary
  apply Measure.ext_of_lintegral ((A (cube d 1)) • (volume : Measure (Rd d)))
  intro f hf
  exact (lintegral_eq_unitCube_mul_lintegral_of_addLeftInvariant d A f hf).trans
    (lintegral_smul_measure (A (cube d 1)) f).symm

/-- Local factorial moments give finite collision mass in the unit cube. -/
theorem factorialCollisionAnchor_unitCube_lt_top
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞) :
    factorialCollisionAnchor d P hsecond (cube d 1) < ∞ := by
  obtain ⟨R, hR⟩ := (Riesz.Negative.cube_isBounded d 1).exists_norm_le
  let K : Set (Rd d) := Metric.closedBall 0 R
  rw [factorialCollisionAnchor,
    Measure.map_apply measurable_fst (Riesz.Negative.measurableSet_cube d 1),
    Measure.restrict_apply ((Riesz.Negative.measurableSet_cube d 1).preimage measurable_fst)]
  refine (measure_mono (show
      Prod.fst ⁻¹' cube d 1 ∩ {p : Rd d × Rd d | p.1 = p.2} ⊆ K ×ˢ K from ?_)).trans_lt
    ((isCompact_closedBall (0 : Rd d) R).prod
      (isCompact_closedBall (0 : Rd d) R)).measure_lt_top
  intro p hp
  have hfirst : p.1 ∈ K := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hR p.1 hp.1
  exact ⟨hfirst, hp.2 ▸ hfirst⟩

private theorem factorialCollisionAnchor_apply_compact_diagonal
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (K : Set (Rd d)) (hK : MeasurableSet K) :
    factorialCollisionAnchor d P hsecond K =
      expectedFactorialMeasure d P hsecond ((fun x : Rd d => (x,x)) '' K) := by
  rw [factorialCollisionAnchor, Measure.map_apply measurable_fst hK,
    Measure.restrict_apply (hK.preimage measurable_fst)]
  congr 1
  ext p
  constructor
  · intro hp
    exact ⟨p.1, hp.1, Prod.ext rfl hp.2⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩

/-- A nonsimple stationary law supplies strictly positive real collision intensity. -/
theorem factorialCollisionAnchor_unitCube_toReal_pos_of_not_ae_simple
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hstationary : IsStationary d (P.map Subtype.val))
    (hnonsimple : ¬ ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val) :
    0 < (factorialCollisionAnchor d P hsecond (cube d 1)).toReal := by
  apply ENNReal.toReal_pos _ (factorialCollisionAnchor_unitCube_lt_top d P hsecond).ne
  intro hzero
  have hAzero : factorialCollisionAnchor d P hsecond = 0 := by
    rw [factorialCollisionAnchor_eq_smul_volume d P hsecond hstationary, hzero, zero_smul]
  apply hnonsimple
  apply ae_isSimpleConfiguration_of_expectedFactorialMeasure_diagonal_zero d P hsecond
  intro n
  rw [← factorialCollisionAnchor_apply_compact_diagonal d P hsecond
    (Metric.closedBall 0 (n : ℝ)) measurableSet_closedBall, hAzero]
  rfl

/-- Every positive-time factorial Gaussian profile contains the collision intensity. -/
theorem factorialCollisionAnchor_unitCube_le_factorialQ
    (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (u : ℝ) :
    factorialCollisionAnchor d P hsecond (cube d 1) ≤ factorialQ d P hsecond u := by
  have hK := Riesz.Negative.measurableSet_cube d 1
  rw [← lintegral_indicator_one hK]
  change (∫⁻ x, (cube d 1).indicator (fun _ : Rd d => (1 : ℝ≥0∞)) x
    ∂factorialCollisionAnchor d P hsecond) ≤ factorialQ d P hsecond u
  rw [lintegral_factorialCollisionAnchor d P hsecond
      ((cube d 1).indicator (fun _ : Rd d => (1 : ℝ≥0∞)))
      (measurable_const.indicator hK), factorialQ]
  apply lintegral_mono
  intro p
  by_cases hp : p.1 = p.2
  · simp [Set.indicator, hp, anchoredGaussianKernel]
  · simp [Set.indicator, hp]

end Riesz.Stationary
