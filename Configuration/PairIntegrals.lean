import Riesz.Configuration.LocalSimplicity

/-! Measurability of pair integrals on simple configuration laws.
Finite restrictions to balls allow the finite-measure product API to be used
before taking the monotone limit over all of Euclidean space. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Configuration

abbrev SimpleMeasure (d : ℕ) := {μ : Measure (Rd d) // IsSimpleConfiguration d μ}

theorem simple_closedBall_isFinite (d n : ℕ) (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ) :
    IsFiniteMeasure (μ.restrict (Metric.closedBall (0 : Rd d) (n : ℝ))) := by
  rcases (simple_locallySimple d μ hμ) n with ⟨N, x, hx, h⟩
  exact h.symm ▸ Riesz.Negative.tupleCounting_isFiniteMeasure d N x

def simpleBallMeasure (d n : ℕ) (μ : SimpleMeasure d) : FiniteMeasure (Rd d) :=
  ⟨μ.val.restrict (Metric.closedBall (0 : Rd d) (n : ℝ)),
    simple_closedBall_isFinite d n μ.val μ.property⟩

theorem measurable_simpleBallMeasure (d n : ℕ) :
    Measurable (simpleBallMeasure d n) := by
  exact ((measurable_restrict d (Metric.closedBall (0 : Rd d) (n : ℝ))
    measurableSet_closedBall).comp measurable_subtype_coe).subtype_mk

theorem simple_isSFinite (d : ℕ) (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ) : SFinite μ := by
  have hl := simple_locallySimple d μ hμ
  letI := (locallySimple_sites_countable d μ hl).toEncodable
  exact (locallySimple_eq_sum d μ hl).symm ▸
    (inferInstance : SFinite (Measure.sum (fun x : atomSites d μ => Measure.dirac x.val)))

theorem closedBall_products_exhaust (d : ℕ) :
    (⋃ n : ℕ, Metric.closedBall (0 : Rd d) (n : ℝ) ×ˢ
      Metric.closedBall (0 : Rd d) (n : ℝ)) = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr (fun p => ?_)
  obtain ⟨n, hn⟩ := exists_nat_ge (max ‖p.1‖ ‖p.2‖)
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  simpa only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right] using
    And.intro ((le_max_left ‖p.1‖ ‖p.2‖).trans hn) ((le_max_right ‖p.1‖ ‖p.2‖).trans hn)

theorem directed_closedBall_products (d : ℕ) :
    Directed (· ⊆ ·) (fun n : ℕ => Metric.closedBall (0 : Rd d) (n : ℝ) ×ˢ
      Metric.closedBall (0 : Rd d) (n : ℝ)) := by
  have hmono : Monotone (fun n : ℕ => Metric.closedBall (0 : Rd d) (n : ℝ) ×ˢ
      Metric.closedBall (0 : Rd d) (n : ℝ)) := fun i j hij => Set.prod_mono
        (Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hij))
        (Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hij))
  exact hmono.directed_le

theorem simple_pair_lintegral_eq_iSup (d : ℕ) (μ : SimpleMeasure d)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ x, ∫⁻ y, k (x, y) ∂μ.val ∂μ.val) =
      ⨆ n : ℕ, ∫⁻ p, k p ∂(simpleBallMeasure d n μ).toMeasure.prod
        (simpleBallMeasure d n μ).toMeasure := by
  letI := simple_isSFinite d μ.val μ.property
  rw [← lintegral_prod k hk.aemeasurable]
  simpa only [closedBall_products_exhaust, Measure.restrict_univ, simpleBallMeasure,
    FiniteMeasure.toMeasure, Measure.prod_restrict] using
      setLIntegral_iUnion_of_directed (μ := μ.val.prod μ.val) k (directed_closedBall_products d)

theorem measurable_simple_pair_lintegral (d : ℕ)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    Measurable (fun μ : SimpleMeasure d => ∫⁻ x, ∫⁻ y, k (x, y) ∂μ.val ∂μ.val) := by
  simp_rw [simple_pair_lintegral_eq_iSup d _ k hk]
  exact Measurable.iSup (fun n => (Measure.measurable_lintegral hk).comp
    (FiniteMeasure.measurable_fun_prod.comp
      ((measurable_simpleBallMeasure d n).prodMk (measurable_simpleBallMeasure d n))))

/-- Pair kernels are measurable almost surely for a law concentrated on simple configurations. -/
theorem aemeasurable_pair_lintegral_of_simple (d : ℕ) (P : ConfigurationLaw d)
    (hP : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    AEMeasurable (fun μ : Measure (Rd d) => ∫⁻ x, ∫⁻ y, k (x, y) ∂μ ∂μ) P := by
  obtain ⟨f, hf, hleft⟩ :=
    (MeasurableEmbedding.subtype_coe (measurableSet_isSimpleConfiguration d)).exists_measurable_extend
      (measurable_simple_pair_lintegral d k hk) (fun _ => ⟨0⟩)
  exact hf.aemeasurable.congr (hP.mono (fun μ hμ => congr_fun hleft ⟨μ, hμ⟩))

end Riesz.Configuration
