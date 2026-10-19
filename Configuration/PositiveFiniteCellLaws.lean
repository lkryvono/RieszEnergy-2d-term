import Riesz.Negative.FiniteSampling
import Riesz.Configuration.PairIntegrals
import Riesz.Stationary.MeanMeasure
import Riesz.Configuration.FiniteProducts
import Mathlib.MeasureTheory.Function.Floor

/-!
# Actual laws used in the positive finite-cell construction

Independent uniform marks retain unit atoms. The resulting finite counting
measures will be combined with a diffuse filler before transport to the sphere.
-/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Negative
open scoped ENNReal Classical

namespace Riesz.Configuration

def windowThinTuple (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) (u : Fin n → unitInterval) : Measure (Rd d) :=
  ∑ i, if (u i : ℝ) < χ (x i) then Measure.dirac (x i) else 0

def windowThinTupleLaw (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) : ConfigurationLaw d :=
  (uniformCellMarks n).map (windowThinTuple d n χ x)

theorem measurable_windowThinTuple_marks (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) : Measurable (windowThinTuple d n χ x) := by
  refine Finset.measurable_fun_sum _ (fun i _ => ?_)
  exact Measurable.ite
    (measurableSet_lt (measurable_subtype_coe.comp (measurable_pi_apply i))
      measurable_const) measurable_const measurable_const

theorem windowThinTupleLaw_probability (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) : IsProbabilityMeasure (windowThinTupleLaw d n χ x) := by
  exact Measure.isProbabilityMeasure_map
    (measurable_windowThinTuple_marks d n χ x).aemeasurable

theorem measurable_windowThinTuple_joint (d n : ℕ) (χ : Rd d → ℝ)
    (hχ : Measurable χ) :
    Measurable (fun p : (Fin n → Rd d) × (Fin n → unitInterval) =>
      windowThinTuple d n χ p.1 p.2) := by
  exact Finset.measurable_fun_sum _ (fun i _ =>
    Measurable.ite
      (measurableSet_lt
        (measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_snd))
        (hχ.comp ((measurable_pi_apply i).comp measurable_fst)))
      (Measure.measurable_dirac.comp ((measurable_pi_apply i).comp measurable_fst))
      measurable_const)

theorem unitInterval_threshold_lintegral (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (c : ℝ≥0∞) :
    (∫⁻ u : unitInterval, if (u : ℝ) < a then c else 0) = ENNReal.ofReal a * c := by
  let p : unitInterval := ⟨a, ha, ha1⟩
  change (∫⁻ u : unitInterval, (Set.Iio p).indicator (fun _ => c) u) = _
  rw [lintegral_indicator_const measurableSet_Iio, unitInterval.volume_Iio]
  exact mul_comm c (ENNReal.ofReal a)

theorem uniformMarks_threshold_lintegral (n : ℕ) (i : Fin n)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (c : ℝ≥0∞) :
    (∫⁻ u, if (u i : ℝ) < a then c else 0 ∂uniformCellMarks n) =
      ENNReal.ofReal a * c := by
  exact ((measurePreserving_eval
    (fun _ : Fin n => (volume : Measure unitInterval)) i).lintegral_comp
      (Measurable.ite
        (measurableSet_lt measurable_subtype_coe measurable_const)
        measurable_const measurable_const)).trans
          (unitInterval_threshold_lintegral a ha ha1 c)

theorem uniformMarks_pair_map (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (uniformCellMarks n).map (fun u => (u i, u j)) =
      (volume : Measure unitInterval).prod (volume : Measure unitInterval) := by
  simpa only [uniformCellMarks,
    (measurePreserving_eval (fun _ : Fin n => (volume : Measure unitInterval)) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => (volume : Measure unitInterval)) j).map_eq]
    using ((ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin n => (volume : Measure unitInterval))
      (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij).map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable

theorem uniformMarks_pair_threshold_lintegral (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (c : ℝ≥0∞) :
    (∫⁻ u, if (u i : ℝ) < a then
        (if (u j : ℝ) < b then c else 0) else 0 ∂uniformCellMarks n) =
      ENNReal.ofReal a * ENNReal.ofReal b * c := by
  let f : unitInterval × unitInterval → ℝ≥0∞ := fun p =>
    if (p.1 : ℝ) < a then (if (p.2 : ℝ) < b then c else 0) else 0
  have hf : Measurable f := Measurable.ite
    (measurableSet_lt (measurable_subtype_coe.comp measurable_fst) measurable_const)
    (Measurable.ite
      (measurableSet_lt (measurable_subtype_coe.comp measurable_snd) measurable_const)
      measurable_const measurable_const) measurable_const
  calc
    _ = ∫⁻ p, f p ∂(volume : Measure unitInterval).prod
        (volume : Measure unitInterval) := by
      rw [← uniformMarks_pair_map n i j hij,
        lintegral_map hf ((measurable_pi_apply i).prodMk (measurable_pi_apply j))]
    _ = ∫⁻ u : unitInterval, ∫⁻ v : unitInterval, f (u, v) :=
      lintegral_prod f hf.aemeasurable
    _ = ∫⁻ u : unitInterval,
        if (u : ℝ) < a then ENNReal.ofReal b * c else 0 := by
      refine lintegral_congr (fun u => ?_)
      by_cases hu : (u : ℝ) < a
      · simpa only [f, if_pos hu] using unitInterval_threshold_lintegral b hb hb1 c
      · simp only [f, if_neg hu, lintegral_zero]
    _ = _ := by rw [unitInterval_threshold_lintegral a ha ha1, mul_assoc]

def windowPairIntegral (d : ℕ) (k : Rd d × Rd d → ℝ≥0∞)
    (μ : Measure (Rd d)) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, if x = y then 0 else k (x, y) ∂μ ∂μ

theorem lintegral_windowThinTuple (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) (u : Fin n → unitInterval) (f : Rd d → ℝ≥0∞) :
    (∫⁻ z, f z ∂windowThinTuple d n χ x u) =
      ∑ i, if (u i : ℝ) < χ (x i) then f (x i) else 0 := by
  rw [windowThinTuple, lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [apply_ite (fun μ : Measure (Rd d) => ∫⁻ z, f z ∂μ),
    lintegral_dirac, lintegral_zero_measure]

theorem windowThinTuple_pair_expansion (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) (hx : Function.Injective x) (u : Fin n → unitInterval)
    (k : Rd d × Rd d → ℝ≥0∞) :
    windowPairIntegral d k (windowThinTuple d n χ x u) =
      ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else
        (if (u i : ℝ) < χ (x i) then
          (if (u j : ℝ) < χ (x j) then k (x i, x j) else 0) else 0) := by
  simp only [windowPairIntegral, lintegral_windowThinTuple, Finset.ite_sum_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte, ite_self]
  · simp only [if_neg hij, if_neg (fun h => hij (hx h))]

theorem windowThinTuple_expected_pair (d n : ℕ) (χ : Rd d → ℝ)
    (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (x : Fin n → Rd d) (hx : Function.Injective x) (k : Rd d × Rd d → ℝ≥0∞) :
    (∫⁻ u, windowPairIntegral d k (windowThinTuple d n χ x u) ∂uniformCellMarks n) =
      ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else
        ENNReal.ofReal (χ (x i)) * ENNReal.ofReal (χ (x j)) * k (x i, x j) := by
  let term (i j : Fin n) (u : Fin n → unitInterval) : ℝ≥0∞ :=
    if i = j then 0 else (if (u i : ℝ) < χ (x i) then
      (if (u j : ℝ) < χ (x j) then k (x i, x j) else 0) else 0)
  have hm (i j : Fin n) : Measurable (term i j) :=
    Measurable.ite (measurableSet_eq_fun measurable_const measurable_const)
      measurable_const
      (Measurable.ite
        (measurableSet_lt (measurable_subtype_coe.comp (measurable_pi_apply i))
          measurable_const)
        (Measurable.ite
          (measurableSet_lt (measurable_subtype_coe.comp (measurable_pi_apply j))
            measurable_const) measurable_const measurable_const) measurable_const)
  have hfun : (fun u => windowPairIntegral d k (windowThinTuple d n χ x u)) =
      (fun u => ∑ i : Fin n, ∑ j : Fin n, term i j u) :=
    funext (fun u => windowThinTuple_pair_expansion d n χ x hx u k)
  rw [hfun, lintegral_finsetSum Finset.univ
    (fun i _ => Finset.measurable_fun_sum _ (fun j _ => hm i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [lintegral_finsetSum Finset.univ (fun j _ => hm i j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hij : i = j
  · simp only [term, if_pos hij, lintegral_zero]
  · simpa only [term, if_neg hij] using
      uniformMarks_pair_threshold_lintegral n i j hij (χ (x i)) (χ (x j))
        (hχ (x i)).1 (hχ (x i)).2 (hχ (x j)).1 (hχ (x j)).2 (k (x i, x j))

theorem windowThinTuple_representation (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) (hx : Function.Injective x) (u : Fin n → unitInterval) :
    ∃ m : ℕ, ∃ y : Fin m → Rd d, Function.Injective y ∧
      windowThinTuple d n χ x u = tupleCounting d m y := by
  let J := {i : Fin n // (u i : ℝ) < χ (x i)}
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun k => x (e k).val,
    hx.comp (Subtype.val_injective.comp e.injective), ?_⟩
  change (∑ i : Fin n, if (u i : ℝ) < χ (x i) then Measure.dirac (x i) else 0) =
    ∑ k : Fin (Fintype.card J), Measure.dirac (x (e k).val)
  rw [← Finset.sum_filter,
    Finset.sum_subtype (p := fun i => (u i : ℝ) < χ (x i))
      (F := inferInstance) _ (by simp)]
  exact (e.sum_comp (fun i : J => Measure.dirac (x i.val))).symm

theorem windowThinTuple_simple (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) (hx : Function.Injective x) (u : Fin n → unitInterval) :
    IsSimpleConfiguration d (windowThinTuple d n χ x u) := by
  exact (windowThinTuple_representation d n χ x hx u).elim (fun m hm =>
    hm.elim (fun y hy => hy.2.symm ▸ tupleCounting_simple d m y hy.1))

theorem windowThinTupleLaw_simple_ae (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) (hx : Function.Injective x) :
    ∀ᵐ μ ∂windowThinTupleLaw d n χ x, IsSimpleConfiguration d μ := by
  exact (ae_map_iff (measurable_windowThinTuple_marks d n χ x).aemeasurable
    (measurableSet_isSimpleConfiguration d)).mpr
      (Filter.Eventually.of_forall (fun u => windowThinTuple_simple d n χ x hx u))

theorem aemeasurable_windowPairIntegral_of_simple (d : ℕ) (Q : ConfigurationLaw d)
    (hQ : ∀ᵐ μ ∂Q, IsSimpleConfiguration d μ)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    AEMeasurable (windowPairIntegral d k) Q := by
  exact aemeasurable_pair_lintegral_of_simple d Q hQ
    (fun p => if p.1 = p.2 then 0 else k p)
    (Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd)
      measurable_const hk)

def windowWeightedKernel (d : ℕ) (χ : Rd d → ℝ)
    (k : Rd d × Rd d → ℝ≥0∞) (p : Rd d × Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (χ p.1) * ENNReal.ofReal (χ p.2) * k p

theorem windowThinTupleLaw_pair (d n : ℕ) (χ : Rd d → ℝ)
    (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) (x : Fin n → Rd d)
    (hx : Function.Injective x) (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ μ, windowPairIntegral d k μ ∂windowThinTupleLaw d n χ x) =
      windowPairIntegral d (windowWeightedKernel d χ k) (tupleCounting d n x) := by
  have hm := aemeasurable_windowPairIntegral_of_simple d (windowThinTupleLaw d n χ x)
    (windowThinTupleLaw_simple_ae d n χ x hx) k hk
  calc
    _ = ∫⁻ u, windowPairIntegral d k (windowThinTuple d n χ x u)
        ∂uniformCellMarks n :=
      lintegral_map' hm (measurable_windowThinTuple_marks d n χ x).aemeasurable
    _ = ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else
        ENNReal.ofReal (χ (x i)) * ENNReal.ofReal (χ (x j)) * k (x i, x j) :=
      windowThinTuple_expected_pair d n χ hχ x hx k
    _ = _ := by
      simp only [windowPairIntegral, tupleCounting, lintegral_finsetSum_measure,
        lintegral_dirac, windowWeightedKernel, hx.eq_iff]

theorem windowThinTuple_expected_first (d n : ℕ) (χ : Rd d → ℝ)
    (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) (x : Fin n → Rd d) (D : Set (Rd d)) :
    (∫⁻ u, windowThinTuple d n χ x u D ∂uniformCellMarks n) =
      ∑ i, ENNReal.ofReal (χ (x i)) * Measure.dirac (x i) D := by
  simp only [windowThinTuple, Measure.finsetSum_apply,
    apply_ite (fun μ : Measure (Rd d) => μ D), Measure.coe_zero, Pi.zero_apply]
  rw [lintegral_finsetSum (μ := uniformCellMarks n)
    (f := fun (i : Fin n) (u : Fin n → unitInterval) =>
      if (u i : ℝ) < χ (x i) then Measure.dirac (x i) D else 0)
    Finset.univ (fun i _ => Measurable.ite
    (measurableSet_lt (measurable_subtype_coe.comp (measurable_pi_apply i))
      measurable_const) measurable_const measurable_const)]
  exact Finset.sum_congr rfl (fun i _ => uniformMarks_threshold_lintegral n i
    (χ (x i)) (hχ (x i)).1 (hχ (x i)).2 (Measure.dirac (x i) D))

theorem measurable_parametric_map
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (ρ : Measure B) [SFinite ρ] (f : A × B → C) (hf : Measurable f) :
    Measurable (fun a => ρ.map (fun b => f (a, b))) := by
  refine Measure.measurable_of_measurable_coe _ (fun D hD => ?_)
  have hm : Measurable (fun p : A × B =>
      D.indicator (fun _ => (1 : ℝ≥0∞)) (f p)) :=
    (measurable_const.indicator hD).comp hf
  convert hm.lintegral_prod_right' (ν := ρ) using 1
  funext a
  have hfa : Measurable (fun b => f (a, b)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  simpa only [Measure.map_apply hfa hD, one_mul] using
    (lintegral_indicator_const_comp hfa hD (1 : ℝ≥0∞)).symm

theorem measurable_windowThinTupleLaw (d n : ℕ) (χ : Rd d → ℝ)
    (hχ : Measurable χ) : Measurable (windowThinTupleLaw d n χ) := by
  exact measurable_parametric_map (uniformCellMarks n) _
    (measurable_windowThinTuple_joint d n χ hχ)

def windowLabel (d n : ℕ) : Measure (Rd d) → (Fin n → Rd d) :=
  Classical.choose (exists_measurable_label d n)

theorem measurable_windowLabel (d n : ℕ) : Measurable (windowLabel d n) :=
  (Classical.choose_spec (exists_measurable_label d n)).1

theorem windowLabel_spec (d n : ℕ) (μ : Measure (Rd d))
    (hμ : ∃ x : Fin n → Rd d, Function.Injective x ∧ μ = tupleCounting d n x) :
    Function.Injective (windowLabel d n μ) ∧ tupleCounting d n (windowLabel d n μ) = μ :=
  (Classical.choose_spec (exists_measurable_label d n)).2 μ hμ

def windowInputCount (d : ℕ) (K : Set (Rd d)) (μ : Measure (Rd d)) : ℕ :=
  ⌊(μ K).toReal⌋₊

theorem measurable_windowInputCount (d : ℕ) (K : Set (Rd d)) (hK : MeasurableSet K) :
    Measurable (windowInputCount d K) :=
  (Measure.measurable_coe hK).ennreal_toReal.nat_floor

def fixedWindowThinLaw (d n : ℕ) (K : Set (Rd d)) (χ : Rd d → ℝ)
    (μ : Measure (Rd d)) : ConfigurationLaw d :=
  windowThinTupleLaw d n χ (windowLabel d n (μ.restrict K))

theorem measurable_fixedWindowThinLaw (d n : ℕ) (K : Set (Rd d))
    (hK : MeasurableSet K) (χ : Rd d → ℝ) (hχ : Measurable χ) :
    Measurable (fixedWindowThinLaw d n K χ) :=
  (measurable_windowThinTupleLaw d n χ hχ).comp
    ((measurable_windowLabel d n).comp (measurable_restrict d K hK))

def windowThinKernel (d : ℕ) (K : Set (Rd d)) (χ : Rd d → ℝ)
    (μ : Measure (Rd d)) : ConfigurationLaw d :=
  fixedWindowThinLaw d (windowInputCount d K μ) K χ μ

theorem measurable_windowThinKernel (d : ℕ) (K : Set (Rd d))
    (hK : MeasurableSet K) (χ : Rd d → ℝ) (hχ : Measurable χ) :
    Measurable (windowThinKernel d K χ) := by
  have hfamily : Measurable (fun p : Measure (Rd d) × ℕ =>
      fixedWindowThinLaw d p.2 K χ p.1) :=
    measurable_from_prod_countable_left
      (fun n => measurable_fixedWindowThinLaw d n K hK χ hχ)
  exact hfamily.comp (measurable_id.prodMk (measurable_windowInputCount d K hK))

theorem windowThinKernel_probability (d : ℕ) (K : Set (Rd d))
    (χ : Rd d → ℝ) (μ : Measure (Rd d)) :
    IsProbabilityMeasure (windowThinKernel d K χ μ) :=
  windowThinTupleLaw_probability d _ χ _

def finiteWindowThinningLaw (d : ℕ) (P : ConfigurationLaw d)
    (K : Set (Rd d)) (χ : Rd d → ℝ) : ConfigurationLaw d :=
  P.bind (windowThinKernel d K χ)

theorem finiteWindowThinningLaw_probability (d : ℕ) (P : ConfigurationLaw d)
    [IsProbabilityMeasure P] (K : Set (Rd d)) (hK : MeasurableSet K)
    (χ : Rd d → ℝ) (hχ : Measurable χ) :
    IsProbabilityMeasure (finiteWindowThinningLaw d P K χ) := by
  letI : ∀ μ, IsProbabilityMeasure (windowThinKernel d K χ μ) :=
    fun μ => windowThinKernel_probability d K χ μ
  refine ⟨?_⟩
  simp only [finiteWindowThinningLaw, Measure.bind_apply MeasurableSet.univ
    (measurable_windowThinKernel d K hK χ hχ).aemeasurable,
    measure_univ, lintegral_one]

theorem simple_compact_restrict_representation (d : ℕ)
    (μ : Measure (Rd d)) (hμ : IsSimpleConfiguration d μ)
    (K : Set (Rd d)) (hK : IsCompact K) :
    ∃ n : ℕ, ∃ x : Fin n → Rd d, Function.Injective x ∧
      μ.restrict K = tupleCounting d n x ∧ ∀ i, x i ∈ K := by
  rcases hμ with ⟨S, hS, rfl⟩
  letI := (hS K hK).fintype
  let e : Fin (Fintype.card ↥(S ∩ K)) ≃ ↥(S ∩ K) := (Fintype.equivFin ↥(S ∩ K)).symm
  refine ⟨Fintype.card ↥(S ∩ K), fun i => (e i).val,
    Subtype.val_injective.comp e.injective,
    (restrict_sum_dirac d S K hK.measurableSet).trans ?_, fun i => (e i).property.2⟩
  simpa only [Measure.sum_fintype, Function.comp_def, tupleCounting] using
    (Measure.sum_comp_equiv e (fun z : ↥(S ∩ K) => Measure.dirac z.val)).symm

theorem window_selected_label_spec (d : ℕ) (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ) (K : Set (Rd d)) (hK : IsCompact K) :
    Function.Injective (windowLabel d (windowInputCount d K μ) (μ.restrict K)) ∧
      tupleCounting d (windowInputCount d K μ)
        (windowLabel d (windowInputCount d K μ) (μ.restrict K)) = μ.restrict K ∧
      ∀ i, windowLabel d (windowInputCount d K μ) (μ.restrict K) i ∈ K := by
  obtain ⟨n, x, hx, hrep, hxK⟩ := simple_compact_restrict_representation d μ hμ K hK
  have hmass : μ K = (n : ℝ≥0∞) := by
    simpa only [Measure.restrict_apply_univ, tupleCounting_univ] using
      congrArg (fun ρ : Measure (Rd d) => ρ Set.univ) hrep
  have hn : windowInputCount d K μ = n := by simp [windowInputCount, hmass]
  rw [hn]
  have hl := windowLabel_spec d n (μ.restrict K) ⟨x, hx, hrep⟩
  refine ⟨hl.1, hl.2,
    (tupleCounting_compl_eq_zero_iff d n _ K hK.measurableSet).mp ?_⟩
  simp only [hl.2, Measure.restrict_apply hK.measurableSet.compl,
    Set.compl_inter_self, measure_empty]

theorem windowThinKernel_pair (d : ℕ) (K : Set (Rd d)) (hK : IsCompact K)
    (χ : Rd d → ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (μ : Measure (Rd d)) (hμ : IsSimpleConfiguration d μ)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ ν, windowPairIntegral d k ν ∂windowThinKernel d K χ μ) =
      windowPairIntegral d (windowWeightedKernel d χ k) (μ.restrict K) := by
  have hl := window_selected_label_spec d μ hμ K hK
  exact (windowThinTupleLaw_pair d _ χ hχ _ hl.1 k hk).trans
    (congrArg (windowPairIntegral d (windowWeightedKernel d χ k)) hl.2.1)

theorem windowThinTuple_le (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) (u : Fin n → unitInterval) :
    windowThinTuple d n χ x u ≤ tupleCounting d n x := by
  refine Finset.sum_le_sum (fun i _ => ?_)
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem windowThinTuple_univ_lt_top (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) (u : Fin n → unitInterval) :
    windowThinTuple d n χ x u Set.univ < ∞ := by
  exact ((windowThinTuple_le d n χ x u) Set.univ).trans_lt
    ((tupleCounting_univ d n x).trans_lt (ENNReal.natCast_lt_top n))

theorem windowThinTuple_concentrated (d n : ℕ) (χ : Rd d → ℝ)
    (x : Fin n → Rd d) (u : Fin n → unitInterval)
    (K : Set (Rd d)) (hK : MeasurableSet K) (hxK : ∀ i, x i ∈ K) :
    windowThinTuple d n χ x u Kᶜ = 0 := by
  exact le_antisymm
    (((windowThinTuple_le d n χ x u) Kᶜ).trans_eq
      ((tupleCounting_compl_eq_zero_iff d n x K hK).mpr hxK)) bot_le

theorem measurableSet_windowFiniteGood (d : ℕ) (K : Set (Rd d)) (hK : MeasurableSet K) :
    MeasurableSet {ν : Measure (Rd d) | IsSimpleConfiguration d ν ∧
      ν Kᶜ = 0 ∧ ν Set.univ < ∞} :=
  (measurableSet_isSimpleConfiguration d).inter
    ((measurableSet_eq_fun (Measure.measurable_coe hK.compl) measurable_const).inter
      (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const))

theorem windowThinKernel_good (d : ℕ) (K : Set (Rd d)) (hK : IsCompact K)
    (χ : Rd d → ℝ) (μ : Measure (Rd d)) (hμ : IsSimpleConfiguration d μ) :
    ∀ᵐ ν ∂windowThinKernel d K χ μ, IsSimpleConfiguration d ν ∧
      ν Kᶜ = 0 ∧ ν Set.univ < ∞ := by
  have hl := window_selected_label_spec d μ hμ K hK
  exact (ae_map_iff (measurable_windowThinTuple_marks d _ χ _).aemeasurable
    (measurableSet_windowFiniteGood d K hK.measurableSet)).mpr
      (Filter.Eventually.of_forall (fun u =>
        ⟨windowThinTuple_simple d _ χ _ hl.1 u,
          windowThinTuple_concentrated d _ χ _ u K hK.measurableSet hl.2.2,
          windowThinTuple_univ_lt_top d _ χ _ u⟩))

theorem ae_bind_of_ae_ae
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) (T : A → Measure B) (hT : Measurable T)
    (Good : B → Prop) (hGood : MeasurableSet {b | Good b})
    (h : ∀ᵐ a ∂P, ∀ᵐ b ∂T a, Good b) : ∀ᵐ b ∂P.bind T, Good b := by
  rw [ae_iff, Measure.bind_apply (s := {b | ¬Good b}) hGood.compl hT.aemeasurable]
  exact lintegral_eq_zero_of_ae_eq_zero (h.mono (fun a ha => ae_iff.mp ha))

theorem finiteWindowThinningLaw_good (d : ℕ) (P : ConfigurationLaw d)
    (hP : Admissible d P) (K : Set (Rd d)) (hK : IsCompact K)
    (χ : Rd d → ℝ) (hχ : Measurable χ) :
    ∀ᵐ ν ∂finiteWindowThinningLaw d P K χ, IsSimpleConfiguration d ν ∧
      ν Kᶜ = 0 ∧ ν Set.univ < ∞ := by
  exact ae_bind_of_ae_ae P (windowThinKernel d K χ)
    (measurable_windowThinKernel d K hK.measurableSet χ hχ) _
    (measurableSet_windowFiniteGood d K hK.measurableSet)
    (hP.2.1.mono (fun μ hμ => windowThinKernel_good d K hK χ μ hμ))

theorem lintegral_restrict_eq_of_zero_compl
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : Set X)
    (_hK : MeasurableSet K) (f : X → ℝ≥0∞) (hf : ∀ x ∉ K, f x = 0) :
    (∫⁻ x, f x ∂μ.restrict K) = ∫⁻ x, f x ∂μ := by
  exact setLIntegral_eq_of_support_subset (Function.support_subset_iff'.mpr hf)

theorem windowWeightedPair_restrict_eq (d : ℕ) (μ : Measure (Rd d))
    (K : Set (Rd d)) (hK : MeasurableSet K) (χ : Rd d → ℝ)
    (hzero : ∀ x ∉ K, χ x = 0) (k : Rd d × Rd d → ℝ≥0∞) :
    windowPairIntegral d (windowWeightedKernel d χ k) (μ.restrict K) =
      windowPairIntegral d (windowWeightedKernel d χ k) μ := by
  have hinner (x : Rd d) :
      (∫⁻ y, if x = y then 0 else windowWeightedKernel d χ k (x, y) ∂μ.restrict K) =
        ∫⁻ y, if x = y then 0 else windowWeightedKernel d χ k (x, y) ∂μ :=
    lintegral_restrict_eq_of_zero_compl μ K hK _ (fun y hy => by
      simp only [windowWeightedKernel, hzero y hy, ENNReal.ofReal_zero,
        mul_zero, zero_mul, ite_self])
  simp only [windowPairIntegral, hinner]
  exact lintegral_restrict_eq_of_zero_compl μ K hK _ (fun x hx => by
    simp only [windowWeightedKernel, hzero x hx, ENNReal.ofReal_zero,
      zero_mul, ite_self, lintegral_zero])

theorem finiteWindowThinningLaw_pair_lintegral
    (d : ℕ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (K : Set (Rd d)) (hK : IsCompact K) (χ : Rd d → ℝ)
    (hχ : Measurable χ) (hbound : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hzero : ∀ x ∉ K, χ x = 0)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ ν, windowPairIntegral d k ν ∂finiteWindowThinningLaw d P K χ) =
      ∫⁻ μ, windowPairIntegral d (windowWeightedKernel d χ k) μ ∂P := by
  have hprofile := aemeasurable_windowPairIntegral_of_simple d
    (finiteWindowThinningLaw d P K χ)
    ((finiteWindowThinningLaw_good d P hP K hK χ hχ).mono (fun _ h => h.1)) k hk
  rw [finiteWindowThinningLaw, Measure.lintegral_bind
    (measurable_windowThinKernel d K hK.measurableSet χ hχ).aemeasurable hprofile]
  exact lintegral_congr_ae (hP.2.1.mono (fun μ hμ =>
    (windowThinKernel_pair d K hK χ hbound μ hμ k hk).trans
      (windowWeightedPair_restrict_eq d μ K hK.measurableSet χ hzero k)))

theorem windowThinKernel_first (d : ℕ) (K : Set (Rd d)) (hK : IsCompact K)
    (χ : Rd d → ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (μ : Measure (Rd d)) (hμ : IsSimpleConfiguration d μ)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ ν, ν D ∂windowThinKernel d K χ μ) =
      ∫⁻ x, ENNReal.ofReal (χ x) * D.indicator (fun _ => 1) x ∂μ.restrict K := by
  have hl := window_selected_label_spec d μ hμ K hK
  let n := windowInputCount d K μ
  let x := windowLabel d n (μ.restrict K)
  calc
    _ = ∫⁻ u, windowThinTuple d n χ x u D ∂uniformCellMarks n :=
      lintegral_map (Measure.measurable_coe hD) (measurable_windowThinTuple_marks d n χ x)
    _ = ∑ i, ENNReal.ofReal (χ (x i)) * Measure.dirac (x i) D :=
      windowThinTuple_expected_first d n χ hχ x D
    _ = ∫⁻ z, ENNReal.ofReal (χ z) * D.indicator (fun _ => 1) z
        ∂tupleCounting d n x := by
      simp only [tupleCounting, lintegral_finsetSum_measure, lintegral_dirac,
        Measure.dirac_apply' _ hD, Set.indicator, Pi.one_apply]
    _ = _ := congrArg
      (fun ρ : Measure (Rd d) => ∫⁻ z, ENNReal.ofReal (χ z) * D.indicator (fun _ => 1) z ∂ρ)
      hl.2.1

theorem finiteWindowThinningLaw_mean (d : ℕ) (P : ConfigurationLaw d)
    (hP : Admissible d P) (K : Set (Rd d)) (hK : IsCompact K)
    (χ : Rd d → ℝ) (hχ : Measurable χ)
    (hbound : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hzero : ∀ x ∉ K, χ x = 0)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ ν, ν D ∂finiteWindowThinningLaw d P K χ) =
      (volume.withDensity (fun x => ENNReal.ofReal (χ x)) : Measure (Rd d)) D := by
  let f : Rd d → ℝ≥0∞ := fun x => ENNReal.ofReal (χ x) * D.indicator (fun _ => 1) x
  have hf : Measurable f := hχ.ennreal_ofReal.mul (measurable_const.indicator hD)
  rw [finiteWindowThinningLaw, Measure.lintegral_bind
    (measurable_windowThinKernel d K hK.measurableSet χ hχ).aemeasurable
    (Measure.measurable_coe hD).aemeasurable]
  calc
    _ = ∫⁻ μ, ∫⁻ x, f x ∂μ ∂P := lintegral_congr_ae (hP.2.1.mono (fun μ hμ =>
      (windowThinKernel_first d K hK χ hbound μ hμ D hD).trans
        (lintegral_restrict_eq_of_zero_compl μ K hK.measurableSet f (fun x hx => by
          simp only [f, hzero x hx, ENNReal.ofReal_zero, zero_mul]))))
    _ = ∫⁻ x, f x ∂P.join := (Measure.lintegral_join hf.aemeasurable).symm
    _ = _ := by
      rw [Riesz.Stationary.join_eq_volume_of_admissible d P hP,
        withDensity_apply _ hD, ← lintegral_indicator hD]
      simp only [f, Set.indicator, mul_ite, mul_one, mul_zero]

theorem windowThinKernel_countSquare_bound (d : ℕ) (K : Set (Rd d)) (hK : IsCompact K)
    (χ : Rd d → ℝ) (μ : Measure (Rd d)) (hμ : IsSimpleConfiguration d μ) :
    (∫⁻ ν, (ν Set.univ) ^ (2 : ℕ) ∂windowThinKernel d K χ μ) ≤ (μ K) ^ (2 : ℕ) := by
  have hl := window_selected_label_spec d μ hμ K hK
  have hmass : tupleCounting d (windowInputCount d K μ)
      (windowLabel d (windowInputCount d K μ) (μ.restrict K)) Set.univ = μ K := by
    rw [hl.2.1, Measure.restrict_apply_univ]
  rw [windowThinKernel, fixedWindowThinLaw, windowThinTupleLaw,
    lintegral_map ((Measure.measurable_coe MeasurableSet.univ).pow_const 2)
      (measurable_windowThinTuple_marks d (windowInputCount d K μ) χ
        (windowLabel d (windowInputCount d K μ) (μ.restrict K)))]
  calc
    _ ≤ ∫⁻ _u : Fin (windowInputCount d K μ) → unitInterval,
        (μ K)^2 ∂uniformCellMarks (windowInputCount d K μ) :=
      lintegral_mono (fun u => pow_le_pow_left'
        (((windowThinTuple_le d _ χ _ u) Set.univ).trans_eq hmass) 2)
    _ = _ := by simp only [lintegral_const, measure_univ, mul_one]

theorem finiteWindowThinningLaw_secondMoment (d : ℕ) (P : ConfigurationLaw d)
    (hP : Admissible d P) (K : Set (Rd d)) (hK : IsCompact K)
    (χ : Rd d → ℝ) (hχ : Measurable χ) :
    (∫⁻ ν, (ν Set.univ) ^ (2 : ℕ) ∂finiteWindowThinningLaw d P K χ) < ∞ := by
  rw [finiteWindowThinningLaw, Measure.lintegral_bind
    (measurable_windowThinKernel d K hK.measurableSet χ hχ).aemeasurable
    ((Measure.measurable_coe MeasurableSet.univ).pow_const 2).aemeasurable]
  exact (lintegral_mono_ae (hP.2.1.mono (fun μ hμ =>
    windowThinKernel_countSquare_bound d K hK χ μ hμ))).trans_lt
      (hP.2.2.2.2 K hK.measurableSet hK.isBounded)

theorem iid_pi_pair_map (d n : ℕ) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (i j : Fin n) (hij : i ≠ j) :
    Measure.map (fun x : Fin n → Rd d => (x i, x j))
      (Measure.pi (fun _ : Fin n => ρ)) = ρ.prod ρ := by
  simpa only [(measurePreserving_eval (fun _ : Fin n => ρ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => ρ) j).map_eq]
    using ((ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin n => ρ) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hij).map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable

theorem tupleCounting_offSite_lintegral (d n : ℕ) (x : Fin n → Rd d)
    (hx : Function.Injective x) (k : Rd d × Rd d → ℝ≥0∞) :
    windowPairIntegral d k (tupleCounting d n x) =
      ∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, k (x i, x j) := by
  simp only [windowPairIntegral, tupleCounting, lintegral_finsetSum_measure,
    lintegral_dirac, hx.eq_iff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_erase Finset.univ
    (f := fun j : Fin n => if i = j then 0 else k (x i, x j))
    (a := i) (if_pos rfl)]
  exact Finset.sum_congr rfl (fun j hj => if_neg (Ne.symm (Finset.ne_of_mem_erase hj)))

theorem sum_erase_const_ennreal (n : ℕ) (c : ℝ≥0∞) :
    (∑ i : Fin n, ∑ _j ∈ (Finset.univ : Finset (Fin n)).erase i, c) =
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * c := by
  simp [Finset.card_erase_of_mem, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

theorem iidCountingLaw_pair_lintegral (d n : ℕ) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] [NullSingletonClass ρ]
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ μ, windowPairIntegral d k μ ∂iidCountingLaw d n ρ) =
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ∫⁻ p, k p ∂ρ.prod ρ := by
  have hsimple : ∀ᵐ μ ∂iidCountingLaw d n ρ, IsSimpleConfiguration d μ :=
    ((iidCountingLaw_spec d n ρ Set.univ MeasurableSet.univ (by simp)).2.1).mono
      (fun _ h => h.1)
  calc
    _ = ∫⁻ x, windowPairIntegral d k (tupleCounting d n x)
        ∂Measure.pi (fun _ : Fin n => ρ) :=
      lintegral_map'
        (aemeasurable_windowPairIntegral_of_simple d (iidCountingLaw d n ρ) hsimple k hk)
        (measurable_tupleCounting d n).aemeasurable
    _ = ∫⁻ x, ∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        k (x i, x j) ∂Measure.pi (fun _ : Fin n => ρ) :=
      lintegral_congr_ae ((ae_injective_pi d n ρ).mono
        (fun x hx => tupleCounting_offSite_lintegral d n x hx k))
    _ = ∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        ∫⁻ x, k (x i, x j) ∂Measure.pi (fun _ : Fin n => ρ) := by
      exact (lintegral_finsetSum
        (f := fun (i : Fin n) (x : Fin n → Rd d) =>
          ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, k (x i, x j))
        Finset.univ (fun i _ => Finset.measurable_fun_sum _ (fun j _ =>
          hk.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))))).trans
        (Finset.sum_congr rfl (fun i _ => lintegral_finsetSum _ (fun j _ =>
          hk.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j)))))
    _ = ∑ i : Fin n, ∑ _j ∈ (Finset.univ : Finset (Fin n)).erase i,
        ∫⁻ p, k p ∂ρ.prod ρ := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j hj => ?_))
      exact (lintegral_map hk
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).symm.trans
          (congrArg (fun m : Measure (Rd d × Rd d) => ∫⁻ p, k p ∂m)
            (iid_pi_pair_map d n ρ i j (Ne.symm (Finset.ne_of_mem_erase hj))))
    _ = _ := sum_erase_const_ennreal n _

def diffuseFillerLowerCount {X : Type*} [MeasurableSpace X]
    (ν : FiniteMeasure X) : ℕ := ⌊(ν.mass : ℝ)⌋₊

def diffuseFillerFraction {X : Type*} [MeasurableSpace X]
    (ν : FiniteMeasure X) : ℝ := (ν.mass : ℝ) - (diffuseFillerLowerCount ν : ℝ)

theorem diffuseFillerFraction_bounds {X : Type*} [MeasurableSpace X]
    (ν : FiniteMeasure X) :
    0 ≤ diffuseFillerFraction ν ∧ diffuseFillerFraction ν < 1 := by
  exact ⟨sub_nonneg.mpr (Nat.floor_le ν.mass.2),
    sub_lt_iff_lt_add.mpr ((Nat.lt_floor_add_one (ν.mass : ℝ)).trans_eq (add_comm _ _))⟩

theorem diffuseFiller_scalar_mean {X : Type*} [MeasurableSpace X]
    (ν : FiniteMeasure X) :
    (1 - diffuseFillerFraction ν) * (diffuseFillerLowerCount ν : ℝ) +
      diffuseFillerFraction ν * ((diffuseFillerLowerCount ν + 1 : ℕ) : ℝ) =
        (ν.mass : ℝ) := by
  simp only [diffuseFillerFraction, Nat.cast_add, Nat.cast_one]
  ring

theorem diffuseFiller_ennreal_mean {X : Type*} [MeasurableSpace X]
    (ν : FiniteMeasure X) :
    ENNReal.ofReal (1 - diffuseFillerFraction ν) *
        (diffuseFillerLowerCount ν : ℝ≥0∞) +
      ENNReal.ofReal (diffuseFillerFraction ν) *
        ((diffuseFillerLowerCount ν + 1 : ℕ) : ℝ≥0∞) = (ν.mass : ℝ≥0∞) := by
  have hθ := diffuseFillerFraction_bounds ν
  simpa only [ENNReal.ofReal_add
      (mul_nonneg (sub_nonneg.mpr hθ.2.le) (Nat.cast_nonneg _))
      (mul_nonneg hθ.1 (Nat.cast_nonneg _)),
    ENNReal.ofReal_mul (sub_nonneg.mpr hθ.2.le), ENNReal.ofReal_mul hθ.1,
    ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal]
    using congrArg ENNReal.ofReal (diffuseFiller_scalar_mean ν)

def diffuseFillerPairCoefficient {X : Type*} [MeasurableSpace X]
    (ν : FiniteMeasure X) : ℝ :=
  (1 - diffuseFillerFraction ν) *
      ((diffuseFillerLowerCount ν * (diffuseFillerLowerCount ν - 1) : ℕ) : ℝ) +
    diffuseFillerFraction ν *
      (((diffuseFillerLowerCount ν + 1) * diffuseFillerLowerCount ν : ℕ) : ℝ)

theorem diffuseFillerPairCoefficient_le_mass_square
    {X : Type*} [MeasurableSpace X] (ν : FiniteMeasure X) :
    diffuseFillerPairCoefficient ν ≤ (ν.mass : ℝ)^2 := by
  cases hm : diffuseFillerLowerCount ν with
  | zero => simp [diffuseFillerPairCoefficient, hm]
  | succ m =>
    simp only [diffuseFillerPairCoefficient, diffuseFillerFraction, hm,
      Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    nlinarith [sq_nonneg ((ν.mass : ℝ) - ((m : ℝ) + 1)), Nat.cast_nonneg (α := ℝ) m]

theorem diffuseFiller_ennreal_pairCoefficient {X : Type*} [MeasurableSpace X]
    (ν : FiniteMeasure X) :
    ENNReal.ofReal (1 - diffuseFillerFraction ν) *
        ((diffuseFillerLowerCount ν * (diffuseFillerLowerCount ν - 1) : ℕ) : ℝ≥0∞) +
      ENNReal.ofReal (diffuseFillerFraction ν) *
        (((diffuseFillerLowerCount ν + 1) * diffuseFillerLowerCount ν : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal (diffuseFillerPairCoefficient ν) := by
  have hθ := diffuseFillerFraction_bounds ν
  simp only [diffuseFillerPairCoefficient,
    ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr hθ.2.le) (Nat.cast_nonneg _))
      (mul_nonneg hθ.1 (Nat.cast_nonneg _)),
    ENNReal.ofReal_mul (sub_nonneg.mpr hθ.2.le), ENNReal.ofReal_mul hθ.1,
    ENNReal.ofReal_natCast]

def diffuseFillerLaw (d : ℕ) (ν : FiniteMeasure (Rd d)) : ConfigurationLaw d :=
  if ν = 0 then Measure.dirac (0 : Measure (Rd d)) else
    ENNReal.ofReal (1 - diffuseFillerFraction ν) •
      iidCountingLaw d (diffuseFillerLowerCount ν) (ν.normalize : Measure (Rd d)) +
    ENNReal.ofReal (diffuseFillerFraction ν) •
      iidCountingLaw d (diffuseFillerLowerCount ν + 1) (ν.normalize : Measure (Rd d))

theorem iidCountingLaw_probability (d n : ℕ) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] : IsProbabilityMeasure (iidCountingLaw d n ρ) := by
  exact Measure.isProbabilityMeasure_map (measurable_tupleCounting d n).aemeasurable

instance diffuseFillerLaw_probability (d : ℕ) (ν : FiniteMeasure (Rd d)) :
    IsProbabilityMeasure (diffuseFillerLaw d ν) := by
  by_cases hν : ν = 0
  · simpa only [diffuseFillerLaw, if_pos hν] using
      (inferInstance : IsProbabilityMeasure (Measure.dirac (0 : Measure (Rd d))))
  · letI (n : ℕ) : IsProbabilityMeasure
        (iidCountingLaw d n (ν.normalize : Measure (Rd d))) :=
      iidCountingLaw_probability d n (ν.normalize : Measure (Rd d))
    refine ⟨?_⟩
    simp only [diffuseFillerLaw, if_neg hν, Measure.add_apply, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    simpa only [sub_add_cancel, ENNReal.ofReal_one] using
      (ENNReal.ofReal_add
        (sub_nonneg.mpr (diffuseFillerFraction_bounds ν).2.le)
        (diffuseFillerFraction_bounds ν).1).symm

theorem ae_eq_zero_dirac_zero (d : ℕ) :
    ∀ᵐ μ ∂Measure.dirac (0 : Measure (Rd d)), μ = 0 := by
  have hZ : MeasurableSet {μ : Measure (Rd d) | μ = 0} := by
    simpa only [Measure.measure_univ_eq_zero] using
      (measurableSet_eq_fun (Measure.measurable_coe MeasurableSet.univ)
        (measurable_const : Measurable (fun _ : Measure (Rd d) => (0 : ℝ≥0∞))))
  exact (ae_dirac_iff hZ).mpr rfl

theorem lintegral_dirac_zero_measure (d : ℕ) (f : Measure (Rd d) → ℝ≥0∞) :
    (∫⁻ μ, f μ ∂Measure.dirac (0 : Measure (Rd d))) = f 0 := by
  rw [lintegral_congr_ae ((ae_eq_zero_dirac_zero d).mono
    (fun μ hμ => congrArg f hμ)), lintegral_const, measure_univ, mul_one]

theorem zero_isSimpleConfiguration (d : ℕ) :
    IsSimpleConfiguration d (0 : Measure (Rd d)) := by
  simpa [tupleCounting] using
    tupleCounting_simple d 0 Fin.elim0 (fun i => Fin.elim0 i)

theorem diffuseFiller_normalize_nullSingleton (d : ℕ) (ν : FiniteMeasure (Rd d))
    [NullSingletonClass (ν : Measure (Rd d))] (hν : ν ≠ 0) :
    NullSingletonClass (ν.normalize : Measure (Rd d)) := by
  refine ⟨fun y => ?_⟩
  simp [ν.toMeasure_normalize_eq_of_nonzero hν]

theorem diffuseFillerLaw_spec (d : ℕ) (ν : FiniteMeasure (Rd d))
    [NullSingletonClass (ν : Measure (Rd d))]
    (S : Set (Rd d)) (hS : MeasurableSet S)
    (hνS : (ν : Measure (Rd d)) Sᶜ = 0) :
    ∀ᵐ μ ∂diffuseFillerLaw d ν,
      IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧
      (μ Set.univ = (diffuseFillerLowerCount ν : ℝ≥0∞) ∨
       μ Set.univ = ((diffuseFillerLowerCount ν + 1 : ℕ) : ℝ≥0∞)) := by
  by_cases hν : ν = 0
  · simp only [diffuseFillerLaw, if_pos hν]
    refine (ae_eq_zero_dirac_zero d).mono (fun μ hμ => ?_)
    simp [hμ, hν, zero_isSimpleConfiguration, diffuseFillerLowerCount]
  · letI := diffuseFiller_normalize_nullSingleton d ν hν
    have hρS : (ν.normalize : Measure (Rd d)) Sᶜ = 0 := by
      simp [ν.toMeasure_normalize_eq_of_nonzero hν, hνS]
    rw [diffuseFillerLaw, if_neg hν, ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure
      (((iidCountingLaw_spec d (diffuseFillerLowerCount ν)
        (ν.normalize : Measure (Rd d)) S hS hρS).2.1).mono
          (fun _ h => ⟨h.1, h.2.1, Or.inl h.2.2⟩)) _,
      Measure.ae_smul_measure
        (((iidCountingLaw_spec d (diffuseFillerLowerCount ν + 1)
          (ν.normalize : Measure (Rd d)) S hS hρS).2.1).mono
            (fun _ h => ⟨h.1, h.2.1, Or.inr h.2.2⟩)) _⟩

theorem diffuseFillerLaw_mean (d : ℕ) (ν : FiniteMeasure (Rd d))
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ μ, μ D ∂diffuseFillerLaw d ν) = (ν : Measure (Rd d)) D := by
  by_cases hν : ν = 0
  · simp [hν, diffuseFillerLaw, lintegral_dirac_zero_measure]
  · rw [diffuseFillerLaw, if_neg hν, lintegral_add_measure,
      lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul,
      iidCountingLaw_mean d (diffuseFillerLowerCount ν) _ D hD,
      iidCountingLaw_mean d (diffuseFillerLowerCount ν + 1) _ D hD,
      ← mul_assoc, ← mul_assoc, ← add_mul, diffuseFiller_ennreal_mean]
    simpa only [ENNReal.coe_mul, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      using (congrArg (fun a : NNReal => (a : ℝ≥0∞))
        (ν.self_eq_mass_mul_normalize D)).symm

theorem diffuseFillerLaw_secondMoment (d : ℕ) (ν : FiniteMeasure (Rd d))
    [NullSingletonClass (ν : Measure (Rd d))] :
    (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂diffuseFillerLaw d ν) < ∞ := by
  have hbound : ∀ᵐ μ ∂diffuseFillerLaw d ν,
      μ Set.univ ≤ ((diffuseFillerLowerCount ν + 1 : ℕ) : ℝ≥0∞) :=
    (diffuseFillerLaw_spec d ν Set.univ MeasurableSet.univ (by simp)).mono
      (fun _ h => h.2.2.elim
        (fun hm => hm.le.trans (Nat.cast_le.mpr (Nat.le_succ _))) (fun hm => hm.le))
  refine (lintegral_mono_ae (hbound.mono (fun _ h => pow_le_pow_left' h 2))).trans_lt ?_
  simp

theorem diffuseFillerLaw_pair_lintegral_eq (d : ℕ) (ν : FiniteMeasure (Rd d))
    [NullSingletonClass (ν : Measure (Rd d))]
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ μ, windowPairIntegral d k μ ∂diffuseFillerLaw d ν) =
      ENNReal.ofReal (diffuseFillerPairCoefficient ν) *
        ∫⁻ p, k p ∂(ν.normalize : Measure (Rd d)).prod
          (ν.normalize : Measure (Rd d)) := by
  by_cases hν : ν = 0
  · simp [hν, diffuseFillerLaw, lintegral_dirac_zero_measure, windowPairIntegral,
      diffuseFillerPairCoefficient, diffuseFillerLowerCount, diffuseFillerFraction]
  · letI := diffuseFiller_normalize_nullSingleton d ν hν
    simp only [diffuseFillerLaw, if_neg hν, lintegral_add_measure,
      lintegral_smul_measure, smul_eq_mul,
      iidCountingLaw_pair_lintegral d (diffuseFillerLowerCount ν)
        (ν.normalize : Measure (Rd d)) k hk,
      iidCountingLaw_pair_lintegral d (diffuseFillerLowerCount ν + 1)
        (ν.normalize : Measure (Rd d)) k hk, Nat.add_sub_cancel]
    rw [← mul_assoc, ← mul_assoc, ← add_mul, diffuseFiller_ennreal_pairCoefficient]

theorem diffuseFiller_product_eq_mass_square (d : ℕ) (ν : FiniteMeasure (Rd d)) :
    (ν : Measure (Rd d)).prod (ν : Measure (Rd d)) =
      ((ν.mass : ℝ≥0∞) ^ 2) •
        (ν.normalize : Measure (Rd d)).prod (ν.normalize : Measure (Rd d)) := by
  simpa only [FiniteMeasure.toMeasure_prod, FiniteMeasure.toMeasure_smul,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ProbabilityMeasure.toMeasure_prod, ← Measure.coe_nnreal_smul,
    ENNReal.coe_mul, pow_two] using
      congrArg (fun σ : FiniteMeasure (Rd d × Rd d) => (σ : Measure (Rd d × Rd d)))
        (finiteMeasure_prod_eq_mass_smul_normalize ν ν)

theorem diffuseFillerLaw_pair_lintegral_le (d : ℕ) (ν : FiniteMeasure (Rd d))
    [NullSingletonClass (ν : Measure (Rd d))]
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ μ, windowPairIntegral d k μ ∂diffuseFillerLaw d ν) ≤
      ∫⁻ p, k p ∂(ν : Measure (Rd d)).prod (ν : Measure (Rd d)) := by
  rw [diffuseFillerLaw_pair_lintegral_eq d ν k hk,
    diffuseFiller_product_eq_mass_square, lintegral_smul_measure, smul_eq_mul]
  refine mul_le_mul_left ?_ _
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (ν.mass : ℝ) from ν.mass.2) 2,
    ENNReal.ofReal_coe_nnreal]
    using ENNReal.ofReal_le_ofReal (diffuseFillerPairCoefficient_le_mass_square ν)

private theorem exists_measurable_finite_extension
    {X : Type*} [MeasurableSpace X] :
    ∃ f : Measure X → FiniteMeasure X, Measurable f ∧
      ∀ μ : Measure X, IsFiniteMeasure μ → (f μ).toMeasure = μ := by
  obtain ⟨f, hf, hleft⟩ :=
    (MeasurableEmbedding.subtype_coe
      (FiniteMeasure.measurableSet_isFiniteMeasure (Ω := X))).exists_measurable_extend
        (measurable_id : Measurable (id : FiniteMeasure X → FiniteMeasure X))
        (fun _ => ⟨0⟩)
  exact ⟨f, hf, fun μ hμ => congrArg FiniteMeasure.toMeasure
    (congr_fun hleft (⟨μ, hμ⟩ : FiniteMeasure X))⟩

private theorem ae_isFiniteMeasure_of_finite_mean
    {X : Type*} [MeasurableSpace X] (M : Measure (Measure X))
    (a : FiniteMeasure X)
    (hmean : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂M) = (a : Measure X) D) :
    ∀ᵐ μ ∂M, IsFiniteMeasure μ := by
  exact (ae_lt_top' (Measure.measurable_coe MeasurableSet.univ).aemeasurable
    (ne_of_lt ((hmean Set.univ MeasurableSet.univ).trans_lt
      (measure_lt_top (a : Measure X) Set.univ)))).mono (fun _ hμ => ⟨hμ⟩)

private theorem aemeasurable_ambient_self_pair_of_finite
    (d : ℕ) (M : ConfigurationLaw d) (hM : ∀ᵐ μ ∂M, IsFiniteMeasure μ)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    AEMeasurable (fun μ : Measure (Rd d) => ∫⁻ x, ∫⁻ y, k (x, y) ∂μ ∂μ) M := by
  obtain ⟨f, hf, hfeq⟩ := exists_measurable_finite_extension (X := Rd d)
  refine ((Measure.measurable_lintegral hk).comp
    (FiniteMeasure.measurable_fun_prod.comp (hf.prodMk hf))).aemeasurable.congr ?_
  filter_upwards [hM] with μ hμ
  letI := hμ
  simpa only [Function.comp_apply, hfeq μ hμ] using lintegral_prod k hk.aemeasurable

theorem independent_ambient_pair_lintegral (d : ℕ)
    (T F : ConfigurationLaw d) [IsProbabilityMeasure T] [IsProbabilityMeasure F]
    (a b : FiniteMeasure (Rd d))
    (hmeanT : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂T) = (a : Measure (Rd d)) D)
    (hmeanF : ∀ D, MeasurableSet D → (∫⁻ η, η D ∂F) = (b : Measure (Rd d)) D)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    AEMeasurable (fun z : Measure (Rd d) × Measure (Rd d) =>
      ∫⁻ x, ∫⁻ y, k (x, y) ∂z.2 ∂z.1) (T.prod F) ∧
    (∫⁻ z : Measure (Rd d) × Measure (Rd d),
      ∫⁻ x, ∫⁻ y, k (x, y) ∂z.2 ∂z.1 ∂T.prod F) =
        ∫⁻ p, k p ∂(a : Measure (Rd d)).prod (b : Measure (Rd d)) := by
  obtain ⟨f, hf, hfeq⟩ := exists_measurable_finite_extension (X := Rd d)
  have ⟨hTfin, hFfin⟩ := And.intro
    (ae_isFiniteMeasure_of_finite_mean T a hmeanT)
    (ae_isFiniteMeasure_of_finite_mean F b hmeanF)
  let G : Measure (Rd d) × Measure (Rd d) → Measure (Rd d × Rd d) :=
    fun z => (f z.1).toMeasure.prod (f z.2).toMeasure
  have hG : Measurable G := FiniteMeasure.measurable_fun_prod.comp
    ((hf.comp measurable_fst).prodMk (hf.comp measurable_snd))
  have hfirst (M : ConfigurationLaw d) (c : FiniteMeasure (Rd d))
      (hM : ∀ᵐ μ ∂M, IsFiniteMeasure μ)
      (hm : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂M) = (c : Measure (Rd d)) D)
      (D : Set (Rd d)) (hD : MeasurableSet D) :
      (∫⁻ μ, (f μ).toMeasure D ∂M) = (c : Measure (Rd d)) D :=
    (lintegral_congr_ae (hM.mono (fun μ hμ =>
      congrArg (fun ρ : Measure (Rd d) => ρ D) (hfeq μ hμ)))).trans (hm D hD)
  have hbind : (T.prod F).bind G =
      (a : Measure (Rd d)).prod (b : Measure (Rd d)) := by
    refine (Measure.prod_eq (fun D E hD hE => ?_)).symm
    rw [Measure.bind_apply (hD.prod hE) hG.aemeasurable]
    simp only [G, Measure.prod_prod]
    exact (lintegral_prod_mul
      (((Measure.measurable_coe hD).comp measurable_subtype_coe).comp hf).aemeasurable
      (((Measure.measurable_coe hE).comp measurable_subtype_coe).comp hf).aemeasurable).trans
        (congrArg₂ (· * ·) (hfirst T a hTfin hmeanT D hD)
          (hfirst F b hFfin hmeanF E hE))
  have hfinitePair : ∀ᵐ z : Measure (Rd d) × Measure (Rd d) ∂T.prod F,
      IsFiniteMeasure z.1 ∧ IsFiniteMeasure z.2 :=
    (ae_of_ae_map measurable_fst.aemeasurable
      ((measurePreserving_fst (μ := T) (ν := F)).map_eq.symm ▸ hTfin)).and
      (ae_of_ae_map measurable_snd.aemeasurable
        ((measurePreserving_snd (μ := T) (ν := F)).map_eq.symm ▸ hFfin))
  have hAE : (fun z : Measure (Rd d) × Measure (Rd d) =>
      ∫⁻ x, ∫⁻ y, k (x, y) ∂z.2 ∂z.1) =ᵐ[T.prod F]
        (fun z => ∫⁻ p, k p ∂G z) :=
    hfinitePair.mono (fun z hz =>
      (congrArg₂ (fun μ η : Measure (Rd d) => ∫⁻ x, ∫⁻ y, k (x, y) ∂η ∂μ)
        (hfeq z.1 hz.1).symm (hfeq z.2 hz.2).symm).trans
          (lintegral_prod k hk.aemeasurable).symm)
  exact ⟨((Measure.measurable_lintegral hk).comp hG).aemeasurable.congr hAE.symm,
    (lintegral_congr_ae hAE).trans
      ((Measure.lintegral_bind hG.aemeasurable hk.aemeasurable).symm.trans
        (congrArg (fun ρ : Measure (Rd d × Rd d) => ∫⁻ p, k p ∂ρ) hbind))⟩

def independentAmbientSumLaw (d : ℕ) (T F : ConfigurationLaw d) : ConfigurationLaw d :=
  (T.prod F).map (fun z => z.1 + z.2)

theorem measurable_ambientPairSum (d : ℕ) :
    Measurable (fun z : Measure (Rd d) × Measure (Rd d) => z.1 + z.2) := by
  exact measurable_fst.add measurable_snd

instance independentAmbientSumLaw_probability (d : ℕ) (T F : ConfigurationLaw d)
    [IsProbabilityMeasure T] [IsProbabilityMeasure F] :
    IsProbabilityMeasure (independentAmbientSumLaw d T F) := by
  exact Measure.isProbabilityMeasure_map (measurable_ambientPairSum d).aemeasurable

theorem independentAmbientSumLaw_mean (d : ℕ) (T F : ConfigurationLaw d)
    [IsProbabilityMeasure T] [IsProbabilityMeasure F]
    (a b : Measure (Rd d))
    (hmeanT : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂T) = a D)
    (hmeanF : ∀ D, MeasurableSet D → (∫⁻ η, η D ∂F) = b D)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ ζ, ζ D ∂independentAmbientSumLaw d T F) = (a + b) D := by
  rw [independentAmbientSumLaw, lintegral_map (Measure.measurable_coe hD)
    (measurable_ambientPairSum d)]
  simp only [Measure.add_apply]
  rw [lintegral_add_left (μ := T.prod F)
      (f := fun z : Measure (Rd d) × Measure (Rd d) => z.1 D)
      (g := fun z => z.2 D) ((Measure.measurable_coe hD).comp measurable_fst),
    (measurePreserving_fst (μ := T) (ν := F)).lintegral_comp (Measure.measurable_coe hD),
    (measurePreserving_snd (μ := T) (ν := F)).lintegral_comp (Measure.measurable_coe hD),
    hmeanT D hD, hmeanF D hD]

def cellOffsiteKernel (d : ℕ) (k : Rd d × Rd d → ℝ≥0∞) (p : Rd d × Rd d) : ℝ≥0∞ :=
  if p.1 = p.2 then 0 else k p

theorem measurable_cellOffsiteKernel (d : ℕ) (k : Rd d × Rd d → ℝ≥0∞)
    (hk : Measurable k) : Measurable (cellOffsiteKernel d k) := by
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const hk

def cellCrossIntegral (d : ℕ) (k : Rd d × Rd d → ℝ≥0∞)
    (μ η : Measure (Rd d)) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, cellOffsiteKernel d k (x, y) ∂η ∂μ

def cellMeanCrossIntegral (d : ℕ) (k : Rd d × Rd d → ℝ≥0∞)
    (a b : Measure (Rd d)) : ℝ≥0∞ := ∫⁻ p, k p ∂a.prod b

theorem windowPairIntegral_add (d : ℕ) (k : Rd d × Rd d → ℝ≥0∞)
    (hk : Measurable k) (μ η : Measure (Rd d)) [SFinite μ] [SFinite η] :
    windowPairIntegral d k (μ + η) = windowPairIntegral d k μ + windowPairIntegral d k η +
      cellCrossIntegral d k μ η + cellCrossIntegral d k η μ := by
  have hμ : Measurable (fun x => ∫⁻ y, cellOffsiteKernel d k (x, y) ∂μ) :=
    (measurable_cellOffsiteKernel d k hk).lintegral_prod_right'
  change (∫⁻ x, ∫⁻ y, cellOffsiteKernel d k (x, y) ∂(μ + η) ∂(μ + η)) =
    (∫⁻ x, ∫⁻ y, cellOffsiteKernel d k (x, y) ∂μ ∂μ) +
      (∫⁻ x, ∫⁻ y, cellOffsiteKernel d k (x, y) ∂η ∂η) +
      (∫⁻ x, ∫⁻ y, cellOffsiteKernel d k (x, y) ∂η ∂μ) +
      (∫⁻ x, ∫⁻ y, cellOffsiteKernel d k (x, y) ∂μ ∂η)
  simp only [lintegral_add_measure, lintegral_add_left hμ _]
  ac_rfl

private theorem lintegral_comp_measurePreserving_ae
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {M : Measure A} {N : Measure B} {g : A → B} (hg : MeasurePreserving g M N)
    (f : B → ℝ≥0∞) (hf : AEMeasurable f N) :
    (∫⁻ x, f (g x) ∂M) = ∫⁻ y, f y ∂N := by
  exact (lintegral_map' (hg.map_eq.symm ▸ hf) hg.measurable.aemeasurable).symm.trans
    (congrArg (fun R => ∫⁻ y, f y ∂R) hg.map_eq)

private theorem aemeasurable_windowPairIntegral_of_finite_mean
    (d : ℕ) (M : ConfigurationLaw d) (a : FiniteMeasure (Rd d))
    (hmean : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂M) = (a : Measure (Rd d)) D)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    AEMeasurable (windowPairIntegral d k) M := by
  exact aemeasurable_ambient_self_pair_of_finite d M
    (ae_isFiniteMeasure_of_finite_mean M a hmean)
    (cellOffsiteKernel d k) (measurable_cellOffsiteKernel d k hk)

theorem independentAmbientSumLaw_pair_offsite (d : ℕ)
    (T F : ConfigurationLaw d) [IsProbabilityMeasure T] [IsProbabilityMeasure F]
    (a b : FiniteMeasure (Rd d))
    (hmeanT : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂T) = (a : Measure (Rd d)) D)
    (hmeanF : ∀ D, MeasurableSet D → (∫⁻ η, η D ∂F) = (b : Measure (Rd d)) D)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ ζ, windowPairIntegral d k ζ ∂independentAmbientSumLaw d T F) =
      (∫⁻ μ, windowPairIntegral d k μ ∂T) +
      (∫⁻ η, windowPairIntegral d k η ∂F) +
      cellMeanCrossIntegral d (cellOffsiteKernel d k) a b +
      cellMeanCrossIntegral d (cellOffsiteKernel d k) b a := by
  have ⟨hpairT, hpairF, hpairSum⟩ := And.intro
    (aemeasurable_windowPairIntegral_of_finite_mean d T a hmeanT k hk)
    (And.intro (aemeasurable_windowPairIntegral_of_finite_mean d F b hmeanF k hk)
      (aemeasurable_windowPairIntegral_of_finite_mean d (independentAmbientSumLaw d T F)
        (a + b) (independentAmbientSumLaw_mean d T F a b hmeanT hmeanF) k hk))
  have ⟨hcross, hrev⟩ := And.intro
    (independent_ambient_pair_lintegral d T F a b hmeanT hmeanF
      (cellOffsiteKernel d k) (measurable_cellOffsiteKernel d k hk))
    (independent_ambient_pair_lintegral d F T b a hmeanF hmeanT
      (cellOffsiteKernel d k) (measurable_cellOffsiteKernel d k hk))
  have hrevInt : (∫⁻ z : Measure (Rd d) × Measure (Rd d),
      cellCrossIntegral d k z.2 z.1 ∂T.prod F) =
        cellMeanCrossIntegral d (cellOffsiteKernel d k) b a :=
    (lintegral_comp_measurePreserving_ae
      (Measure.measurePreserving_swap (μ := T) (ν := F))
      (fun z => cellCrossIntegral d k z.1 z.2) hrev.1).trans hrev.2
  have hfinitePair : ∀ᵐ z : Measure (Rd d) × Measure (Rd d) ∂T.prod F,
      IsFiniteMeasure z.1 ∧ IsFiniteMeasure z.2 :=
    (ae_of_ae_map measurable_fst.aemeasurable
      ((measurePreserving_fst (μ := T) (ν := F)).map_eq.symm ▸
        ae_isFiniteMeasure_of_finite_mean T a hmeanT)).and
      (ae_of_ae_map measurable_snd.aemeasurable
        ((measurePreserving_snd (μ := T) (ν := F)).map_eq.symm ▸
          ae_isFiniteMeasure_of_finite_mean F b hmeanF))
  calc
    _ = ∫⁻ z : Measure (Rd d) × Measure (Rd d), windowPairIntegral d k (z.1 + z.2)
        ∂T.prod F := lintegral_map' hpairSum (measurable_ambientPairSum d).aemeasurable
    _ = ∫⁻ z : Measure (Rd d) × Measure (Rd d), windowPairIntegral d k z.1 +
        windowPairIntegral d k z.2 + cellCrossIntegral d k z.1 z.2 +
          cellCrossIntegral d k z.2 z.1 ∂T.prod F :=
      lintegral_congr_ae (hfinitePair.mono (fun z hz =>
        letI := hz.1
        letI := hz.2
        windowPairIntegral_add d k hk z.1 z.2))
    _ = _ := by
      have ⟨hfst, hsnd⟩ := And.intro
        (hpairT.comp_quasiMeasurePreserving
          (measurePreserving_fst (μ := T) (ν := F)).quasiMeasurePreserving)
        (hpairF.comp_quasiMeasurePreserving
          (measurePreserving_snd (μ := T) (ν := F)).quasiMeasurePreserving)
      rw [lintegral_add_left'
          (f := fun z : Measure (Rd d) × Measure (Rd d) =>
            windowPairIntegral d k z.1 + windowPairIntegral d k z.2 +
              cellCrossIntegral d k z.1 z.2)
          ((hfst.add hsnd).add hcross.1) (fun z => cellCrossIntegral d k z.2 z.1),
        lintegral_add_left'
          (f := fun z : Measure (Rd d) × Measure (Rd d) =>
            windowPairIntegral d k z.1 + windowPairIntegral d k z.2)
          (hfst.add hsnd) (fun z => cellCrossIntegral d k z.1 z.2),
        lintegral_add_left'
          (f := fun z : Measure (Rd d) × Measure (Rd d) => windowPairIntegral d k z.1)
          hfst (fun z => windowPairIntegral d k z.2),
        lintegral_comp_measurePreserving_ae
          (measurePreserving_fst (μ := T) (ν := F)) _ hpairT,
        lintegral_comp_measurePreserving_ae
          (measurePreserving_snd (μ := T) (ν := F)) _ hpairF,
        (show (∫⁻ z : Measure (Rd d) × Measure (Rd d),
            cellCrossIntegral d k z.1 z.2 ∂T.prod F) =
          cellMeanCrossIntegral d (cellOffsiteKernel d k) a b from hcross.2), hrevInt]

theorem cellMeanCrossIntegral_add_square (d : ℕ) (k : Rd d × Rd d → ℝ≥0∞)
    (a b : FiniteMeasure (Rd d)) :
    cellMeanCrossIntegral d k (a + b : Measure (Rd d)) (a + b : Measure (Rd d)) =
      cellMeanCrossIntegral d k a a + cellMeanCrossIntegral d k b b +
        cellMeanCrossIntegral d k a b + cellMeanCrossIntegral d k b a := by
  simp only [cellMeanCrossIntegral, Measure.add_prod, Measure.prod_add, lintegral_add_measure]
  ac_rfl

theorem independentAmbientSumLaw_pair_centered_ennreal (d : ℕ)
    (T F : ConfigurationLaw d) [IsProbabilityMeasure T] [IsProbabilityMeasure F]
    (a b : FiniteMeasure (Rd d))
    (hmeanT : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂T) = (a : Measure (Rd d)) D)
    (hmeanF : ∀ D, MeasurableSet D → (∫⁻ η, η D ∂F) = (b : Measure (Rd d)) D)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k)
    (hfill : (∫⁻ η, windowPairIntegral d k η ∂F) ≤ cellMeanCrossIntegral d k b b) :
    (∫⁻ ζ, windowPairIntegral d k ζ ∂independentAmbientSumLaw d T F) +
      cellMeanCrossIntegral d k a a ≤
        (∫⁻ μ, windowPairIntegral d k μ ∂T) +
          cellMeanCrossIntegral d k (a + b : Measure (Rd d)) (a + b : Measure (Rd d)) := by
  have h0 : ∀ p, cellOffsiteKernel d k p ≤ k p :=
    fun p => if h : p.1 = p.2 then
      (show cellOffsiteKernel d k p = 0 from if_pos h).trans_le bot_le
    else (show cellOffsiteKernel d k p = k p from if_neg h).le
  rw [independentAmbientSumLaw_pair_offsite d T F a b hmeanT hmeanF k hk,
    cellMeanCrossIntegral_add_square]
  calc
    _ ≤ ((∫⁻ μ, windowPairIntegral d k μ ∂T) + cellMeanCrossIntegral d k b b +
        cellMeanCrossIntegral d k a b + cellMeanCrossIntegral d k b a) +
          cellMeanCrossIntegral d k a a :=
      add_le_add
        (add_le_add (add_le_add (add_le_add le_rfl hfill) (lintegral_mono h0))
          (lintegral_mono h0)) le_rfl
    _ = _ := by
      ac_rfl

def cellRealEnergy (d : ℕ) (k : Rd d × Rd d → ℝ≥0∞) (μ : Measure (Rd d)) : ℝ :=
  (windowPairIntegral d k μ).toReal

theorem independentAmbientSumLaw_centered_energy (d : ℕ)
    (T F : ConfigurationLaw d) [IsProbabilityMeasure T] [IsProbabilityMeasure F]
    (a b : FiniteMeasure (Rd d))
    (hmeanT : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂T) = (a : Measure (Rd d)) D)
    (hmeanF : ∀ D, MeasurableSet D → (∫⁻ η, η D ∂F) = (b : Measure (Rd d)) D)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k)
    (hfill : (∫⁻ η, windowPairIntegral d k η ∂F) ≤ cellMeanCrossIntegral d k b b)
    (hthin : (∫⁻ μ, windowPairIntegral d k μ ∂T) < ∞)
    (hbackground : cellMeanCrossIntegral d k (a + b : Measure (Rd d))
      (a + b : Measure (Rd d)) < ∞) :
    (∫⁻ ζ, windowPairIntegral d k ζ ∂independentAmbientSumLaw d T F) ≠ ∞ ∧
    Integrable (cellRealEnergy d k) (independentAmbientSumLaw d T F) ∧
    (∫ ζ, cellRealEnergy d k ζ ∂independentAmbientSumLaw d T F) -
      (cellMeanCrossIntegral d k (a + b : Measure (Rd d)) (a + b : Measure (Rd d))).toReal ≤
        (∫ μ, cellRealEnergy d k μ ∂T) - (cellMeanCrossIntegral d k a a).toReal := by
  have hENN := independentAmbientSumLaw_pair_centered_ennreal
    d T F a b hmeanT hmeanF k hk hfill
  have hRightNe : (∫⁻ μ, windowPairIntegral d k μ ∂T) +
      cellMeanCrossIntegral d k (a + b : Measure (Rd d)) (a + b : Measure (Rd d)) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hthin.ne, hbackground.ne⟩
  have ⟨hCne, hBgAne⟩ := ENNReal.add_ne_top.mp (ne_top_of_le_ne_top hRightNe hENN)
  have ⟨hpairT, hpairC⟩ := And.intro
    (aemeasurable_windowPairIntegral_of_finite_mean d T a hmeanT k hk)
    (aemeasurable_windowPairIntegral_of_finite_mean d (independentAmbientSumLaw d T F)
      (a + b) (independentAmbientSumLaw_mean d T F a b hmeanT hmeanF) k hk)
  have hr : (∫⁻ ζ, windowPairIntegral d k ζ ∂independentAmbientSumLaw d T F).toReal +
      (cellMeanCrossIntegral d k a a).toReal ≤
        (∫⁻ μ, windowPairIntegral d k μ ∂T).toReal +
          (cellMeanCrossIntegral d k (a + b : Measure (Rd d))
            (a + b : Measure (Rd d))).toReal := by
    simpa only [ENNReal.toReal_add hCne hBgAne,
      ENNReal.toReal_add hthin.ne hbackground.ne] using ENNReal.toReal_mono hRightNe hENN
  refine ⟨hCne, integrable_toReal_of_lintegral_ne_top hpairC hCne, ?_⟩
  simpa only [cellRealEnergy, integral_toReal hpairC (ae_lt_top' hpairC hCne),
    integral_toReal hpairT (ae_lt_top' hpairT hthin.ne)] using sub_le_sub_iff.mpr hr

theorem simple_finite_count_representation (d : ℕ) (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ) (hμFin : μ Set.univ < ∞) :
    ∃ n : ℕ, ∃ x : Fin n → Rd d, Function.Injective x ∧ μ = tupleCounting d n x := by
  rcases hμ with ⟨S, _, rfl⟩
  have hS : S.Finite := by
    by_contra hS
    haveI : Infinite S := Set.infinite_coe_iff.mpr hS
    simp only [Measure.sum_apply _ MeasurableSet.univ,
      Measure.dirac_apply_of_mem (Set.mem_univ _),
      ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero, lt_self_iff_false] at hμFin
  letI := hS.fintype
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  simpa only [Measure.sum_fintype, Function.comp_def, tupleCounting] using
    (Measure.sum_comp_equiv e (fun z : S => Measure.dirac z.val)).symm

theorem tupleCounting_append (d n m : ℕ) (x : Fin n → Rd d) (y : Fin m → Rd d) :
    tupleCounting d (n + m) (Fin.append x y) = tupleCounting d n x + tupleCounting d m y := by
  simp only [tupleCounting, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem tupleCounting_add_simple_of_avoid (d n : ℕ) (x : Fin n → Rd d)
    (hx : Function.Injective x) (η : Measure (Rd d))
    (hη : IsSimpleConfiguration d η) (hηFin : η Set.univ < ∞)
    (havoid : ∀ i, η {x i} = 0) :
    IsSimpleConfiguration d (tupleCounting d n x + η) := by
  obtain ⟨m, y, hy, rfl⟩ := simple_finite_count_representation d η hη hηFin
  have hxy : ∀ i j, x i ≠ y j := fun i j hij =>
    zero_ne_one ((havoid i).symm.trans
      ((congrArg (fun z : Rd d => tupleCounting d m y {z}) hij).trans
        (tupleCounting_singleton_one d m y hy j)))
  simpa only [tupleCounting_append] using
    tupleCounting_simple d (n + m) (Fin.append x y)
      (Fin.append_injective_iff.mpr ⟨hx, hy, hxy⟩)

theorem ae_no_atom_of_diffuse_mean (d : ℕ) (Q : ConfigurationLaw d)
    (ν : Measure (Rd d)) [NullSingletonClass ν]
    (hmean : ∀ D, MeasurableSet D → (∫⁻ η, η D ∂Q) = ν D) (z : Rd d) :
    ∀ᵐ η ∂Q, η {z} = 0 := by
  exact (lintegral_eq_zero_iff (Measure.measurable_coe (measurableSet_singleton z))).mp
    ((hmean {z} (measurableSet_singleton z)).trans (measure_singleton z))

theorem ae_simple_add_fixed_of_diffuse_mean (d : ℕ)
    (Q : ConfigurationLaw d) (ν : Measure (Rd d)) [NullSingletonClass ν]
    (hmean : ∀ D, MeasurableSet D → (∫⁻ η, η D ∂Q) = ν D)
    (hQ : ∀ᵐ η ∂Q, IsSimpleConfiguration d η ∧ η Set.univ < ∞)
    (μ : Measure (Rd d)) (hμ : IsSimpleConfiguration d μ) (hμFin : μ Set.univ < ∞) :
    ∀ᵐ η ∂Q, IsSimpleConfiguration d (μ + η) := by
  obtain ⟨n, x, hx, rfl⟩ := simple_finite_count_representation d μ hμ hμFin
  exact (hQ.and (ae_all_iff.mpr (fun i : Fin n =>
    ae_no_atom_of_diffuse_mean d Q ν hmean (x i)))).mono
      (fun η h => tupleCounting_add_simple_of_avoid d n x hx η h.1.1 h.1.2 h.2)

theorem independentAmbientSumLaw_good (d : ℕ) (T F : ConfigurationLaw d)
    [IsProbabilityMeasure T] [IsProbabilityMeasure F]
    (S : Set (Rd d)) (hS : MeasurableSet S)
    (hT : ∀ᵐ μ ∂T, IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ < ∞)
    (hF : ∀ᵐ η ∂F, IsSimpleConfiguration d η ∧ η Sᶜ = 0 ∧ η Set.univ < ∞)
    (ν : Measure (Rd d)) [NullSingletonClass ν]
    (hmeanF : ∀ D, MeasurableSet D → (∫⁻ η, η D ∂F) = ν D) :
    ∀ᵐ ζ ∂independentAmbientSumLaw d T F,
      IsSimpleConfiguration d ζ ∧ ζ Sᶜ = 0 ∧ ζ Set.univ < ∞ := by
  refine (ae_map_iff (measurable_ambientPairSum d).aemeasurable
    (measurableSet_windowFiniteGood d S hS)).mpr
      ((Measure.ae_prod_iff_ae_ae ((measurableSet_windowFiniteGood d S hS).preimage
        (measurable_ambientPairSum d))).mpr ?_)
  filter_upwards [hT] with μ hμ
  exact (hF.and (ae_simple_add_fixed_of_diffuse_mean d F ν hmeanF
    (hF.mono (fun _ h => ⟨h.1, h.2.2⟩)) μ hμ.1 hμ.2.2)).mono
      (fun η hη => ⟨hη.2,
        (Measure.add_apply μ η Sᶜ).trans
          ((congrArg₂ (· + ·) hμ.2.1 hη.1.2.1).trans (add_zero 0)),
        (Measure.add_apply μ η Set.univ).trans_lt
          (ENNReal.add_lt_top.mpr ⟨hμ.2.2, hη.1.2.2⟩)⟩)

theorem ennreal_add_sq_le_four (a b : ℝ≥0∞) : (a + b)^2 ≤ 4 * (a^2 + b^2) := by
  simpa only [ENNReal.rpow_two, show (2 : ℝ≥0∞)^2 = 4 from by norm_num] using
    ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow a b (show (0 : ℝ) ≤ 2 from zero_le_two)

theorem independentAmbientSumLaw_secondMoment (d : ℕ) (T F : ConfigurationLaw d)
    [IsProbabilityMeasure T] [IsProbabilityMeasure F]
    (hT : (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂T) < ∞)
    (hF : (∫⁻ η, (η Set.univ)^(2 : ℕ) ∂F) < ∞) :
    (∫⁻ ζ, (ζ Set.univ)^(2 : ℕ) ∂independentAmbientSumLaw d T F) < ∞ := by
  have hm : Measurable (fun μ : Measure (Rd d) => (μ Set.univ)^(2 : ℕ)) :=
    (Measure.measurable_coe MeasurableSet.univ).pow_const 2
  rw [independentAmbientSumLaw, lintegral_map hm (measurable_ambientPairSum d)]
  calc
    _ ≤ ∫⁻ z : Measure (Rd d) × Measure (Rd d),
        4 * ((z.1 Set.univ)^2 + (z.2 Set.univ)^2) ∂T.prod F :=
      lintegral_mono (fun z =>
        (congrArg (fun r : ℝ≥0∞ => r^2) (Measure.add_apply z.1 z.2 Set.univ)).trans_le
          (ennreal_add_sq_le_four (z.1 Set.univ) (z.2 Set.univ)))
    _ = 4 * ((∫⁻ μ, (μ Set.univ)^2 ∂T) + ∫⁻ η, (η Set.univ)^2 ∂F) := by
      rw [lintegral_const_mul
          (f := fun z : Measure (Rd d) × Measure (Rd d) =>
            (z.1 Set.univ)^2 + (z.2 Set.univ)^2) _
          ((hm.comp measurable_fst).add (hm.comp measurable_snd)),
        lintegral_add_left
          (f := fun z : Measure (Rd d) × Measure (Rd d) => (z.1 Set.univ)^2)
          (hm.comp measurable_fst) (fun z => (z.2 Set.univ)^2),
        (measurePreserving_fst (μ := T) (ν := F)).lintegral_comp hm,
        (measurePreserving_snd (μ := T) (ν := F)).lintegral_comp hm]
    _ < ∞ := by
      exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hT, hF⟩)

def finiteCellCarrier (d : ℕ) (S K : Set (Rd d)) (hSK : S ⊆ K) (hK : IsCompact K) :
    FiniteMeasure (Rd d) :=
  ⟨volume.restrict S, ⟨(Measure.restrict_apply_univ S).trans_lt
    ((measure_mono hSK).trans_lt (hK.measure_lt_top (μ := (volume : Measure (Rd d)))))⟩⟩

def boundedDensityFiniteMeasure {X : Type*} [MeasurableSpace X]
    (c : FiniteMeasure X) (f : X → ℝ≥0∞) (hbound : ∀ x, f x ≤ 1) : FiniteMeasure X :=
  ⟨(c : Measure X).withDensity f, ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (lintegral_mono hbound).trans_lt (by simp)⟩⟩

def cellWindowMean (d : ℕ) (c : FiniteMeasure (Rd d)) (χ : Rd d → ℝ)
    (hbound : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) : FiniteMeasure (Rd d) :=
  boundedDensityFiniteMeasure c (fun x => ENNReal.ofReal (χ x)) (fun x => by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hbound x).2)

def cellResidualMean (d : ℕ) (c : FiniteMeasure (Rd d)) (χ : Rd d → ℝ)
    (hbound : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) : FiniteMeasure (Rd d) :=
  boundedDensityFiniteMeasure c (fun x => ENNReal.ofReal (1 - χ x)) (fun x => by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      (sub_le_self (1 : ℝ) (hbound x).1))

theorem cellWindowMean_add_residual (d : ℕ) (c : FiniteMeasure (Rd d))
    (χ : Rd d → ℝ) (hχ : Measurable χ) (hbound : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    (cellWindowMean d c χ hbound : Measure (Rd d)) +
      (cellResidualMean d c χ hbound : Measure (Rd d)) = (c : Measure (Rd d)) := by
  have hsum : (fun x => ENNReal.ofReal (χ x)) + (fun x => ENNReal.ofReal (1 - χ x)) =
      (1 : Rd d → ℝ≥0∞) := by
    funext x
    change ENNReal.ofReal (χ x) + ENNReal.ofReal (1 - χ x) = 1
    rw [← ENNReal.ofReal_add (hbound x).1 (sub_nonneg.mpr (hbound x).2),
      show χ x + (1 - χ x) = 1 by ring, ENNReal.ofReal_one]
  change (c : Measure (Rd d)).withDensity (fun x => ENNReal.ofReal (χ x)) +
    (c : Measure (Rd d)).withDensity (fun x => ENNReal.ofReal (1 - χ x)) = _
  rw [← withDensity_add_left hχ.ennreal_ofReal (fun x => ENNReal.ofReal (1 - χ x)),
    hsum, withDensity_one]

theorem windowDensity_restrict_eq (d : ℕ) (S : Set (Rd d)) (hS : MeasurableSet S)
    (χ : Rd d → ℝ) (hzero : ∀ x ∉ S, χ x = 0) :
    (volume.restrict S).withDensity (fun x => ENNReal.ofReal (χ x)) =
      (volume.withDensity (fun x => ENNReal.ofReal (χ x)) : Measure (Rd d)) := by
  have hcompl : (volume.withDensity (fun x => ENNReal.ofReal (χ x)) : Measure (Rd d)) Sᶜ = 0 := by
    rw [withDensity_apply _ hS.compl]
    exact lintegral_eq_zero_of_ae_eq_zero
      ((ae_restrict_mem hS.compl).mono (fun x hx => by simp [hzero x hx]))
  rw [← restrict_withDensity hS]
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hcompl)

def filledWindowLaw (d : ℕ) (P : ConfigurationLaw d) (S K : Set (Rd d))
    (hSK : S ⊆ K) (hK : IsCompact K) (χ : Rd d → ℝ)
    (hbound : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) : ConfigurationLaw d :=
  independentAmbientSumLaw d (finiteWindowThinningLaw d P K χ)
    (diffuseFillerLaw d (cellResidualMean d (finiteCellCarrier d S K hSK hK) χ hbound))

theorem filledWindowLaw_spec (d : ℕ) (hd : 0 < d) (P : ConfigurationLaw d)
    (hP : Admissible d P) (S K : Set (Rd d)) (hS : MeasurableSet S)
    (hSK : S ⊆ K) (hK : IsCompact K) (χ : Rd d → ℝ) (hχ : Measurable χ)
    (hbound : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hzero : ∀ x ∉ S, χ x = 0) :
    IsProbabilityMeasure (filledWindowLaw d P S K hSK hK χ hbound) ∧
    (∀ᵐ ζ ∂filledWindowLaw d P S K hSK hK χ hbound,
      IsSimpleConfiguration d ζ ∧ ζ Sᶜ = 0 ∧ ζ Set.univ < ∞) ∧
    (∀ D, MeasurableSet D → (∫⁻ ζ, ζ D ∂filledWindowLaw d P S K hSK hK χ hbound) =
      (volume.restrict S) D) ∧
    (∫⁻ ζ, (ζ Set.univ) ^ (2 : ℕ) ∂filledWindowLaw d P S K hSK hK χ hbound) < ∞ := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI := hP.1
  let c := finiteCellCarrier d S K hSK hK
  let a := cellWindowMean d c χ hbound
  let b := cellResidualMean d c χ hbound
  let T := finiteWindowThinningLaw d P K χ
  letI : IsProbabilityMeasure T :=
    finiteWindowThinningLaw_probability d P K hK.measurableSet χ hχ
  letI : NullSingletonClass (b : Measure (Rd d)) :=
    inferInstanceAs (NullSingletonClass
      ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (1 - χ x))))
  have ha : (a : Measure (Rd d)) = volume.withDensity (fun x => ENNReal.ofReal (χ x)) :=
    windowDensity_restrict_eq d S hS χ hzero
  have hmeanT : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂T) = (a : Measure (Rd d)) D :=
    fun D hD => (finiteWindowThinningLaw_mean d P hP K hK χ hχ hbound
      (fun x hx => hzero x (fun hxS => hx (hSK hxS))) D hD).trans
        (congrArg (fun ρ : Measure (Rd d) => ρ D) ha.symm)
  have haS : (a : Measure (Rd d)) Sᶜ = 0 := by
    exact withDensity_absolutelyContinuous (volume.restrict S)
      (fun x => ENNReal.ofReal (χ x)) (by simp [Measure.restrict_apply hS.compl])
  have hsupportT : ∀ᵐ μ ∂T, μ Sᶜ = 0 :=
    (lintegral_eq_zero_iff (Measure.measurable_coe hS.compl)).mp
      ((hmeanT Sᶜ hS.compl).trans haS)
  have hT : ∀ᵐ μ ∂T, IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ < ∞ :=
    ((finiteWindowThinningLaw_good d P hP K hK χ hχ).and hsupportT).mono
      (fun μ hμ => ⟨hμ.1.1, hμ.2, hμ.1.2.2⟩)
  have hbS : (b : Measure (Rd d)) Sᶜ = 0 :=
    withDensity_absolutelyContinuous (volume.restrict S)
      (fun x => ENNReal.ofReal (1 - χ x)) (by simp [Measure.restrict_apply hS.compl])
  have hF : ∀ᵐ η ∂diffuseFillerLaw d b,
      IsSimpleConfiguration d η ∧ η Sᶜ = 0 ∧ η Set.univ < ∞ :=
    (diffuseFillerLaw_spec d b S hS hbS).mono (fun η hη =>
      ⟨hη.1, hη.2.1, hη.2.2.elim
        (fun hm => hm.trans_lt (ENNReal.natCast_lt_top _))
        (fun hm => hm.trans_lt (ENNReal.natCast_lt_top _))⟩)
  have hmeanSum : ∀ D, MeasurableSet D →
      (∫⁻ ζ, ζ D ∂independentAmbientSumLaw d T (diffuseFillerLaw d b)) = (volume.restrict S) D :=
    fun D hD => (independentAmbientSumLaw_mean d T (diffuseFillerLaw d b) a b
      hmeanT (diffuseFillerLaw_mean d b) D hD).trans
        (congrArg (fun ρ : Measure (Rd d) => ρ D)
          (cellWindowMean_add_residual d c χ hχ hbound))
  exact ⟨independentAmbientSumLaw_probability d T (diffuseFillerLaw d b),
    independentAmbientSumLaw_good d T (diffuseFillerLaw d b) S hS hT hF b
      (diffuseFillerLaw_mean d b), hmeanSum,
    independentAmbientSumLaw_secondMoment d T (diffuseFillerLaw d b)
      (finiteWindowThinningLaw_secondMoment d P hP K hK χ hχ)
      (diffuseFillerLaw_secondMoment d b)⟩

theorem filledWindowLaw_centered_energy (d : ℕ) (hd : 0 < d) (P : ConfigurationLaw d)
    (hP : Admissible d P) (S K : Set (Rd d)) (hS : MeasurableSet S)
    (hSK : S ⊆ K) (hK : IsCompact K) (χ : Rd d → ℝ) (hχ : Measurable χ)
    (hbound : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hzero : ∀ x ∉ S, χ x = 0)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k)
    (hthin : (∫⁻ μ, windowPairIntegral d k μ ∂finiteWindowThinningLaw d P K χ) < ∞)
    (hbackground : (∫⁻ p, k p ∂(volume.restrict S).prod (volume.restrict S)) < ∞) :
    (∫⁻ ζ, windowPairIntegral d k ζ ∂filledWindowLaw d P S K hSK hK χ hbound) ≠ ∞ ∧
    Integrable (cellRealEnergy d k) (filledWindowLaw d P S K hSK hK χ hbound) ∧
    (∫ ζ, cellRealEnergy d k ζ ∂filledWindowLaw d P S K hSK hK χ hbound) -
      (∫⁻ p, k p ∂(volume.restrict S).prod (volume.restrict S)).toReal ≤
        (∫ μ, cellRealEnergy d k μ ∂finiteWindowThinningLaw d P K χ) -
          (∫⁻ p, k p ∂(volume.withDensity (fun x => ENNReal.ofReal (χ x)) : Measure (Rd d)).prod
            (volume.withDensity (fun x => ENNReal.ofReal (χ x)) : Measure (Rd d))).toReal := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI := hP.1
  let c := finiteCellCarrier d S K hSK hK
  let a := cellWindowMean d c χ hbound
  let b := cellResidualMean d c χ hbound
  let T := finiteWindowThinningLaw d P K χ
  letI : IsProbabilityMeasure T :=
    finiteWindowThinningLaw_probability d P K hK.measurableSet χ hχ
  letI : NullSingletonClass (b : Measure (Rd d)) :=
    inferInstanceAs (NullSingletonClass
      ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (1 - χ x))))
  have ha : (a : Measure (Rd d)) = volume.withDensity (fun x => ENNReal.ofReal (χ x)) :=
    windowDensity_restrict_eq d S hS χ hzero
  have hsum : (a : Measure (Rd d)) + (b : Measure (Rd d)) = volume.restrict S :=
    cellWindowMean_add_residual d c χ hχ hbound
  have hmeanT : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂T) = (a : Measure (Rd d)) D :=
    fun D hD => (finiteWindowThinningLaw_mean d P hP K hK χ hχ hbound
      (fun x hx => hzero x (fun hxS => hx (hSK hxS))) D hD).trans
        (congrArg (fun ρ : Measure (Rd d) => ρ D) ha.symm)
  have hBg : cellMeanCrossIntegral d k (a + b : Measure (Rd d))
      (a + b : Measure (Rd d)) < ∞ := by
    simpa only [cellMeanCrossIntegral, hsum] using hbackground
  have hresult :=
    independentAmbientSumLaw_centered_energy d T (diffuseFillerLaw d b) a b hmeanT
      (diffuseFillerLaw_mean d b) k hk (diffuseFillerLaw_pair_lintegral_le d b k hk) hthin hBg
  rw [hsum, ha] at hresult
  exact hresult

end Riesz.Configuration
