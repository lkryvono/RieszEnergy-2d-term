import Riesz.Negative.Cubes
import Riesz.Configuration.MeasureCodes
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-! Finite sampling laws for the exact balanced class in `Showcase.lean`.
The cube limit and its comparison with the stationary infimum remain separate targets. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Negative

/-- The volume of the half-open coordinate cube in Euclidean space. -/
theorem volume_cube (d : ℕ) (L : ℝ) :
    volume (cube d L) = (ENNReal.ofReal L) ^ d := by
  have h := (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi (fun _ : Fin d =>
      measurableSet_Ico (a := (0 : ℝ)) (b := L))).nullMeasurableSet
  simpa only [cube, Set.preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Ico, Real.volume_pi_Ico, sub_zero, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using h

/-- The finite counting measure of a tuple, retaining multiplicities. -/
def tupleCounting (d n : ℕ) (x : Fin n → Rd d) : Measure (Rd d) :=
  ∑ i, Measure.dirac (x i)

/-- The law of the counting measure of independent samples with common law `ρ`. -/
def iidCountingLaw (d n : ℕ) (ρ : Measure (Rd d)) : ConfigurationLaw d :=
  Measure.map (tupleCounting d n) (Measure.pi (fun _ : Fin n => ρ))

/-- Uniform sampling in the cube, normalized by its prescribed point count. -/
def cubeUniform (d m : ℕ) : Measure (Rd d) :=
  (m ^ d : ℝ≥0∞)⁻¹ • volume.restrict (cube d (m : ℝ))

theorem cubeUniform_probability (d m : ℕ) (hm : 0 < m) :
    IsProbabilityMeasure (cubeUniform d m) := by
  constructor
  simp only [cubeUniform, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_cube,
    ENNReal.ofReal_natCast, ← Nat.cast_pow]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (pow_pos hm d).ne')
    (ENNReal.natCast_ne_top (m ^ d))

theorem cubeUniform_nullSingletonClass (d m : ℕ) (hd : 0 < d) :
    NullSingletonClass (cubeUniform d m) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  dsimp [cubeUniform]
  refine ⟨fun x => ?_⟩
  simp [Measure.smul_apply]

theorem measurable_tupleCounting (d n : ℕ) : Measurable (tupleCounting d n) := by
  exact Finset.measurable_fun_sum _ (fun i _ => Measure.measurable_dirac.comp
    (measurable_pi_apply i))

theorem tupleCounting_isFiniteMeasure (d n : ℕ) (x : Fin n → Rd d) :
    IsFiniteMeasure (tupleCounting d n x) := by
  unfold tupleCounting
  infer_instance

/-- The same counting measure in the finite-measure Giry space. -/
def finiteTupleCounting (d n : ℕ) (x : Fin n → Rd d) : FiniteMeasure (Rd d) :=
  ⟨tupleCounting d n x, tupleCounting_isFiniteMeasure d n x⟩

theorem measurable_finiteTupleCounting (d n : ℕ) : Measurable (finiteTupleCounting d n) := by
  exact (measurable_tupleCounting d n).subtype_mk

theorem tupleCounting_singleton_ne_zero_iff (d n : ℕ) (x : Fin n → Rd d) (z : Rd d) :
    tupleCounting d n x {z} ≠ 0 ↔ z ∈ Set.range x := by
  simp [tupleCounting, Measure.finsetSum_apply, Measure.dirac_apply', Pi.single_apply]

theorem tupleCounting_range_eq_of_eq (d n : ℕ) (x y : Fin n → Rd d)
    (h : tupleCounting d n x = tupleCounting d n y) : Set.range x = Set.range y := by
  ext z
  rw [← tupleCounting_singleton_ne_zero_iff d n x z,
    ← tupleCounting_singleton_ne_zero_iff d n y z, h]

theorem tupleCounting_ordered_injective (d n : ℕ) (f : Rd d → ℝ)
    (hf : Function.Injective f) :
    Set.InjOn (tupleCounting d n) {x | StrictMono (f ∘ x)} := by
  intro x hx y hy h
  have hr := tupleCounting_range_eq_of_eq d n x y h
  have hc : f ∘ x = f ∘ y := hx.range_inj hy |>.mp
    (by simp only [Set.range_comp, hr])
  exact funext (fun i => hf (congr_fun hc i))

theorem measurableSet_ordered_tuples (d n : ℕ) (f : Rd d → ℝ) (hf : Measurable f) :
    MeasurableSet {x : Fin n → Rd d | StrictMono (f ∘ x)} := by
  simpa only [StrictMono, Set.setOf_forall, Function.comp_def] using
    MeasurableSet.iInter (fun i : Fin n => MeasurableSet.iInter (fun j : Fin n =>
    MeasurableSet.iInter (fun _ : i < j =>
      measurableSet_lt (hf.comp (measurable_pi_apply i)) (hf.comp (measurable_pi_apply j)))))

theorem tupleCounting_ordered_representation (d n : ℕ) (f : Rd d → ℝ)
    (hf : Function.Injective f) (x : Fin n → Rd d) (hx : Function.Injective x) :
    ∃ y : Fin n → Rd d, StrictMono (f ∘ y) ∧ tupleCounting d n y = tupleCounting d n x := by
  letI : LinearOrder (Rd d) := LinearOrder.lift' f hf
  let T : Finset (Rd d) := Finset.univ.image x
  have hcard : T.card = n := by simpa [T] using Finset.card_image_of_injective Finset.univ hx
  refine ⟨T.orderEmbOfFin hcard, (T.orderEmbOfFin hcard).strictMono, ?_⟩
  rw [tupleCounting, tupleCounting,
    ← Finset.sum_image (T.orderEmbOfFin hcard).injective.injOn]
  have himage : Finset.univ.image (T.orderEmbOfFin hcard) = T :=
    Finset.coe_injective (by simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      using Finset.range_orderEmbOfFin T hcard)
  simp only [himage, T, Finset.sum_image hx.injOn]

/-- The finite simple-counting class is measurable in the exact space used by the showcase. -/
theorem measurableSet_simple_counting_class (d n : ℕ) :
    MeasurableSet {μ : Measure (Rd d) | ∃ x : Fin n → Rd d,
      Function.Injective x ∧ μ = tupleCounting d n x} := by
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real (Rd d)
  letI := Riesz.Configuration.countablySeparated_finiteMeasure (Rd d)
  have hinj : Set.InjOn (finiteTupleCounting d n) {x | StrictMono (f ∘ x)} :=
    fun x hx y hy h => tupleCounting_ordered_injective d n f hf.injective hx hy
      (congrArg FiniteMeasure.toMeasure h)
  have hB := (measurableSet_ordered_tuples d n f hf.measurable).image_of_measurable_injOn
    (measurable_finiteTupleCounting d n) hinj
  have hC := (MeasurableEmbedding.subtype_coe
    (FiniteMeasure.measurableSet_isFiniteMeasure (Ω := Rd d))).measurableSet_image.mpr hB
  convert hC using 1
  ext μ
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := tupleCounting_ordered_representation d n f hf.injective x hx
    exact ⟨finiteTupleCounting d n y, ⟨y, hy, rfl⟩, hxy⟩
  · rintro ⟨ν, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, fun i j hij => hx.injective (congrArg f hij), rfl⟩

theorem tupleCounting_simple (d n : ℕ) (x : Fin n → Rd d) (hx : Function.Injective x) :
    IsSimpleConfiguration d (tupleCounting d n x) := by
  refine ⟨Set.range x, fun K _ => (Set.finite_range x).inter_of_left K, ?_⟩
  simpa [Measure.sum_fintype, Function.comp_def, tupleCounting] using
    Measure.sum_comp_equiv (Equiv.ofInjective x hx) (fun z : Set.range x => Measure.dirac z.val)

theorem tupleCounting_univ (d n : ℕ) (x : Fin n → Rd d) :
    tupleCounting d n x Set.univ = (n : ℝ≥0∞) := by
  simp [tupleCounting, Measure.finsetSum_apply]

theorem ae_injective_pi (d n : ℕ) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] [NullSingletonClass ρ] :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => ρ), Function.Injective x := by
  simp only [Function.Injective, ae_all_iff]
  intro i j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ _ => hij)
  have hIndep := ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : Fin n => ρ) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hpair := (hIndep.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin n => ρ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => ρ) j).map_eq] at hpair
  have hprod : ∀ᵐ p : Rd d × Rd d ∂ρ.prod ρ, p.1 ≠ p.2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
      (Filter.Eventually.of_forall (fun x => (ρ.ae_ne x).mono (fun y h => h.symm)))
  have hmap : ∀ᵐ p : Rd d × Rd d ∂Measure.map (fun x : Fin n → Rd d => (x i, x j))
      (Measure.pi (fun _ : Fin n => ρ)), p.1 ≠ p.2 := hpair.symm ▸ hprod
  exact (ae_of_ae_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
    hmap).mono (fun x h heq => (h heq).elim)

theorem iidCountingLaw_mean (d n : ℕ) (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    (∫⁻ μ, μ D ∂iidCountingLaw d n ρ) = (n : ℝ≥0∞) * ρ D := by
  rw [iidCountingLaw, lintegral_map (Measure.measurable_coe hD) (measurable_tupleCounting d n)]
  simp_rw [tupleCounting, Measure.finsetSum_apply]
  rw [lintegral_finsetSum (f := fun (i : Fin n) (x : Fin n → Rd d) => Measure.dirac (x i) D)
    (Finset.univ : Finset (Fin n)) (fun i _ => (Measure.measurable_coe hD).comp
    (Measure.measurable_dirac.comp (measurable_pi_apply i)))]
  have heval (i : Fin n) :
      (∫⁻ x, Measure.dirac (x i) D ∂Measure.pi (fun _ : Fin n => ρ)) =
        ∫⁻ z, Measure.dirac z D ∂ρ :=
    (measurePreserving_eval (fun _ : Fin n => ρ) i).lintegral_comp
      ((Measure.measurable_coe hD).comp Measure.measurable_dirac)
  have hdirac : (∫⁻ z, Measure.dirac z D ∂ρ) = ρ D := by
    rw [← Measure.bind_apply hD Measure.measurable_dirac.aemeasurable, Measure.bind_dirac]
  simp only [heval, hdirac, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Independent diffuse samples give a simple fixed-count law with the exact mean. -/
theorem iidCountingLaw_spec (d n : ℕ) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] [NullSingletonClass ρ]
    (S : Set (Rd d)) (hS : MeasurableSet S) (hρ : ρ Sᶜ = 0) :
    IsProbabilityMeasure (iidCountingLaw d n ρ) ∧
    (∀ᵐ μ ∂iidCountingLaw d n ρ,
      IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ = (n : ℝ≥0∞)) ∧
    (∀ D : Set (Rd d), MeasurableSet D →
      (∫⁻ μ, μ D ∂iidCountingLaw d n ρ) = (n : ℝ≥0∞) * ρ D) := by
  have hclass : ∀ᵐ μ ∂iidCountingLaw d n ρ, ∃ x : Fin n → Rd d,
      Function.Injective x ∧ μ = tupleCounting d n x :=
    (ae_map_iff (measurable_tupleCounting d n).aemeasurable
      (measurableSet_simple_counting_class d n)).mpr
      ((ae_injective_pi d n ρ).mono (fun x hx => ⟨x, hx, rfl⟩))
  have hsupport : ∀ᵐ μ ∂iidCountingLaw d n ρ, μ Sᶜ = 0 :=
    (lintegral_eq_zero_iff (Measure.measurable_coe hS.compl)).mp
      ((iidCountingLaw_mean d n ρ Sᶜ hS.compl).trans (by rw [hρ, mul_zero]))
  refine ⟨Measure.isProbabilityMeasure_map (measurable_tupleCounting d n).aemeasurable,
    ?_, iidCountingLaw_mean d n ρ⟩
  filter_upwards [hclass, hsupport] with μ hμ hSμ
  rcases hμ with ⟨x, hx, rfl⟩
  exact ⟨tupleCounting_simple d n x hx, hSμ, tupleCounting_univ d n x⟩

/-- A concrete balanced law exists in every positive dimension and positive integer cube. -/
theorem exists_balanced_law (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    ∃ P : ConfigurationLaw d, BalancedAdmissible d m P := by
  letI := cubeUniform_probability d m hm
  letI := cubeUniform_nullSingletonClass d m hd
  have hsupport : cubeUniform d m (cube d (m : ℝ))ᶜ = 0 := by
    simp only [cubeUniform, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
      Set.compl_inter_self, measure_empty, mul_zero]
  obtain ⟨hprob, hconfig, hmean⟩ := iidCountingLaw_spec d (m ^ d) (cubeUniform d m)
    (cube d (m : ℝ)) (measurableSet_cube d (m : ℝ)) hsupport
  refine ⟨iidCountingLaw d (m ^ d) (cubeUniform d m), hprob, hconfig, ?_⟩
  intro D hD
  rw [hmean D hD, cubeUniform, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ← Nat.cast_pow,
    ENNReal.mul_inv_cancel (by exact_mod_cast (pow_pos hm d).ne') (ENNReal.natCast_ne_top (m ^ d)),
    one_mul]

/-- Actual expected energies of balanced laws, before taking their infimum. -/
def balancedExpectedEnergies (d : ℕ) (q : ℝ) (m : ℕ) : Set ℝ :=
  {r | ∃ P : ConfigurationLaw d,
    BalancedAdmissible d m P ∧ (∫ μ, D_q d q m μ ∂P) = r}

theorem balancedExpectedEnergies_nonempty (d m : ℕ) (q : ℝ) (hd : 0 < d) (hm : 0 < m) :
    (balancedExpectedEnergies d q m).Nonempty := by
  obtain ⟨P, hP⟩ := exists_balanced_law d m hd hm
  exact ⟨∫ μ, D_q d q m μ ∂P, P, hP, rfl⟩

theorem balancedExpectedEnergies_bddBelow (d m : ℕ) (q : ℝ) (hq_pos : 0 < q) (hq_two : q < 2) :
    BddBelow (balancedExpectedEnergies d q m) := by
  refine ⟨0, ?_⟩
  rintro r ⟨P, hP, rfl⟩
  exact (balanced_D_q_integrable_and_nonneg d m q hq_pos hq_two P hP).2

theorem b_le_expectedEnergy (d m : ℕ) (q : ℝ) (hq_pos : 0 < q) (hq_two : q < 2)
    (P : ConfigurationLaw d) (hP : BalancedAdmissible d m P) :
    b d q m ≤ ∫ μ, D_q d q m μ ∂P := by
  exact csInf_le (balancedExpectedEnergies_bddBelow d m q hq_pos hq_two) ⟨P, hP, rfl⟩

theorem b_isGLB (d m : ℕ) (q : ℝ) (hd : 0 < d) (hm : 0 < m)
    (hq_pos : 0 < q) (hq_two : q < 2) :
    IsGLB (balancedExpectedEnergies d q m) (b d q m) := by
  exact isGLB_csInf (balancedExpectedEnergies_nonempty d m q hd hm)
    (balancedExpectedEnergies_bddBelow d m q hq_pos hq_two)

/-- The nonempty finite-volume problem has near-minimizers among actual simple balanced laws. -/
theorem exists_near_optimal_balanced_law (d m : ℕ) (q ε : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hq_pos : 0 < q) (hq_two : q < 2) (hε : 0 < ε) :
    ∃ P : ConfigurationLaw d, BalancedAdmissible d m P ∧
      Integrable (D_q d q m) P ∧ b d q m ≤ (∫ μ, D_q d q m μ ∂P) ∧
      (∫ μ, D_q d q m μ ∂P) < b d q m + ε := by
  obtain ⟨r, ⟨P, hP, hE⟩, hr⟩ := exists_lt_of_csInf_lt
    (balancedExpectedEnergies_nonempty d m q hd hm) (lt_add_of_pos_right (b d q m) hε)
  refine ⟨P, hP, balanced_D_q_integrable d m q hq_pos hq_two P hP,
    b_le_expectedEnergy d m q hq_pos hq_two P hP, ?_⟩
  exact hE.symm ▸ hr
/-- A simple configuration of finite integer mass has an injective finite labeling. -/
theorem simple_fixed_count_representation (d n : ℕ) (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ) (hmass : μ Set.univ = (n : ℝ≥0∞)) :
    ∃ x : Fin n → Rd d, Function.Injective x ∧ μ = tupleCounting d n x := by
  rcases hμ with ⟨S, _, rfl⟩
  have hcount : (∑' _ : S, (1 : ℝ≥0∞)) = (n : ℝ≥0∞) := by
    simpa only [Measure.sum_apply _ MeasurableSet.univ, Measure.dirac_apply_of_mem
      (Set.mem_univ _)] using hmass
  have hS : S.Finite := by
    by_contra hS
    haveI : Infinite S := Set.infinite_coe_iff.mpr hS
    exact ENNReal.natCast_ne_top n
      (hcount.symm.trans (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero))
  letI := hS.fintype
  have hcard : Fintype.card S = n := by
    exact_mod_cast (by simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using hcount : (Fintype.card S : ℝ≥0∞) = n)
  let e : Fin n ≃ S := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  simpa only [Measure.sum_fintype, Function.comp_def, tupleCounting] using
    (Measure.sum_comp_equiv e (fun z : S => Measure.dirac z.val)).symm

/-- Finite simple counting measures admit a measurable choice of distinct labels. -/
theorem exists_measurable_label (d n : ℕ) :
    ∃ label : Measure (Rd d) → (Fin n → Rd d), Measurable label ∧
      ∀ μ : Measure (Rd d),
        (∃ x : Fin n → Rd d, Function.Injective x ∧ μ = tupleCounting d n x) →
        Function.Injective (label μ) ∧ tupleCounting d n (label μ) = μ := by
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real (Rd d)
  let O := {x : Fin n → Rd d // StrictMono (f ∘ x)}
  letI : StandardBorelSpace O := (measurableSet_ordered_tuples d n f hf.measurable).standardBorel
  letI := Riesz.Configuration.countablySeparated_finiteMeasure (Rd d)
  have hg : MeasurableEmbedding (fun x : O => finiteTupleCounting d n x.val) :=
    ((measurable_finiteTupleCounting d n).comp measurable_subtype_coe).measurableEmbedding
      (fun x y h => Subtype.ext (tupleCounting_ordered_injective d n f hf.injective
        x.property y.property (congrArg FiniteMeasure.toMeasure h)))
  have hcount : MeasurableEmbedding (fun x : O => tupleCounting d n x.val) :=
    (MeasurableEmbedding.subtype_coe
      (FiniteMeasure.measurableSet_isFiniteMeasure (Ω := Rd d))).comp hg
  obtain ⟨label, hlabel, hleft⟩ := hcount.exists_measurable_extend
    (measurable_subtype_coe : Measurable (fun x : O => x.val))
    (fun _ => ⟨fun _ => 0⟩)
  refine ⟨label, hlabel, ?_⟩
  rintro μ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := tupleCounting_ordered_representation d n f hf.injective x hx
  have hly : label (tupleCounting d n y) = y := congr_fun hleft (⟨y, hy⟩ : O)
  rw [← hxy, hly]
  exact ⟨fun i j hij => hy.injective (congrArg f hij), rfl⟩

theorem measurableSet_injective_tuples (d n : ℕ) :
    MeasurableSet {x : Fin n → Rd d | Function.Injective x} := by
  simpa only [Function.Injective, Set.mem_setOf_eq] using
    (Measurable.forall (fun i : Fin n => Measurable.forall (fun j : Fin n =>
      (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).mem.imp
        (measurable_const (a := i = j))))).setOf

/-- The showcase's simple, fixed-count event is measurable without a topology on all measures. -/
theorem measurableSet_simple_fixed_count (d n : ℕ) :
    MeasurableSet {μ : Measure (Rd d) |
      IsSimpleConfiguration d μ ∧ μ Set.univ = (n : ℝ≥0∞)} := by
  convert measurableSet_simple_counting_class d n using 1
  ext μ
  refine ⟨fun h => simple_fixed_count_representation d n μ h.1 h.2, ?_⟩
  rintro ⟨x, hx, rfl⟩
  exact ⟨tupleCounting_simple d n x hx, tupleCounting_univ d n x⟩

theorem tupleCounting_compl_eq_zero_iff (d n : ℕ) (x : Fin n → Rd d)
    (S : Set (Rd d)) (hS : MeasurableSet S) :
    tupleCounting d n x Sᶜ = 0 ↔ ∀ i, x i ∈ S := by
  simp [tupleCounting, Measure.finsetSum_apply, Measure.dirac_apply' _ hS.compl]

/-- Every simple fixed-count law is the counting-measure pushforward of a tuple law. -/
theorem exists_tuple_law_of_simple_fixed_count (d n : ℕ) (P : ConfigurationLaw d)
    [IsProbabilityMeasure P]
    (hP : ∀ᵐ μ ∂P, IsSimpleConfiguration d μ ∧ μ Set.univ = (n : ℝ≥0∞)) :
    ∃ Q : Measure (Fin n → Rd d), IsProbabilityMeasure Q ∧
      (∀ᵐ x ∂Q, Function.Injective x) ∧ Measure.map (tupleCounting d n) Q = P := by
  obtain ⟨label, hlabel, hspec⟩ := exists_measurable_label d n
  have hlabelAE := hP.mono (fun μ hμ => hspec μ
    (simple_fixed_count_representation d n μ hμ.1 hμ.2))
  refine ⟨Measure.map label P, Measure.isProbabilityMeasure_map hlabel.aemeasurable,
    (ae_map_iff hlabel.aemeasurable (measurableSet_injective_tuples d n)).mpr
      (hlabelAE.mono (fun _ h => h.1)), ?_⟩
  rw [Measure.map_map (measurable_tupleCounting d n) hlabel]
  exact (Measure.map_congr (hlabelAE.mono (fun _ h => h.2))).trans Measure.map_id

/-- The balanced cube problem represented by labeled, distinct point tuples. -/
def TupleBalancedAdmissible (d m : ℕ) (Q : Measure (Fin (m ^ d) → Rd d)) : Prop :=
  IsProbabilityMeasure Q ∧
  (∀ᵐ x ∂Q, Function.Injective x ∧ ∀ i, x i ∈ cube d (m : ℝ)) ∧
  (∀ D : Set (Rd d), MeasurableSet D →
    (∫⁻ x, tupleCounting d (m ^ d) x D ∂Q) =
      (volume.restrict (cube d (m : ℝ))) D)

/-- Passing from tuples to counting measures preserves the exact balanced predicate. -/
theorem balancedAdmissible_map_tuple (d m : ℕ) (Q : Measure (Fin (m ^ d) → Rd d))
    (hQ : TupleBalancedAdmissible d m Q) :
    BalancedAdmissible d m (Measure.map (tupleCounting d (m ^ d)) Q) := by
  letI : IsProbabilityMeasure Q := hQ.1
  have hclass : ∀ᵐ μ ∂Measure.map (tupleCounting d (m ^ d)) Q,
      IsSimpleConfiguration d μ ∧ μ Set.univ = (m ^ d : ℕ) :=
    (ae_map_iff (measurable_tupleCounting d (m ^ d)).aemeasurable
      (measurableSet_simple_fixed_count d (m ^ d))).mpr
      (hQ.2.1.mono (fun x hx => ⟨tupleCounting_simple d (m ^ d) x hx.1,
        tupleCounting_univ d (m ^ d) x⟩))
  have hsupport : ∀ᵐ μ ∂Measure.map (tupleCounting d (m ^ d)) Q,
      μ (cube d (m : ℝ))ᶜ = 0 :=
    (ae_map_iff (measurable_tupleCounting d (m ^ d)).aemeasurable
      (measurableSet_eq_fun (Measure.measurable_coe (measurableSet_cube d (m : ℝ)).compl)
        measurable_const)).mpr
      (hQ.2.1.mono (fun x hx => (tupleCounting_compl_eq_zero_iff d (m ^ d) x
        (cube d (m : ℝ)) (measurableSet_cube d (m : ℝ))).mpr hx.2))
  refine ⟨Measure.isProbabilityMeasure_map (measurable_tupleCounting d (m ^ d)).aemeasurable,
    ?_, fun D hD => (lintegral_map (Measure.measurable_coe hD)
      (measurable_tupleCounting d (m ^ d))).trans (hQ.2.2 D hD)⟩
  exact (hclass.and hsupport).mono (fun _ h => ⟨h.1.1, h.2, h.1.2⟩)

/-- A showcase balanced law has a tuple realization with the same law and exact mean. -/
theorem exists_tuple_balanced_law (d m : ℕ) (P : ConfigurationLaw d)
    (hP : BalancedAdmissible d m P) :
    ∃ Q : Measure (Fin (m ^ d) → Rd d), TupleBalancedAdmissible d m Q ∧
      Measure.map (tupleCounting d (m ^ d)) Q = P := by
  letI : IsProbabilityMeasure P := hP.1
  obtain ⟨Q, hprob, hinj, hmap⟩ := exists_tuple_law_of_simple_fixed_count d (m ^ d) P
    (hP.2.1.mono (fun _ h => ⟨h.1, h.2.2⟩))
  have hsupport : ∀ᵐ x ∂Q, ∀ i, x i ∈ cube d (m : ℝ) :=
    (ae_of_ae_map (measurable_tupleCounting d (m ^ d)).aemeasurable
      (hmap.symm ▸ hP.2.1.mono (fun _ h => h.2.1))).mono
      (fun x hx => (tupleCounting_compl_eq_zero_iff d (m ^ d) x
        (cube d (m : ℝ)) (measurableSet_cube d (m : ℝ))).mp hx)
  refine ⟨Q, ⟨hprob, hinj.and hsupport, ?_⟩, hmap⟩
  exact fun D hD => (lintegral_map (Measure.measurable_coe hD)
    (measurable_tupleCounting d (m ^ d))).symm.trans (hmap.symm ▸ hP.2.2 D hD)

theorem balancedAdmissible_iff_tuple_realization (d m : ℕ) (P : ConfigurationLaw d) :
    BalancedAdmissible d m P ↔
      ∃ Q : Measure (Fin (m ^ d) → Rd d), TupleBalancedAdmissible d m Q ∧
        Measure.map (tupleCounting d (m ^ d)) Q = P := by
  exact ⟨exists_tuple_balanced_law d m P, fun ⟨Q, hQ, hmap⟩ =>
    hmap ▸ balancedAdmissible_map_tuple d m Q hQ⟩

/-- Expected energies agree under the counting-measure pushforward. -/
theorem tupleBalanced_expectedEnergy_eq (d m : ℕ) (q : ℝ) (hq : 0 < q)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    (∫ x, D_q d q m (tupleCounting d (m ^ d) x) ∂Q) =
      ∫ μ, D_q d q m μ ∂Measure.map (tupleCounting d (m ^ d)) Q := by
  exact (integral_map (measurable_tupleCounting d (m ^ d)).aemeasurable
    (balanced_D_q_aestronglyMeasurable d m q hq _
      (balancedAdmissible_map_tuple d m Q hQ))).symm

theorem tupleBalanced_D_q_integrable (d m : ℕ) (q : ℝ) (hq : 0 < q) (hq_two : q < 2)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    Integrable (fun x => D_q d q m (tupleCounting d (m ^ d) x)) Q := by
  exact (balanced_D_q_integrable d m q hq hq_two _
    (balancedAdmissible_map_tuple d m Q hQ)).comp_measurable
      (measurable_tupleCounting d (m ^ d))

/-- Expected energies of balanced tuple laws, using the exact showcase kernel. -/
def tupleBalancedExpectedEnergies (d : ℕ) (q : ℝ) (m : ℕ) : Set ℝ :=
  {r | ∃ Q : Measure (Fin (m ^ d) → Rd d), TupleBalancedAdmissible d m Q ∧
    (∫ x, D_q d q m (tupleCounting d (m ^ d) x) ∂Q) = r}

def tupleBalancedInfimum (d : ℕ) (q : ℝ) (m : ℕ) : ℝ :=
  sInf (tupleBalancedExpectedEnergies d q m)

/-- Labeling changes neither the attainable expected-energy set nor its real infimum. -/
theorem balancedExpectedEnergies_eq_tuple (d m : ℕ) (q : ℝ) (hq : 0 < q) :
    balancedExpectedEnergies d q m = tupleBalancedExpectedEnergies d q m := by
  ext r
  constructor
  · rintro ⟨P, hP, hE⟩
    obtain ⟨Q, hQ, hmap⟩ := exists_tuple_balanced_law d m P hP
    exact ⟨Q, hQ, (tupleBalanced_expectedEnergy_eq d m q hq Q hQ).trans (hmap.symm ▸ hE)⟩
  · rintro ⟨Q, hQ, hE⟩
    exact ⟨Measure.map (tupleCounting d (m ^ d)) Q, balancedAdmissible_map_tuple d m Q hQ,
      (tupleBalanced_expectedEnergy_eq d m q hq Q hQ).symm.trans hE⟩

/-- The exact showcase infimum is unchanged by measurable finite labeling. -/
theorem b_eq_tupleBalancedInfimum (d m : ℕ) (q : ℝ) (hq : 0 < q) :
    b d q m = tupleBalancedInfimum d q m := by
  exact congrArg sInf (balancedExpectedEnergies_eq_tuple d m q hq)

end Riesz.Negative
