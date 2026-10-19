import Riesz.Configuration.FactorialContinuity
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! The expected factorial pair measure is represented directly from compact
tests. Unequal labels at coincident sites are retained until simplicity is proved.
-/

noncomputable section

open MeasureTheory RieszShowcase Filter
open scoped ENNReal Topology Classical CompactlySupported

namespace Riesz.Configuration

theorem countingFactorialIntegral_add (d : ℕ) (μ : CountingConfiguration d)
    (f g : C_c(Rd d × Rd d, ℝ)) :
    countingFactorialIntegral d μ (f + g) =
      countingFactorialIntegral d μ f + countingFactorialIntegral d μ g := by
  simp only [countingFactorialIntegral, CompactlySupportedContinuousMap.add_apply]
  rw [integral_add f.integrable g.integrable,
    integral_add
      (show Integrable (fun x => f (x, x)) μ.val from (countingDiagonalTest d f).integrable)
      (show Integrable (fun x => g (x, x)) μ.val from (countingDiagonalTest d g).integrable)]
  ring

theorem countingFactorialIntegral_smul (d : ℕ) (μ : CountingConfiguration d)
    (c : ℝ) (f : C_c(Rd d × Rd d, ℝ)) :
    countingFactorialIntegral d μ (c • f) = c * countingFactorialIntegral d μ f := by
  simp only [countingFactorialIntegral, CompactlySupportedContinuousMap.smul_apply,
    smul_eq_mul, integral_const_mul]
  ring

/-- The sharp local count-square bound uses labels, including repeated sites. -/
theorem abs_countingFactorialIntegral_le_localCount_sq (d n : ℕ)
    (μ : CountingConfiguration d) (f : C_c(Rd d × Rd d, ℝ))
    (hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ) ×ˢ
      Metric.closedBall (0 : Rd d) (n : ℝ)) :
    |countingFactorialIntegral d μ f| ≤ ‖f.toBoundedContinuousFunction‖ *
      (μ.val.real (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 := by
  obtain ⟨m, x, hx⟩ := μ.property n
  have hmass : μ.val.real (Metric.closedBall (0 : Rd d) (n : ℝ)) = (m : ℝ) := by
    simpa only [Measure.real, Measure.restrict_apply_univ,
      Riesz.Negative.tupleCounting_univ, ENNReal.toReal_natCast] using
      congrArg ENNReal.toReal (congrArg (fun ν : Measure (Rd d) => ν Set.univ) hx)
  rw [countingFactorialIntegral_eq_sum_of_restrict_eq_tupleCounting d n m μ x f hx hf, hmass]
  calc
    |∑ i : Fin m, ∑ j : Fin m, if i = j then 0 else f (x i, x j)| ≤
        ∑ i : Fin m, ∑ j : Fin m, ‖if i = j then 0 else f (x i, x j)‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le Finset.univ (fun i : Fin m => ∑ j : Fin m,
          if i = j then 0 else f (x i, x j))).trans
          (Finset.sum_le_sum (fun i _ => norm_sum_le Finset.univ
            (fun j : Fin m => if i = j then 0 else f (x i, x j))))
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, ‖f.toBoundedContinuousFunction‖ := by
      refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
      split_ifs
      · simp only [norm_zero, norm_nonneg]
      · exact f.toBoundedContinuousFunction.norm_coe_le_norm (x i, x j)
    _ = ‖f.toBoundedContinuousFunction‖ * (m : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Local second moments make every compact factorial test integrable. -/
theorem integrable_countingFactorialIntegral (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (f : C_c(Rd d × Rd d, ℝ)) :
    Integrable (fun μ => countingFactorialIntegral d μ f) P := by
  obtain ⟨R, hR⟩ := ((f.hasCompactSupport.image continuous_fst).union
    (f.hasCompactSupport.image continuous_snd)).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hf : tsupport f ⊆ Metric.closedBall (0 : Rd d) (n : ℝ) ×ˢ
      Metric.closedBall (0 : Rd d) (n : ℝ) := fun p hp => ⟨by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hR p.1 (Or.inl ⟨p, hp, rfl⟩)).trans hn, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hR p.2 (Or.inr ⟨p, hp, rfl⟩)).trans hn⟩
  have hbound (μ : CountingConfiguration d) :
      ENNReal.ofReal ‖countingFactorialIntegral d μ f‖ ≤
        ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
          (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 := by
    calc
      _ = ENNReal.ofReal |countingFactorialIntegral d μ f| := by rw [Real.norm_eq_abs]
      _ ≤ ENNReal.ofReal (‖f.toBoundedContinuousFunction‖ *
          (μ.val.real (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2) :=
        ENNReal.ofReal_le_ofReal (abs_countingFactorialIntegral_le_localCount_sq d n μ f hf)
      _ = _ := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), Measure.real,
          ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal
            (isCountingConfiguration_closedBall_lt_top d μ.val μ.property n).ne]
  refine ⟨(continuous_countingFactorialIntegral d f).measurable.aestronglyMeasurable,
    (hasFiniteIntegral_iff_norm _).2 ?_⟩
  calc
    _ ≤ ∫⁻ μ, ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P := lintegral_mono hbound
    _ < ∞ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hsecond n)

/-- Positive expectation functional, without a pointwise subtraction of measures. -/
def expectedFactorialFunctional (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞) :
    C_c(Rd d × Rd d, ℝ) →ₚ[ℝ] ℝ := by
  refine PositiveLinearMap.mk₀
    { toFun := fun f => ∫ μ, countingFactorialIntegral d μ f ∂P
      map_add' := ?_
      map_smul' := ?_ } ?_
  · intro f g
    simp_rw [countingFactorialIntegral_add]
    exact integral_add (integrable_countingFactorialIntegral d P hsecond f)
      (integrable_countingFactorialIntegral d P hsecond g)
  · intro c f
    simp only [countingFactorialIntegral_smul, smul_eq_mul, integral_const_mul, RingHom.id_apply]
  · intro f hf
    exact integral_nonneg (fun μ => countingFactorialIntegral_nonneg d μ f (fun p => hf p))

/-- The expected factorial pair measure on the actual Euclidean pair space. -/
def expectedFactorialMeasure (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞) :
    Measure (Rd d × Rd d) := RealRMK.rieszMeasure (expectedFactorialFunctional d P hsecond)

instance expectedFactorialMeasure_regular (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞) :
    (expectedFactorialMeasure d P hsecond).Regular :=
  RealRMK.regular_rieszMeasure (expectedFactorialFunctional d P hsecond)

theorem integral_expectedFactorialMeasure (d : ℕ) (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (f : C_c(Rd d × Rd d, ℝ)) :
    (∫ p, f p ∂expectedFactorialMeasure d P hsecond) =
      ∫ μ, countingFactorialIntegral d μ f ∂P := by
  exact RealRMK.integral_rieszMeasure (expectedFactorialFunctional d P hsecond) f

/-- Compact factorial Portmanteau requires no moment assumption on the prelimit. -/
theorem countingLaw_factorial_test_le_liminf (d : ℕ)
    (P : ℕ → ProbabilityMeasure (CountingConfiguration d))
    (Q : ProbabilityMeasure (CountingConfiguration d)) (hQ : Tendsto P atTop (𝓝 Q))
    (f : C_c(Rd d × Rd d, ℝ)) (hf : ∀ p, 0 ≤ f p) :
    (∫⁻ μ, ENNReal.ofReal (countingFactorialIntegral d μ f) ∂Q.toMeasure) ≤
      atTop.liminf (fun n => ∫⁻ μ,
        ENNReal.ofReal (countingFactorialIntegral d μ f) ∂(P n).toMeasure) := by
  exact lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (continuous_countingFactorialIntegral d f)
    (fun μ => countingFactorialIntegral_nonneg d μ f hf)
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hQ hG)

theorem lintegral_expectedFactorialMeasure_le_liminf (d : ℕ)
    (P : ℕ → ProbabilityMeasure (CountingConfiguration d))
    (Q : ProbabilityMeasure (CountingConfiguration d)) (hQ : Tendsto P atTop (𝓝 Q))
    (hsecondQ : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂Q.toMeasure) < ∞)
    (f : C_c(Rd d × Rd d, ℝ)) (hf : ∀ p, 0 ≤ f p) :
    (∫⁻ p, ENNReal.ofReal (f p) ∂expectedFactorialMeasure d Q.toMeasure hsecondQ) ≤
      atTop.liminf (fun n => ∫⁻ μ,
        ENNReal.ofReal (countingFactorialIntegral d μ f) ∂(P n).toMeasure) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
      (f.integrable (μ := expectedFactorialMeasure d Q.toMeasure hsecondQ))
      (Eventually.of_forall hf), integral_expectedFactorialMeasure d Q.toMeasure hsecondQ f,
    ofReal_integral_eq_lintegral_ofReal
      (integrable_countingFactorialIntegral d Q.toMeasure hsecondQ f)
      (Eventually.of_forall (fun μ => countingFactorialIntegral_nonneg d μ f hf))]
  exact countingLaw_factorial_test_le_liminf d P Q hQ f hf

/-- Failure of local simplicity is witnessed by unequal labels at one site. -/
theorem exists_collision_of_not_finiteSimpleOn (d n r m : ℕ) (μ : Measure (Rd d))
    (x : Fin m → Rd d) (hnr : n ≤ r)
    (hrest : μ.restrict (Metric.closedBall 0 (r : ℝ)) = Riesz.Negative.tupleCounting d m x)
    (hbad : ¬ FiniteSimpleOn d (Metric.closedBall 0 (n : ℝ)) μ) :
    ∃ i j : Fin m, i ≠ j ∧ x i ∈ Metric.closedBall 0 (n : ℝ) ∧
      x j ∈ Metric.closedBall 0 (n : ℝ) ∧ x i = x j := by
  by_contra hcollision
  let K := Metric.closedBall (0 : Rd d) (n : ℝ)
  let J := {i : Fin m // x i ∈ K}
  let e := Fintype.equivFin J
  let xf : Fin (Fintype.card J) → Rd d := fun j => x (e.symm j).val
  have hfilter : (Riesz.Negative.tupleCounting d m x).restrict K =
      Riesz.Negative.tupleCounting d (Fintype.card J) xf := by
    rw [Riesz.Negative.tupleCounting, ← Measure.sum_fintype,
      Measure.restrict_sum_of_countable, Measure.sum_fintype]
    simp only [restrict_dirac, Riesz.Negative.tupleCounting]
    rw [← Finset.sum_filter,
      Finset.sum_subtype (p := fun i => x i ∈ K) (F := inferInstance) _ (by simp)]
    exact (e.symm.sum_comp (fun i : J => Measure.dirac (x i.val))).symm
  have hsub : K ⊆ Metric.closedBall (0 : Rd d) (r : ℝ) :=
    Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hnr)
  have hsmall : μ.restrict K = Riesz.Negative.tupleCounting d (Fintype.card J) xf :=
    (Measure.restrict_restrict_of_subset hsub).symm.trans
      ((congrArg (fun ν : Measure (Rd d) => ν.restrict K) hrest).trans hfilter)
  have hinj : Function.Injective (fun i : J => x i.val) := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact hcollision ⟨i.val, j.val, hne, i.property, j.property, hij⟩
  exact hbad ⟨Fintype.card J, xf, hinj.comp e.symm.injective, hsmall⟩

theorem one_le_countingFactorialIntegral_of_not_finiteSimpleOn (d n : ℕ)
    (μ : CountingConfiguration d) (f : C_c(Rd d × Rd d, ℝ))
    (hf : ∀ p, 0 ≤ f p)
    (hfone : ∀ z ∈ Metric.closedBall (0 : Rd d) (n : ℝ), f (z, z) = 1)
    (hbad : ¬ FiniteSimpleOn d (Metric.closedBall (0 : Rd d) (n : ℝ)) μ.val) :
    1 ≤ countingFactorialIntegral d μ f := by
  obtain ⟨R, hR⟩ := ((f.hasCompactSupport.image continuous_fst).union
    (f.hasCompactSupport.image continuous_snd)).isBounded.exists_norm_le
  obtain ⟨r, hr⟩ := exists_nat_ge (max (n : ℝ) R)
  have hs : tsupport f ⊆ Metric.closedBall (0 : Rd d) (r : ℝ) ×ˢ
      Metric.closedBall (0 : Rd d) (r : ℝ) := fun p hp => ⟨by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hR p.1 (Or.inl ⟨p, hp, rfl⟩)).trans ((le_max_right _ _).trans hr), by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hR p.2 (Or.inr ⟨p, hp, rfl⟩)).trans ((le_max_right _ _).trans hr)⟩
  have hnr : n ≤ r := by exact_mod_cast (le_max_left (n : ℝ) R).trans hr
  obtain ⟨m, x, hx⟩ := μ.property r
  obtain ⟨i, j, hij, hxi, _hxj, hxy⟩ :=
    exists_collision_of_not_finiteSimpleOn d n r m μ.val x hnr hx hbad
  rw [countingFactorialIntegral_eq_sum_of_restrict_eq_tupleCounting d r m μ x f hx hs]
  have hterm (k l : Fin m) : 0 ≤ (if k = l then 0 else f (x k, x l)) := by
    split_ifs <;> first | exact le_rfl | exact hf _
  have hinner := Finset.single_le_sum (s := Finset.univ)
    (fun l _ => hterm i l) (Finset.mem_univ j)
  rw [if_neg hij, ← hxy, hfone (x i) hxi] at hinner
  exact hinner.trans (Finset.single_le_sum (s := Finset.univ)
    (fun k _ => Finset.sum_nonneg (fun l _ => hterm k l)) (Finset.mem_univ i))

/-- Zero expected diagonal mass forces almost-sure simplicity. -/
theorem ae_isSimpleConfiguration_of_expectedFactorialMeasure_diagonal_zero (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hdiag : ∀ n : ℕ, expectedFactorialMeasure d P hsecond
      ((fun z : Rd d => (z, z)) '' Metric.closedBall 0 (n : ℝ)) = 0) :
    ∀ᵐ μ ∂P, IsSimpleConfiguration d μ.val := by
  have hlocal (n : ℕ) : P {μ | ¬ FiniteSimpleOn d
      (Metric.closedBall (0 : Rd d) (n : ℝ)) μ.val} = 0 := by
    refine le_antisymm ?_ bot_le
    apply le_of_forall_gt
    intro ε hε
    let D := (fun z : Rd d => (z, z)) '' Metric.closedBall 0 (n : ℝ)
    have hD : IsCompact D := (isCompact_closedBall (0 : Rd d) (n : ℝ)).image
      (continuous_id.prodMk continuous_id)
    obtain ⟨U, hDU, hU, hMU⟩ := D.exists_isOpen_lt_of_lt (μ :=
      expectedFactorialMeasure d P hsecond) ε (by simpa only [D, hdiag n] using hε)
    obtain ⟨χ, hχD, hχcompact, hχsupport, hχrange⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hD hU hDU
    let F : C_c(Rd d × Rd d, ℝ) := ⟨χ, hχcompact⟩
    have hbound := (integrable_countingFactorialIntegral d P hsecond F).measure_le_integral
      (Eventually.of_forall (fun μ => countingFactorialIntegral_nonneg d μ F
        (fun p => (hχrange p).1)))
      (fun μ hbad => one_le_countingFactorialIntegral_of_not_finiteSimpleOn d n μ F
        (fun p => (hχrange p).1) (fun z hz => hχD ⟨z, hz, rfl⟩) hbad)
    rw [← integral_expectedFactorialMeasure d P hsecond F] at hbound
    refine (hbound.trans (integral_le_measure (fun p _ => (hχrange p).2)
      (fun p hp => ?_))).trans_lt hMU
    exact (image_eq_zero_of_notMem_tsupport (fun h => hp (hχsupport h))).le
  have hae (n : ℕ) : ∀ᵐ μ ∂P,
      FiniteSimpleOn d (Metric.closedBall (0 : Rd d) (n : ℝ)) μ.val := ae_iff.mpr (hlocal n)
  exact (ae_all_iff.mpr hae).mono (fun μ hμ => (locallySimple_iff_simple d μ.val).mp hμ)

/-- The simplicity conclusion in the exact ambient law space of the Showcase. -/
theorem ae_isSimpleConfiguration_map_val_of_expectedFactorialMeasure_diagonal_zero (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (hdiag : ∀ n : ℕ, expectedFactorialMeasure d P hsecond
      ((fun z : Rd d => (z, z)) '' Metric.closedBall 0 (n : ℝ)) = 0) :
    ∀ᵐ μ ∂P.map Subtype.val, IsSimpleConfiguration d μ := by
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_isSimpleConfiguration d)).mpr
    (ae_isSimpleConfiguration_of_expectedFactorialMeasure_diagonal_zero d P hsecond hdiag)

/-- A positive power tail cannot have finite integral above a positive floor. -/
theorem eq_zero_of_le_of_pos_rpow_tail_lintegral_lt_top (s c : ℝ)
    (hs : 0 < s) (hc : 0 < c) (a : ℝ≥0∞) (G : ℝ → ℝ≥0∞)
    (hG : ∀ u ∈ Set.Ioi c, a ≤ G u)
    (hfin : (∫⁻ u in Set.Ioi c, ENNReal.ofReal (u ^ (s / 2 - 1)) * G u) < ∞) :
    a = 0 := by
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi c)] (fun u : ℝ => u ^ (s / 2 - 1)) :=
    ae_restrict_of_forall_mem measurableSet_Ioi
      (fun u hu => Real.rpow_nonneg (hc.le.trans hu.le) _)
  have hm : AEStronglyMeasurable (fun u : ℝ => u ^ (s / 2 - 1))
      (volume.restrict (Set.Ioi c)) := (measurable_id.pow_const _).aestronglyMeasurable
  have htop : (∫⁻ u in Set.Ioi c, ENNReal.ofReal (u ^ (s / 2 - 1))) = ∞ := by
    by_contra hne
    have hi : IntegrableOn (fun u : ℝ => u ^ (s / 2 - 1)) (Set.Ioi c) :=
      ⟨hm, (hasFiniteIntegral_iff_ofReal hnn).mpr (lt_top_iff_ne_top.mpr hne)⟩
    have hb := (integrableOn_Ioi_rpow_iff hc).mp hi
    linarith
  by_contra ha
  have hle : ∞ ≤ ∫⁻ u in Set.Ioi c, ENNReal.ofReal (u ^ (s / 2 - 1)) * G u := by
    calc
      ∞ = (∫⁻ u in Set.Ioi c, ENNReal.ofReal (u ^ (s / 2 - 1))) * a := by
        rw [htop, ENNReal.top_mul ha]
      _ ≤ ∫⁻ u in Set.Ioi c, ENNReal.ofReal (u ^ (s / 2 - 1)) * a :=
        lintegral_mul_const_le a _
      _ ≤ _ := setLIntegral_mono' measurableSet_Ioi
        (fun u hu => mul_le_mul_right (hG u hu) _)
  exact hfin.not_ge hle

/-- A compact Gaussian test detects all coincident pairs in its diagonal core. -/
theorem measure_diagonal_le_lintegral_gaussian (d n : ℕ)
    (Γ : Measure (Rd d × Rd d)) (χ : C_c(Rd d × Rd d, ℝ))
    (hχone : ∀ z ∈ Metric.closedBall (0 : Rd d) (n : ℝ), χ (z, z) = 1) (u : ℝ) :
    Γ ((fun z : Rd d => (z, z)) '' Metric.closedBall 0 (n : ℝ)) ≤
      ∫⁻ p, ENNReal.ofReal (χ p) *
        ENNReal.ofReal (Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ))) ∂Γ := by
  let D := (fun z : Rd d => (z, z)) '' Metric.closedBall 0 (n : ℝ)
  have hD : MeasurableSet D := ((isCompact_closedBall (0 : Rd d) (n : ℝ)).image
    (continuous_id.prodMk continuous_id)).measurableSet
  calc
    Γ D = ∫⁻ _p in D, (1 : ℝ≥0∞) ∂Γ := by simp
    _ = ∫⁻ p in D, ENNReal.ofReal (χ p) *
        ENNReal.ofReal (Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ))) ∂Γ :=
      setLIntegral_congr_fun hD (fun p hp => ?_)
    _ ≤ _ := setLIntegral_le_lintegral _ _
  obtain ⟨z, hz, rfl⟩ := hp
  simp only [hχone z hz, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]

/-- The positive-exponent tail criterion, before any coincident pairs are removed. -/
theorem expectedFactorialMeasure_diagonal_zero_of_pos_gaussian_tail_finite (d : ℕ)
    (P : Measure (CountingConfiguration d))
    (hsecond : ∀ n : ℕ,
      (∫⁻ μ, (μ.val (Metric.closedBall (0 : Rd d) (n : ℝ))) ^ 2 ∂P) < ∞)
    (s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hfinite : ∀ χ : C_c(Rd d × Rd d, ℝ), (∀ p, 0 ≤ χ p) →
      (∫⁻ u in Set.Ioi c, ENNReal.ofReal (u ^ (s / 2 - 1)) *
        ∫⁻ p, ENNReal.ofReal (χ p) *
          ENNReal.ofReal (Real.exp (-u * ‖p.2 - p.1‖ ^ (2 : ℕ)))
          ∂expectedFactorialMeasure d P hsecond) < ∞) :
    ∀ n : ℕ, expectedFactorialMeasure d P hsecond
      ((fun z : Rd d => (z, z)) '' Metric.closedBall 0 (n : ℝ)) = 0 := by
  intro n
  obtain ⟨χ, hχone, hχcompact, _hχsupport, hχrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      ((isCompact_closedBall (0 : Rd d) (n : ℝ)).image
        (continuous_id.prodMk continuous_id)) isOpen_univ (Set.subset_univ _)
  exact eq_zero_of_le_of_pos_rpow_tail_lintegral_lt_top s c hs hc _ _
    (fun u _ => measure_diagonal_le_lintegral_gaussian d n _ ⟨χ, hχcompact⟩
      (fun z hz => hχone ⟨z, hz, rfl⟩) u)
    (hfinite ⟨χ, hχcompact⟩ (fun p => (hχrange p).1))

end Riesz.Configuration
