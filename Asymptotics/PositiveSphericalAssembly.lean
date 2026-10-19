import Riesz.Asymptotics.PositiveSphericalCell
import Riesz.Asymptotics.CountRepairIntegral
import Riesz.Asymptotics.SphericalOptimalLower
import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.BigOperators.Fin

/-! Actual independent finite-cell laws for the positive spherical upper bound. -/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Negative Riesz.Stationary Riesz.Geometry
open ProbabilityTheory Filter
open scoped ENNReal Classical Topology

namespace Riesz.Configuration

theorem independentAmbientSumLaw_pair_centered_add_ennreal (d : ℕ)
    (T F : ConfigurationLaw d) [IsProbabilityMeasure T] [IsProbabilityMeasure F]
    (a b : FiniteMeasure (Rd d))
    (hmeanT : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂T) = (a : Measure (Rd d)) D)
    (hmeanF : ∀ D, MeasurableSet D → (∫⁻ η, η D ∂F) = (b : Measure (Rd d)) D)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ ζ, windowPairIntegral d k ζ ∂independentAmbientSumLaw d T F) +
      cellMeanCrossIntegral d k a a + cellMeanCrossIntegral d k b b ≤
        (∫⁻ μ, windowPairIntegral d k μ ∂T) +
          (∫⁻ η, windowPairIntegral d k η ∂F) +
          cellMeanCrossIntegral d k (a + b : Measure (Rd d)) (a + b : Measure (Rd d)) := by
  have h0 : ∀ p, cellOffsiteKernel d k p ≤ k p :=
    fun p => if h : p.1 = p.2 then
      (show cellOffsiteKernel d k p = 0 from if_pos h).trans_le bot_le
    else (show cellOffsiteKernel d k p = k p from if_neg h).le
  rw [independentAmbientSumLaw_pair_offsite d T F a b hmeanT hmeanF k hk,
    cellMeanCrossIntegral_add_square]
  calc
    _ ≤ (((∫⁻ μ, windowPairIntegral d k μ ∂T) +
          (∫⁻ η, windowPairIntegral d k η ∂F) +
          cellMeanCrossIntegral d k a b + cellMeanCrossIntegral d k b a) +
          cellMeanCrossIntegral d k a a) + cellMeanCrossIntegral d k b b :=
      add_le_add (add_le_add
        (add_le_add (add_le_add le_rfl (lintegral_mono h0)) (lintegral_mono h0)) le_rfl) le_rfl
    _ = _ := by ac_rfl

theorem independentAmbientSumLaw_centered_energy_add (d : ℕ)
    (T F : ConfigurationLaw d) [IsProbabilityMeasure T] [IsProbabilityMeasure F]
    (a b : FiniteMeasure (Rd d))
    (hmeanT : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂T) = (a : Measure (Rd d)) D)
    (hmeanF : ∀ D, MeasurableSet D → (∫⁻ η, η D ∂F) = (b : Measure (Rd d)) D)
    (hTs : ∀ᵐ μ ∂T, IsSimpleConfiguration d μ)
    (hFs : ∀ᵐ μ ∂F, IsSimpleConfiguration d μ)
    (hCs : ∀ᵐ μ ∂independentAmbientSumLaw d T F, IsSimpleConfiguration d μ)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k)
    (hTp : (∫⁻ μ, windowPairIntegral d k μ ∂T) ≠ ⊤)
    (hFp : (∫⁻ μ, windowPairIntegral d k μ ∂F) ≠ ⊤)
    (hBg : cellMeanCrossIntegral d k (a + b : Measure (Rd d))
      (a + b : Measure (Rd d)) ≠ ⊤) :
    (∫⁻ μ, windowPairIntegral d k μ ∂independentAmbientSumLaw d T F) ≠ ⊤ ∧
      Integrable (cellRealEnergy d k) (independentAmbientSumLaw d T F) ∧
      (∫ μ, cellRealEnergy d k μ ∂independentAmbientSumLaw d T F) -
        (cellMeanCrossIntegral d k (a + b : Measure (Rd d)) (a + b : Measure (Rd d))).toReal ≤
          ((∫ μ, cellRealEnergy d k μ ∂T) - (cellMeanCrossIntegral d k a a).toReal) +
          ((∫ μ, cellRealEnergy d k μ ∂F) - (cellMeanCrossIntegral d k b b).toReal) := by
  have hENN := independentAmbientSumLaw_pair_centered_add_ennreal
    d T F a b hmeanT hmeanF k hk
  have hRight : ((∫⁻ μ, windowPairIntegral d k μ ∂T) +
      (∫⁻ μ, windowPairIntegral d k μ ∂F)) +
        cellMeanCrossIntegral d k (a + b : Measure (Rd d)) (a + b : Measure (Rd d)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hTp, hFp⟩, hBg⟩
  obtain ⟨hLeft, hBbb⟩ := ENNReal.add_ne_top.mp (ne_top_of_le_ne_top hRight hENN)
  obtain ⟨hCp, hBaa⟩ := ENNReal.add_ne_top.mp hLeft
  have ⟨hTmeas, hFmeas, hCmeas⟩ := And.intro
    (aemeasurable_windowPairIntegral_of_simple d T hTs k hk)
    (And.intro (aemeasurable_windowPairIntegral_of_simple d F hFs k hk)
      (aemeasurable_windowPairIntegral_of_simple d _ hCs k hk))
  have hr : (∫⁻ μ, windowPairIntegral d k μ ∂independentAmbientSumLaw d T F).toReal +
      (cellMeanCrossIntegral d k a a).toReal + (cellMeanCrossIntegral d k b b).toReal ≤
        (∫⁻ μ, windowPairIntegral d k μ ∂T).toReal +
          (∫⁻ μ, windowPairIntegral d k μ ∂F).toReal +
          (cellMeanCrossIntegral d k (a + b : Measure (Rd d)) (a + b : Measure (Rd d))).toReal := by
    simpa only [ENNReal.toReal_add hLeft hBbb, ENNReal.toReal_add hCp hBaa,
      ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hTp, hFp⟩) hBg,
      ENNReal.toReal_add hTp hFp] using ENNReal.toReal_mono hRight hENN
  refine ⟨hCp, integrable_toReal_of_lintegral_ne_top hCmeas hCp, ?_⟩
  simp only [cellRealEnergy,
    integral_toReal hTmeas (ae_lt_top' hTmeas hTp),
    integral_toReal hFmeas (ae_lt_top' hFmeas hFp),
    integral_toReal hCmeas (ae_lt_top' hCmeas hCp)]
  linarith only [hr]

private theorem cellMeanCrossIntegral_left_le_add_square (d : ℕ)
    (k : Rd d × Rd d → ℝ≥0∞) (a b : FiniteMeasure (Rd d)) :
    cellMeanCrossIntegral d k a a ≤
      cellMeanCrossIntegral d k (a + b : Measure (Rd d)) (a + b : Measure (Rd d)) := by
  rw [cellMeanCrossIntegral_add_square]
  exact le_add_right (le_add_right (le_add_right le_rfl))

private theorem positiveLaw_massReal_memLp_two (d : ℕ) (Q : ConfigurationLaw d)
    (hsecond : (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂Q) < ⊤) :
    MemLp (fun μ => μ.real Set.univ) 2 Q := by
  have hm : Measurable (fun μ : Measure (Rd d) => μ Set.univ) :=
    Measure.measurable_coe MeasurableSet.univ
  have hsq : Integrable (fun μ : Measure (Rd d) => (μ Set.univ).toReal^2) Q := by
    simpa only [ENNReal.toReal_pow] using
      integrable_toReal_of_lintegral_ne_top (hm.pow_const 2).aemeasurable hsecond.ne
  exact (memLp_two_iff_integrable_sq hm.ennreal_toReal.aestronglyMeasurable).mpr hsq

theorem independentAmbientSumLaw_massReal_variance_add
    (d : ℕ) (T F : ConfigurationLaw d)
    [IsProbabilityMeasure T] [IsProbabilityMeasure F]
    (hT : (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂T) < ⊤)
    (hF : (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂F) < ⊤) :
    variance (fun μ => μ.real Set.univ) (independentAmbientSumLaw d T F) =
      variance (fun μ => μ.real Set.univ) T +
        variance (fun μ => μ.real Set.univ) F := by
  let r : Measure (Rd d) → ℝ := fun μ => μ.real Set.univ
  have hr : Measurable r := (Measure.measurable_coe MeasurableSet.univ).ennreal_toReal
  have hfinite (Q : ConfigurationLaw d)
      (hQ : (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂Q) < ⊤) :
      ∀ᵐ μ ∂Q, μ Set.univ ≠ ⊤ :=
    (ae_lt_top' ((Measure.measurable_coe MeasurableSet.univ).pow_const 2).aemeasurable hQ.ne).mono
      (fun μ hμ => ((ENNReal.pow_lt_top_iff.mp hμ).resolve_right (by decide)).ne)
  have hfst : ∀ᵐ z : Measure (Rd d) × Measure (Rd d) ∂T.prod F,
      z.1 Set.univ ≠ ⊤ :=
    ae_of_ae_map (μ := T.prod F) (f := Prod.fst)
      (p := fun μ : Measure (Rd d) => μ Set.univ ≠ ⊤) measurable_fst.aemeasurable (by
      simpa only [(measurePreserving_fst (μ := T) (ν := F)).map_eq] using hfinite T hT)
  have hsnd : ∀ᵐ z : Measure (Rd d) × Measure (Rd d) ∂T.prod F,
      z.2 Set.univ ≠ ⊤ :=
    ae_of_ae_map (μ := T.prod F) (f := Prod.snd)
      (p := fun μ : Measure (Rd d) => μ Set.univ ≠ ⊤) measurable_snd.aemeasurable (by
      simpa only [(measurePreserving_snd (μ := T) (ν := F)).map_eq] using hfinite F hF)
  have hadd : (r ∘ (fun z : Measure (Rd d) × Measure (Rd d) => z.1 + z.2)) =ᵐ[T.prod F]
      (fun z => r z.1 + r z.2) :=
    (hfst.and hsnd).mono (fun z h =>
      (congrArg ENNReal.toReal (Measure.add_apply z.1 z.2 Set.univ)).trans
        (ENNReal.toReal_add h.1 h.2))
  calc
    _ = variance (r ∘ (fun z : Measure (Rd d) × Measure (Rd d) => z.1 + z.2))
        (T.prod F) := variance_map hr.aemeasurable (measurable_ambientPairSum d).aemeasurable
    _ = variance (fun z => r z.1 + r z.2) (T.prod F) := variance_congr hadd
    _ = _ := variance_add_prod
      (positiveLaw_massReal_memLp_two d T hT) (positiveLaw_massReal_memLp_two d F hF)

def positiveIndependentLaw (d : ℕ) : (n : ℕ) → (Fin n → ConfigurationLaw d) → ConfigurationLaw d
  | 0, _ => Measure.dirac (0 : Measure (Rd d))
  | n + 1, Q => independentAmbientSumLaw d
      (positiveIndependentLaw d n (fun i => Q i.castSucc)) (Q (Fin.last n))

theorem positiveIndependentLaw_certificate (d n : ℕ) (Q : Fin n → ConfigurationLaw d)
    (a : Fin n → FiniteMeasure (Rd d)) (S : Set (Rd d)) (hS : MeasurableSet S)
    (hprob : ∀ i, IsProbabilityMeasure (Q i))
    (hgood : ∀ i, ∀ᵐ μ ∂Q i,
      IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ < ⊤)
    (hmean : ∀ i D, MeasurableSet D → (∫⁻ μ, μ D ∂Q i) = (a i : Measure (Rd d)) D)
    (hatom : ∀ i, NullSingletonClass (a i : Measure (Rd d)))
    (hsecond : ∀ i, (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂Q i) < ⊤)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k)
    (hpair : ∀ i, (∫⁻ μ, windowPairIntegral d k μ ∂Q i) ≠ ⊤)
    (hbackground : cellMeanCrossIntegral d k
      (∑ i, (a i : Measure (Rd d))) (∑ i, (a i : Measure (Rd d))) ≠ ⊤) :
    IsProbabilityMeasure (positiveIndependentLaw d n Q) ∧
      (∀ᵐ μ ∂positiveIndependentLaw d n Q,
        IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ < ⊤) ∧
      (∀ D, MeasurableSet D →
        (∫⁻ μ, μ D ∂positiveIndependentLaw d n Q) = (∑ i, (a i : Measure (Rd d))) D) ∧
      (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂positiveIndependentLaw d n Q) < ⊤ ∧
      (∫⁻ μ, windowPairIntegral d k μ ∂positiveIndependentLaw d n Q) ≠ ⊤ ∧
      Integrable (cellRealEnergy d k) (positiveIndependentLaw d n Q) ∧
      ((∫ μ, cellRealEnergy d k μ ∂positiveIndependentLaw d n Q) -
        (cellMeanCrossIntegral d k (∑ i, (a i : Measure (Rd d)))
          (∑ i, (a i : Measure (Rd d)))).toReal ≤
          ∑ i, ((∫ μ, cellRealEnergy d k μ ∂Q i) -
            (cellMeanCrossIntegral d k (a i) (a i)).toReal)) ∧
      variance (fun μ => μ.real Set.univ) (positiveIndependentLaw d n Q) =
        ∑ i, variance (fun μ => μ.real Set.univ) (Q i) := by
  induction n with
  | zero =>
    have hzero : ∀ᵐ μ ∂positiveIndependentLaw d 0 Q, μ = 0 := ae_eq_zero_dirac_zero d
    letI : IsProbabilityMeasure (positiveIndependentLaw d 0 Q) :=
      (inferInstance : IsProbabilityMeasure (Measure.dirac (0 : Measure (Rd d))))
    have hEzero : cellRealEnergy d k =ᵐ[positiveIndependentLaw d 0 Q] (fun _ => 0) :=
      hzero.mono (fun μ hμ => by simp [hμ, cellRealEnergy, windowPairIntegral])
    refine ⟨inferInstance, hzero.mono (fun μ hμ => by
      simp [hμ, zero_isSimpleConfiguration]), ?_, ?_, ?_,
      (integrable_const (0 : ℝ)).congr hEzero.symm, ?_, ?_⟩
    · intro D hD
      simp [positiveIndependentLaw, lintegral_dirac_zero_measure]
    · simp [positiveIndependentLaw, lintegral_dirac_zero_measure]
    · simp [positiveIndependentLaw, lintegral_dirac_zero_measure, windowPairIntegral]
    · simp [cellMeanCrossIntegral, integral_eq_zero_of_ae hEzero]
    · calc
        _ = variance (0 : Measure (Rd d) → ℝ) (positiveIndependentLaw d 0 Q) :=
          variance_congr (hzero.mono (fun μ hμ => by simp [hμ, Measure.real]))
        _ = 0 := ProbabilityTheory.variance_zero _
        _ = _ := by simp
  | succ n ih =>
    let aT : FiniteMeasure (Rd d) := ∑ i : Fin n, a i.castSucc
    have hsplit : (∑ i : Fin (n+1), (a i : Measure (Rd d))) =
        (aT : Measure (Rd d)) + (a (Fin.last n) : Measure (Rd d)) := by
      simp only [Fin.sum_univ_castSucc, aT, FiniteMeasure.toMeasure_sum]
    have hpartial : cellMeanCrossIntegral d k aT aT ≠ ⊤ :=
      ne_top_of_le_ne_top (by simpa only [hsplit] using hbackground)
        (cellMeanCrossIntegral_left_le_add_square d k aT (a (Fin.last n)))
    obtain ⟨hTprob, hTgood, hTmean, hTsecond, hTpair, hTint, hTcost, hTvar⟩ :=
      ih (fun i => Q i.castSucc) (fun i => a i.castSucc)
        (fun i => hprob i.castSucc) (fun i => hgood i.castSucc)
        (fun i => hmean i.castSucc) (fun i => hatom i.castSucc)
        (fun i => hsecond i.castSucc) (fun i => hpair i.castSucc)
        (by simpa only [aT, FiniteMeasure.toMeasure_sum] using hpartial)
    letI := hTprob
    letI := hprob (Fin.last n)
    letI := hatom (Fin.last n)
    have hCgood := independentAmbientSumLaw_good d
      (positiveIndependentLaw d n (fun i => Q i.castSucc)) (Q (Fin.last n)) S hS
      hTgood (hgood (Fin.last n)) (a (Fin.last n)) (hmean (Fin.last n))
    obtain ⟨hCpair, hCint, hCcost⟩ := independentAmbientSumLaw_centered_energy_add d
      (positiveIndependentLaw d n (fun i => Q i.castSucc)) (Q (Fin.last n)) aT (a (Fin.last n))
      (fun D hD => by simpa only [aT, FiniteMeasure.toMeasure_sum] using hTmean D hD)
      (hmean (Fin.last n)) (hTgood.mono (fun _ h => h.1))
      ((hgood (Fin.last n)).mono (fun _ h => h.1)) (hCgood.mono (fun _ h => h.1))
      k hk hTpair (hpair (Fin.last n)) (by simpa only [hsplit] using hbackground)
    refine ⟨independentAmbientSumLaw_probability d _ _, hCgood, ?_,
      independentAmbientSumLaw_secondMoment d _ _ hTsecond (hsecond (Fin.last n)),
      hCpair, hCint, ?_, ?_⟩
    · intro D hD
      simpa only [positiveIndependentLaw, Fin.sum_univ_castSucc] using
        independentAmbientSumLaw_mean d _ _
          (∑ i : Fin n, (a i.castSucc : Measure (Rd d))) (a (Fin.last n))
          hTmean (hmean (Fin.last n)) D hD
    · simp only [← FiniteMeasure.toMeasure_sum] at hTcost
      simpa only [positiveIndependentLaw, hsplit, Fin.sum_univ_castSucc] using
        hCcost.trans (add_le_add hTcost le_rfl)
    · simpa only [positiveIndependentLaw, hTvar, Fin.sum_univ_castSucc] using
        independentAmbientSumLaw_massReal_variance_add d
          (positiveIndependentLaw d n (fun i => Q i.castSucc)) (Q (Fin.last n))
          hTsecond (hsecond (Fin.last n))

def positiveAmbientSphere (d : ℕ) : Set (Rd (d + 1)) := {x | ‖x‖ = 1}

theorem measurableSet_positiveAmbientSphere (d : ℕ) :
    MeasurableSet (positiveAmbientSphere d) := by
  exact measurableSet_eq_fun continuous_norm.measurable measurable_const

def positiveSphericalMean (d N : ℕ) (C : Set (Sphere d)) : FiniteMeasure (Rd (d + 1)) :=
  ⟨(ENNReal.ofReal (N : ℝ) • (sphericalMeasure d).restrict C).map Subtype.val, by
    letI : IsFiniteMeasure (ENNReal.ofReal (N : ℝ) • (sphericalMeasure d).restrict C) :=
      ((sphericalMeasure d).restrict C).smul_finite ENNReal.ofReal_ne_top
    exact Measure.isFiniteMeasure_map _ _⟩

theorem sphericalCellKernel_homogeneous (d : ℕ) (s R : ℝ) (hR : 0 < R)
    (p : Rd (d + 1) × Rd (d + 1)) :
    sphericalCellKernel d s R p = ENNReal.ofReal (R^(-s)) * positiveCellKernel (d + 1) s p := by
  simp only [sphericalCellKernel, positiveCellKernel, K_s,
    Real.mul_rpow hR.le (norm_nonneg _), mul_div_assoc,
    ENNReal.ofReal_mul (Real.rpow_nonneg hR.le (-s))]

theorem positive_sphereKernel_lintegral_section (d : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (x : Sphere d) :
    (∫⁻ y, ENNReal.ofReal (K_s s (chord d x y)) ∂sphericalMeasure d) =
      ENNReal.ofReal (V_K d s) := by
  simpa only [sphericalMeasure_kernel_integral d hd s hsd hs.ne' x] using
    (ofReal_integral_eq_lintegral_ofReal
      (sphericalMeasure_kernel_integrable d hd s hsd hs.ne' x)
      (Filter.Eventually.of_forall (fun y => div_nonneg
        (Real.rpow_nonneg (norm_nonneg _) (-s)) hs.le))).symm

theorem sphericalCellKernel_sphere_lintegral_section (d : ℕ) (hd : 2 ≤ d)
    (s R : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (hR : 0 < R) (x : Sphere d) :
    (∫⁻ y : Sphere d, sphericalCellKernel d s R (x.val, y.val) ∂sphericalMeasure d) =
      ENNReal.ofReal (R^(-s)) * ENNReal.ofReal (V_K d s) := by
  simp_rw [sphericalCellKernel_homogeneous d s R hR]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hnorm : ∀ y : Sphere d, positiveCellKernel (d + 1) s (x.val, y.val) =
      ENNReal.ofReal (K_s s (chord d x y)) :=
    fun y => congrArg (fun r => ENNReal.ofReal (K_s s r)) (norm_sub_rev y.val x.val)
  simp_rw [hnorm, positive_sphereKernel_lintegral_section d hd s hs hsd x]

theorem positiveSphericalMean_full_background (d N : ℕ) (hd : 2 ≤ d)
    (s R : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (hR : 0 < R) :
    cellMeanCrossIntegral (d + 1) (sphericalCellKernel d s R)
      (positiveSphericalMean d N Set.univ) (positiveSphericalMean d N Set.univ) =
        ENNReal.ofReal (R^(-s) * ((N : ℝ)^2 * V_K d s)) := by
  let μ : Measure (Sphere d) := ENNReal.ofReal (N : ℝ) • sphericalMeasure d
  letI : IsFiniteMeasure μ := (sphericalMeasure d).smul_finite ENNReal.ofReal_ne_top
  have hμ : (positiveSphericalMean d N Set.univ : Measure (Rd (d + 1))) =
      μ.map Subtype.val := by simp [positiveSphericalMean, μ]
  rw [cellMeanCrossIntegral, hμ,
    Measure.map_prod_map μ μ continuous_subtype_val.measurable continuous_subtype_val.measurable,
    lintegral_map (measurable_sphericalCellKernel d s R)
      (continuous_subtype_val.measurable.prodMap continuous_subtype_val.measurable)]
  change (∫⁻ p : Sphere d × Sphere d, sphericalCellKernel d s R (p.1.val, p.2.val) ∂μ.prod μ) = _
  rw [lintegral_prod (μ := μ) (ν := μ)
    (fun p : Sphere d × Sphere d => sphericalCellKernel d s R (p.1.val, p.2.val))
    ((measurable_sphericalCellKernel d s R).comp
      ((continuous_subtype_val.measurable : Measurable (fun x : Sphere d => x.val)).prodMap
        continuous_subtype_val.measurable)).aemeasurable]
  simp_rw [μ, lintegral_smul_measure, smul_eq_mul,
    sphericalCellKernel_sphere_lintegral_section d hd s R hs hsd hR]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR.le (-s)),
    ENNReal.ofReal_mul (sq_nonneg (N : ℝ)), ENNReal.ofReal_pow (Nat.cast_nonneg N)]
  simp only [pow_two, mul_left_comm, mul_assoc]

theorem positiveSphericalMean_nullSingletonClass (d N : ℕ) (hd : 2 ≤ d)
    (C : Set (Sphere d)) :
    NullSingletonClass (positiveSphericalMean d N C : Measure (Rd (d + 1))) := by
  letI := sphericalMeasure_nullSingletonClass d hd
  refine ⟨fun x => ?_⟩
  change ((ENNReal.ofReal (N : ℝ) • (sphericalMeasure d).restrict C).map Subtype.val) {x} = 0
  rw [Measure.map_apply continuous_subtype_val.measurable (measurableSet_singleton x),
    Measure.smul_apply, smul_eq_mul]
  have hsub : (Subtype.val ⁻¹' {x} : Set (Sphere d)).Subsingleton :=
    fun p hp q hq => Subtype.val_injective
      ((Set.mem_singleton_iff.mp hp).trans (Set.mem_singleton_iff.mp hq).symm)
  rw [hsub.measure_zero ((sphericalMeasure d).restrict C), mul_zero]

theorem positiveSphericalMean_concentrated (d N : ℕ) (C : Set (Sphere d)) :
    (positiveSphericalMean d N C : Measure (Rd (d + 1))) (positiveAmbientSphere d)ᶜ = 0 := by
  change ((ENNReal.ofReal (N : ℝ) • (sphericalMeasure d).restrict C).map Subtype.val)
    (positiveAmbientSphere d)ᶜ = 0
  rw [Measure.map_apply continuous_subtype_val.measurable (measurableSet_positiveAmbientSphere d).compl]
  have hempty : (Subtype.val ⁻¹' (positiveAmbientSphere d)ᶜ : Set (Sphere d)) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hx x.property)
  rw [hempty, measure_empty]

theorem retained_chart_complement_subset (d n : ℕ)
    (D : Fin n → Set (Rd d)) (F : Fin n → Rd d → Sphere d)
    (ell : ℝ) (I : Fin n → Finset (GridIndex d)) :
    (⋃ i, ⋃ z ∈ I i, F i '' latticeCell d ell 0 z)ᶜ ⊆
      (⋃ i, F i '' D i)ᶜ ∪
        ⋃ i, F i '' (D i \ ⋃ z ∈ I i, latticeCell d ell 0 z) := by
  intro y hy
  by_cases hyD : y ∈ ⋃ i, F i '' D i
  · right
    obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hyD
    refine Set.mem_iUnion.mpr ⟨i, x, ⟨hx, ?_⟩, rfl⟩
    exact fun hxcovered => hy (Set.mem_iUnion.mpr ⟨i,
      Set.mem_iUnion₂.mpr (by
        obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hxcovered
        exact ⟨z, hz, x, hxz, rfl⟩)⟩)
  · exact Or.inl hyD

theorem eventually_exists_retained_spherical_cells (d n : ℕ)
    (D : Fin n → Set (Rd d)) (F : Fin n → Rd d → Sphere d)
    (hDopen : ∀ i, IsOpen (D i)) (hDbdd : ∀ i, Bornology.IsBounded (D i))
    (harea : ∀ i E, MeasurableSet E → E ⊆ D i →
      sphericalMeasure d (F i '' E) =
        (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E)
    (ell : ℕ → ℝ) (hell : ∀ N, 0 < ell N) (hmesh : Tendsto ell atTop (𝓝 0))
    (eta : ℝ) (heta : 0 < eta)
    (hcover : sphericalMeasure d (⋃ i, F i '' D i)ᶜ < ENNReal.ofReal (eta/2)) :
    ∀ᶠ N in atTop, ∃ I : Fin n → Finset (GridIndex d),
      (∀ i z, z ∈ I i → closure (latticeCell d (ell N) 0 z) ⊆ D i) ∧
      sphericalMeasure d (⋃ i, ⋃ z ∈ I i, F i '' latticeCell d (ell N) 0 z)ᶜ <
        ENNReal.ofReal eta := by
  choose I hI hlim using fun i =>
    exists_finite_interiorGrid_almost_cover d (D i) (hDopen i) (hDbdd i) ell hell hmesh
  have hκ : (ENNReal.ofReal (omega d))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (sphericalArea_pos d)).ne'
  have hsum : Tendsto (fun N => ∑ i : Fin n, (ENNReal.ofReal (omega d))⁻¹ *
      (volume : Measure (Rd d)) (D i \ ⋃ z ∈ I i N, latticeCell d (ell N) 0 z))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ =>
        ENNReal.Tendsto.const_mul (hlim i) (Or.inr hκ))
  filter_upwards [(tendsto_order.mp hsum).2
    (ENNReal.ofReal (eta/2)) (ENNReal.ofReal_pos.mpr (half_pos heta))] with N hN
  refine ⟨fun i => I i N, fun i z hz => (hI i N z).mp hz, ?_⟩
  have hb := (measure_mono (μ := sphericalMeasure d)
    (retained_chart_complement_subset d n D F (ell N) (fun i => I i N))).trans
      (measure_union_le _ _)
  have hb' := hb.trans (add_le_add le_rfl (measure_iUnion_fintype_le (sphericalMeasure d)
    (fun i => F i '' (D i \ ⋃ z ∈ I i N, latticeCell d (ell N) 0 z))))
  have himage (i : Fin n) : sphericalMeasure d
      (F i '' (D i \ ⋃ z ∈ I i N, latticeCell d (ell N) 0 z)) =
        (ENNReal.ofReal (omega d))⁻¹ *
          (volume : Measure (Rd d)) (D i \ ⋃ z ∈ I i N, latticeCell d (ell N) 0 z) :=
    harea i _ ((hDopen i).measurableSet.diff (MeasurableSet.iUnion fun z =>
      MeasurableSet.iUnion fun _ => latticeCell_measurable d (ell N) 0 z)) Set.sdiff_subset
  have hh : ENNReal.ofReal (eta/2) + ENNReal.ofReal (eta/2) = ENNReal.ofReal eta := by
    rw [← ENNReal.ofReal_add (half_pos heta).le (half_pos heta).le, add_halves]
  simp only [himage] at hb'
  exact hb'.trans_lt (by simpa only [hh] using ENNReal.add_lt_add hcover hN)

theorem sphericalTuple_cellRealEnergy (d M : ℕ) (s R : ℝ)
    (hs : 0 < s) (hR : 0 < R) (x : SphereConfiguration d M) :
    cellRealEnergy (d+1) (sphericalCellKernel d s R)
      (tupleCounting (d+1) M (fun i => (x.val i).val)) =
        R^(-s) * Riesz.Energy.kernelEnergy d s M x := by
  rw [cellRealEnergy, tupleCounting_offSite_lintegral (d+1) M
    (fun i => (x.val i).val) (Subtype.val_injective.comp x.property)]
  rw [ENNReal.toReal_sum (f := fun i : Fin M => ∑ j ∈ Finset.univ.erase i,
    sphericalCellKernel d s R ((x.val i).val, (x.val j).val))
    (fun i _ => ENNReal.sum_ne_top.mpr (fun j _ => ENNReal.ofReal_ne_top))]
  have hr (i : Fin M) : (∑ j ∈ Finset.univ.erase i,
      sphericalCellKernel d s R ((x.val i).val, (x.val j).val)).toReal =
        ∑ j ∈ Finset.univ.erase i,
          (sphericalCellKernel d s R ((x.val i).val, (x.val j).val)).toReal :=
    ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)
  simp_rw [hr, sphericalCellKernel_homogeneous d s R hR, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hR.le (-s))]
  have hk (i j : Fin M) : (positiveCellKernel (d+1) s ((x.val i).val, (x.val j).val)).toReal =
      K_s s (chord d (x.val i) (x.val j)) := by
    simpa only [positiveCellKernel, chord, K_s, norm_sub_rev] using
      ENNReal.toReal_ofReal (div_nonneg
        (Real.rpow_nonneg (norm_nonneg ((x.val j).val - (x.val i).val)) (-s)) hs.le)
  simp_rw [hk, ← Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_erase Finset.univ
    (f := fun j => if i = j then 0 else K_s s (chord d (x.val i) (x.val j)))
    (a := i) (if_pos rfl)]
  exact Finset.sum_congr rfl (fun j hj =>
    (if_neg (Ne.symm (Finset.ne_of_mem_erase hj))).symm)

theorem positive_sphere_measure_scaled_count_repair_bound
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d:ℝ))
    (N : ℕ) (hN : 2 ≤ N) (R : ℝ) (hR : 0 < R)
    (μ : Measure (Rd (d+1)))
    (hμ : IsSimpleConfiguration (d+1) μ ∧
      μ (positiveAmbientSphere d)ᶜ = 0 ∧ μ Set.univ < ⊤) :
    R^(-s) * (E_K d s N - V_K d s * (N:ℝ)^2) ≤
      cellRealEnergy (d+1) (sphericalCellKernel d s R) μ -
        (R^(-s)*V_K d s) * (μ.real Set.univ)^2 +
      (2*Problem1.part5_energy_constants_positive d s*R^(-s)) *
        ((N:ℝ)^(s/(d:ℝ)) * |μ.real Set.univ - (N:ℝ)| +
          (N:ℝ)^(s/(d:ℝ)-1) * (μ.real Set.univ - (N:ℝ))^2) := by
  obtain ⟨M, x, hx, hrep⟩ := simple_finite_count_representation (d+1) μ hμ.1 hμ.2.2
  have hxs : ∀ i, x i ∈ positiveAmbientSphere d :=
    (tupleCounting_compl_eq_zero_iff (d+1) M x _
      (measurableSet_positiveAmbientSphere d)).mp (hrep ▸ hμ.2.1)
  let x' : SphereConfiguration d M :=
    ⟨fun i => ⟨x i, hxs i⟩, fun i j h => hx (congrArg Subtype.val h)⟩
  have hmass : μ.real Set.univ = (M : ℝ) := by
    simp only [Measure.real, hrep, tupleCounting_univ, ENNReal.toReal_natCast]
  have henergy : cellRealEnergy (d+1) (sphericalCellKernel d s R) μ =
      R^(-s) * Riesz.Energy.kernelEnergy d s M x' := by
    simpa only [hrep] using sphericalTuple_cellRealEnergy d M s R hs hR x'
  have hC : 0 ≤ 2 * Problem1.part5_energy_constants_positive d s * R^(-s) :=
    mul_nonneg (mul_nonneg (by norm_num)
      ((Problem1.part5_energy_constant_signs d hd).1 s hs hsd).le)
      (Real.rpow_nonneg hR.le (-s))
  have hp : s / (d : ℝ) ≤ 1 :=
    ((div_lt_one (Nat.cast_pos.mpr (show 0 < d by omega))).mpr hsd).le
  rw [hmass, henergy]
  nlinarith only [positive_sphere_scaled_count_repair_bound d hd s hs hsd N M hN R hR x',
    mul_le_mul_of_nonneg_left (Riesz.Asymptotics.countRepairCost_le_moments
      (N : ℝ) (M : ℝ) (s / (d : ℝ)) (Nat.cast_pos.mpr (by omega))
      (Nat.cast_nonneg M) hp) hC]

theorem positive_sphere_law_scaled_count_repair_bound
    (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs : 0 < s) (hsd : s < (d:ℝ))
    (N : ℕ) (hN : 2 ≤ N) (R : ℝ) (hR : 0 < R)
    (Γ : ConfigurationLaw (d+1)) [IsProbabilityMeasure Γ]
    (hgood : ∀ᵐ μ ∂Γ, IsSimpleConfiguration (d+1) μ ∧
      μ (positiveAmbientSphere d)ᶜ = 0 ∧ μ Set.univ < ⊤)
    (hsecond : (∫⁻ μ, (μ Set.univ)^(2:ℕ) ∂Γ) < ⊤)
    (hmean : (∫ μ, μ.real Set.univ ∂Γ) = (N:ℝ))
    (henergy : Integrable (cellRealEnergy (d+1) (sphericalCellKernel d s R)) Γ) :
    R^(-s) * (E_K d s N - V_K d s * (N:ℝ)^2) ≤
      (∫ μ, cellRealEnergy (d+1) (sphericalCellKernel d s R) μ ∂Γ) -
        (R^(-s)*V_K d s) * (N:ℝ)^2 +
      (2*Problem1.part5_energy_constants_positive d s*R^(-s)) *
        ((N:ℝ)^(s/(d:ℝ)) * Real.sqrt (variance (fun μ => μ.real Set.univ) Γ) +
          (N:ℝ)^(s/(d:ℝ)-1) * variance (fun μ => μ.real Set.univ) Γ) := by
  let r : Measure (Rd (d+1)) → ℝ := fun μ => μ.real Set.univ
  have hr : MemLp r 2 Γ := positiveLaw_massReal_memLp_two (d+1) Γ hsecond
  have hdev : MemLp (fun μ => r μ - (N : ℝ)) 2 Γ := hr.sub (memLp_const (N : ℝ))
  have hvar : (∫ μ, (r μ - (N : ℝ))^2 ∂Γ) = variance r Γ := by
    simpa only [r, hmean] using (variance_eq_integral hr.aemeasurable).symm
  have hsq : (N : ℝ)^2 ≤ ∫ μ, (r μ)^2 ∂Γ := by
    simpa only [variance_eq_sub hr, Pi.pow_apply, r, hmean, sub_nonneg] using
      ProbabilityTheory.variance_nonneg r Γ
  have habs : Integrable (fun μ => |r μ - (N : ℝ)|) Γ := by
    simpa only [Real.norm_eq_abs] using (MemLp.integrable (q := 2) (by norm_num) hdev).norm
  have hmoments : Integrable (fun μ =>
      (N : ℝ)^(s/(d : ℝ)) * |r μ - (N : ℝ)| +
        (N : ℝ)^(s/(d : ℝ)-1) * (r μ - (N : ℝ))^2) Γ :=
    (habs.const_mul _).add (hdev.integrable_sq.const_mul _)
  have hint := integral_mono_ae
    (integrable_const (R^(-s) * (E_K d s N - V_K d s * (N : ℝ)^2)))
    ((henergy.sub (hr.integrable_sq.const_mul (R^(-s)*V_K d s))).add
      (hmoments.const_mul (2*Problem1.part5_energy_constants_positive d s*R^(-s))))
    (hgood.mono (fun μ hμ => positive_sphere_measure_scaled_count_repair_bound
      d hd s hs hsd N hN R hR μ hμ))
  simp only [Pi.add_apply, Pi.sub_apply] at hint
  rw [integral_const, probReal_univ, one_smul,
    integral_add (f := fun μ => cellRealEnergy (d+1) (sphericalCellKernel d s R) μ -
      (R^(-s)*V_K d s) * (r μ)^2)
      (henergy.sub (hr.integrable_sq.const_mul (R^(-s)*V_K d s)))
      (hmoments.const_mul (2*Problem1.part5_energy_constants_positive d s*R^(-s))),
    integral_sub henergy (hr.integrable_sq.const_mul (R^(-s)*V_K d s)),
    integral_const_mul, integral_const_mul,
    integral_add (habs.const_mul _) (hdev.integrable_sq.const_mul _),
    integral_const_mul, integral_const_mul, hvar] at hint
  have hB : 0 ≤ R^(-s)*V_K d s :=
    mul_nonneg (Real.rpow_nonneg hR.le (-s))
      (Riesz.Asymptotics.positiveExponent_background_pos d s (by omega) hs hsd).le
  have habsbound : (∫ μ, |r μ - (N : ℝ)| ∂Γ) ≤ Real.sqrt (variance r Γ) := by
    simpa only [hvar] using Riesz.Asymptotics.integral_abs_le_sqrt_integral_sq Γ _ hdev
  have hC : 0 ≤ 2 * Problem1.part5_energy_constants_positive d s * R^(-s) :=
    mul_nonneg (mul_nonneg (by norm_num)
      ((Problem1.part5_energy_constant_signs d hd).1 s hs hsd).le)
      (Real.rpow_nonneg hR.le (-s))
  exact hint.trans (add_le_add
    (sub_le_sub le_rfl (mul_le_mul_of_nonneg_left hsq hB))
    (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left habsbound
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)) le_rfl) hC))

theorem positiveSphericalMean_partition (d N n : ℕ) (C : Fin n → Set (Sphere d))
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j))) :
    (∑ i, (positiveSphericalMean d N (C i) : Measure (Rd (d+1)))) +
      (positiveSphericalMean d N (⋃ i, C i)ᶜ : Measure (Rd (d+1))) =
        (positiveSphericalMean d N Set.univ : Measure (Rd (d+1))) := by
  have hrestrict : (∑ i, (sphericalMeasure d).restrict (C i)) +
      (sphericalMeasure d).restrict (⋃ i, C i)ᶜ = sphericalMeasure d := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisjoint hC,
      Measure.restrict_add_restrict_compl (MeasurableSet.iUnion hC)]
  simpa [positiveSphericalMean, smul_add, Finset.smul_sum,
    Measure.map_add _ _ continuous_subtype_val.measurable,
    Measure.map_finset_sum' (f := (Subtype.val : Sphere d → Rd (d+1)))
      continuous_subtype_val.measurable.aemeasurable] using
    congrArg (fun μ : Measure (Sphere d) => (ENNReal.ofReal (N : ℝ) • μ).map Subtype.val) hrestrict

theorem finiteCellTransportLaw_massReal_variance (d e : ℕ)
    (Q : ConfigurationLaw d) (T : Rd d → Rd e) (hT : Measurable T) :
    variance (fun μ => μ.real Set.univ) (finiteCellTransportLaw d e Q T) =
      variance (fun μ => μ.real Set.univ) Q := by
  rw [finiteCellTransportLaw, variance_map (X := fun μ : Measure (Rd e) => μ.real Set.univ)
    (Measure.measurable_coe MeasurableSet.univ).ennreal_toReal.aemeasurable
    (Measure.measurable_map T hT).aemeasurable]
  exact variance_congr (Filter.Eventually.of_forall (fun μ =>
    congrArg ENNReal.toReal (map_univ_count d e T hT μ)))

theorem diffuseFillerLaw_massReal_variance_le_quarter (d : ℕ)
    (a : FiniteMeasure (Rd d)) [NullSingletonClass (a : Measure (Rd d))] :
    variance (fun μ => μ.real Set.univ) (diffuseFillerLaw d a) ≤ (1 : ℝ)/4 := by
  have hr : Measurable (fun μ : Measure (Rd d) => μ.real Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).ennreal_toReal
  have hspec := diffuseFillerLaw_spec d a Set.univ MeasurableSet.univ (by simp)
  have hinterval : ∀ᵐ μ ∂diffuseFillerLaw d a, μ.real Set.univ ∈
      Set.Icc (diffuseFillerLowerCount a : ℝ) ((diffuseFillerLowerCount a : ℝ)+1) :=
    hspec.mono (fun μ hμ => hμ.2.2.elim
      (fun hm => by simp [Measure.real, hm])
      (fun hm => by simp [Measure.real, hm, ENNReal.toReal_add]))
  calc
    _ ≤ (((diffuseFillerLowerCount a : ℝ)+1-(diffuseFillerLowerCount a : ℝ))/2)^2 :=
      variance_le_sq_of_bounded hinterval hr.aemeasurable
    _ = (1 : ℝ)/4 := by ring

theorem eventually_exists_positiveSphericalGrid (d : ℕ) (hd : 2 ≤ d)
    (L δ eta : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ < 1) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∃ n : ℕ, ∃ D : Fin n → Set (Rd d),
      ∃ F : Fin n → Rd d → Sphere d, ∃ I : Fin n → Finset (GridIndex d),
      (∀ i, IsOpen (D i) ∧ Bornology.IsBounded (D i) ∧
        ContinuousOn (F i) (D i) ∧ Set.InjOn (F i) (D i)) ∧
      Pairwise (fun i j => Disjoint (F i '' D i) (F j '' D j)) ∧
      (∀ i E, MeasurableSet E → E ⊆ D i → sphericalMeasure d (F i '' E) =
        (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E) ∧
      (∀ i, ∀ x ∈ D i, ∀ y ∈ D i,
        (1-δ)*‖x-y‖ ≤ chord d (F i x) (F i y) ∧
          chord d (F i x) (F i y) ≤ (1+δ)*‖x-y‖) ∧
      (∀ i z, z ∈ I i → closure (latticeCell d (L / sphericalRadius d N) 0 z) ⊆ D i) ∧
      sphericalMeasure d (⋃ i, ⋃ z ∈ I i,
        F i '' latticeCell d (L / sphericalRadius d N) 0 z)ᶜ < ENNReal.ofReal eta := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  obtain ⟨rho, hrho, hsmall, n, U, D, hD, hdisjoint, hcover, harea, hmetric⟩ :=
    exists_finite_disjoint_equalAreaCapPoint_patches k hδ hδ1 (half_pos heta)
  let ell : ℕ → ℝ := fun N => if N = 0 then L else L / sphericalRadius (k+1) N
  have hell (N : ℕ) : 0 < ell N := by
    exact if hN : N = 0 then (by simpa only [ell, if_pos hN] using hL)
      else (by simpa only [ell, if_neg hN] using
        div_pos hL (sphericalRadius_pos (k+1) N (Nat.pos_of_ne_zero hN)))
  have hmesh : Tendsto ell atTop (𝓝 (0 : ℝ)) := by
    apply ((sphericalRadius_tendsto_atTop (k+1) (by omega)).const_div_atTop L).congr'
    exact (eventually_gt_atTop (0 : ℕ)).mono (fun N hN => by simp only [ell, if_neg hN.ne'])
  let F : Fin n → Rd (k+1) → Sphere (k+1) :=
    fun i => rotateSphere (k+1) (U i) ∘ equalAreaCapPoint k
  filter_upwards [eventually_exists_retained_spherical_cells (k+1) n D F
    (fun i => (hD i).1) (fun i => (hD i).2.2.1) harea ell hell hmesh eta heta hcover,
    eventually_gt_atTop (0 : ℕ)] with N hret hN
  obtain ⟨I, hI, hmiss⟩ := hret
  exact ⟨n, D, F, I, fun i => ⟨(hD i).1, (hD i).2.2.1,
      (hD i).2.2.2.1, (hD i).2.2.2.2.1⟩,
    hdisjoint, harea, hmetric,
    by simpa only [ell, if_neg hN.ne'] using hI,
    by simpa only [ell, if_neg hN.ne'] using hmiss⟩

theorem exists_positiveSphericalLaw_of_cells (d : ℕ) (hd : 2 ≤ d)
    (s L R δ : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (hR : 0 < R) (N : ℕ) (hRN : R^d * omega d = N) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (Q : ConfigurationLaw d) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ μ ∂Q, IsSimpleConfiguration d μ ∧ μ (cube d L)ᶜ = 0 ∧ μ Set.univ < ⊤)
    (hmeanQ : ∀ E, MeasurableSet E → (∫⁻ μ, μ E ∂Q) = (volume.restrict (cube d L)) E)
    (hsecondQ : (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂Q) < ⊤)
    (hpairQ : (∫⁻ μ, windowPairIntegral d (positiveCellKernel d s) μ ∂Q) ≠ ⊤)
    (hbackgroundQ : positiveCellBackground d s L ≠ ⊤)
    (m : ℕ) (D : Fin m → Set (Rd d)) (F : Fin m → Rd d → Sphere d)
    (z : Fin m → GridIndex d)
    (hD : ∀ i, MeasurableSet (D i)) (hF : ∀ i, ContinuousOn (F i) (D i))
    (hFi : ∀ i, Set.InjOn (F i) (D i))
    (harea : ∀ i E, MeasurableSet E → E ⊆ D i →
      sphericalMeasure d (F i '' E) =
        (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E)
    (hcell : ∀ i, latticeCell d (L/R) 0 (z i) ⊆ D i)
    (hmetric : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i,
      (1-δ)*‖x-y‖ ≤ chord d (F i x) (F i y) ∧
        chord d (F i x) (F i y) ≤ (1+δ)*‖x-y‖)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (F i '' latticeCell d (L/R) 0 (z i)) (F j '' latticeCell d (L/R) 0 (z j)))) :
    ∃ Γ : ConfigurationLaw (d+1), IsProbabilityMeasure Γ ∧
      (∀ᵐ μ ∂Γ, IsSimpleConfiguration (d+1) μ ∧
        μ (positiveAmbientSphere d)ᶜ = 0 ∧ μ Set.univ < ⊤) ∧
      (∀ E, MeasurableSet E → (∫⁻ μ, μ E ∂Γ) =
        (positiveSphericalMean d N Set.univ : Measure (Rd (d+1))) E) ∧
      (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂Γ) < ⊤ ∧
      (∫⁻ μ, windowPairIntegral (d+1) (sphericalCellKernel d s R) μ ∂Γ) ≠ ⊤ ∧
      Integrable (cellRealEnergy (d+1) (sphericalCellKernel d s R)) Γ ∧
      ((∫ μ, cellRealEnergy (d+1) (sphericalCellKernel d s R) μ ∂Γ) -
        R^(-s) * ((N : ℝ)^2 * V_K d s) ≤
          (m : ℝ) * ((1-δ)^(-s) * (∫ μ, cellRealEnergy d (positiveCellKernel d s) μ ∂Q) -
            (1+δ)^(-s) * (positiveCellBackground d s L).toReal)) ∧
      variance (fun μ => μ.real Set.univ) Γ ≤
        (m : ℝ) * variance (fun μ => μ.real Set.univ) Q + (1 : ℝ)/4 := by
  let T (i : Fin m) := sphericalCellMap d L R (D i) (F i) (z i)
  let C (i : Fin m) := F i '' latticeCell d (L/R) 0 (z i)
  let Λ (i : Fin m) := finiteCellTransportLaw d (d+1) Q (T i)
  let a (i : Fin m) := positiveSphericalMean d N (C i)
  let b := positiveSphericalMean d N (⋃ i, C i)ᶜ
  let aRet : FiniteMeasure (Rd (d+1)) := ∑ i, a i
  have hTmeas (i : Fin m) : Measurable (T i) :=
    measurable_sphericalCellMap d L R (D i) (F i) (hD i) (hF i) (z i)
  have hCmeas (i : Fin m) : MeasurableSet (C i) :=
    (latticeCell_measurable d (L/R) 0 (z i)).image_of_continuousOn_injOn
      ((hF i).mono (hcell i)) ((hFi i).mono (hcell i))
  have hpartition : (aRet : Measure (Rd (d+1))) + (b : Measure (Rd (d+1))) =
      (positiveSphericalMean d N Set.univ : Measure (Rd (d+1))) := by
    simpa only [aRet, FiniteMeasure.toMeasure_sum] using
      positiveSphericalMean_partition d N m C hCmeas hdisjoint
  have hBg : cellMeanCrossIntegral (d+1) (sphericalCellKernel d s R)
      (aRet + b : Measure (Rd (d+1))) (aRet + b : Measure (Rd (d+1))) < ⊤ := by
    simpa only [hpartition, positiveSphericalMean_full_background d N hd s R hs hsd hR] using
      (ENNReal.ofReal_lt_top : ENNReal.ofReal (R^(-s)*((N : ℝ)^2*V_K d s)) < ⊤)
  have hTS (i : Fin m) : T i '' cube d L ⊆ positiveAmbientSphere d :=
    fun _ ⟨x, _, hxy⟩ => hxy ▸
      (sphericalCellChartExtension d (D i) (F i) (sphericalCellAffine d L R (z i) x)).property
  have hΛgood (i : Fin m) : ∀ᵐ μ ∂Λ i, IsSimpleConfiguration (d+1) μ ∧
      μ (positiveAmbientSphere d)ᶜ = 0 ∧ μ Set.univ < ⊤ :=
    (finiteCellTransportLaw_good d (d+1) Q (cube d L) (measurableSet_cube d L)
      (T i) (hTmeas i) (injOn_sphericalCellMap d L R hR (z i) (D i) (F i) (hFi i) (hcell i))
      (measurableSet_sphericalCellMap_image d L R hR (z i) (D i) (F i) (hF i) (hFi i) (hcell i))
      hQ).mono (fun μ hμ => ⟨hμ.1,
        measure_mono_null (Set.compl_subset_compl.mpr (hTS i)) hμ.2.1, hμ.2.2⟩)
  have hΛmean (i : Fin m) (E : Set (Rd (d+1))) (hE : MeasurableSet E) :
      (∫⁻ μ, μ E ∂Λ i) = (a i : Measure (Rd (d+1))) E :=
    sphericalCellTransportLaw_mean d N L R hR hRN (z i) (D i) (F i)
      (hD i) (hF i) (hFi i) (harea i) (hcell i) Q hmeanQ E hE
  have hΛenergy (i : Fin m) := sphericalCellTransportLaw_centered_energy
    d N s L R δ hs hR hRN hδ0 hδ1 (z i) (D i) (F i) (hD i) (hF i) (hFi i)
      (harea i) (hcell i) (hmetric i) Q hQ hpairQ hbackgroundQ
  have hΛsecond (i : Fin m) : (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂Λ i) < ⊤ :=
    (finiteCellTransportLaw_countSquare d (d+1) Q (T i) (hTmeas i)).trans_lt hsecondQ
  have hpartial : cellMeanCrossIntegral (d+1) (sphericalCellKernel d s R)
      (∑ i, (a i : Measure (Rd (d+1)))) (∑ i, (a i : Measure (Rd (d+1)))) ≠ ⊤ := by
    simpa only [aRet, FiniteMeasure.toMeasure_sum] using
      ne_top_of_le_ne_top hBg.ne
        (cellMeanCrossIntegral_left_le_add_square (d+1) (sphericalCellKernel d s R) aRet b)
  obtain ⟨hRetprob, hRetgood, hRetmean, hRetsecond, hRetpair, hRetint, hRetcost, hRetvar⟩ :=
    positiveIndependentLaw_certificate (d+1) m Λ a (positiveAmbientSphere d)
      (measurableSet_positiveAmbientSphere d)
      (fun i => finiteCellTransportLaw_probability d (d+1) Q (T i) (hTmeas i))
      hΛgood hΛmean (fun i => positiveSphericalMean_nullSingletonClass d N hd (C i))
      hΛsecond (sphericalCellKernel d s R) (measurable_sphericalCellKernel d s R)
      (fun i => (hΛenergy i).1) hpartial
  letI := hRetprob
  letI : NullSingletonClass (b : Measure (Rd (d+1))) :=
    positiveSphericalMean_nullSingletonClass d N hd (⋃ i, C i)ᶜ
  have hFillgood : ∀ᵐ μ ∂diffuseFillerLaw (d+1) b,
      IsSimpleConfiguration (d+1) μ ∧ μ (positiveAmbientSphere d)ᶜ = 0 ∧ μ Set.univ < ⊤ :=
    (diffuseFillerLaw_spec (d+1) b (positiveAmbientSphere d)
      (measurableSet_positiveAmbientSphere d)
      (positiveSphericalMean_concentrated d N (⋃ i, C i)ᶜ)).mono (fun μ hμ =>
        ⟨hμ.1, hμ.2.1, hμ.2.2.elim (fun hm => by simp [hm]) (fun hm => by simp [hm])⟩)
  have hΓgood := independentAmbientSumLaw_good (d+1) (positiveIndependentLaw (d+1) m Λ)
    (diffuseFillerLaw (d+1) b) (positiveAmbientSphere d) (measurableSet_positiveAmbientSphere d)
    hRetgood hFillgood b (diffuseFillerLaw_mean (d+1) b)
  obtain ⟨hΓpair, hΓint, hΓcost⟩ := independentAmbientSumLaw_centered_energy (d+1)
    (positiveIndependentLaw (d+1) m Λ) (diffuseFillerLaw (d+1) b) aRet b
      (fun E hE => by simpa only [aRet, FiniteMeasure.toMeasure_sum] using hRetmean E hE)
      (diffuseFillerLaw_mean (d+1) b) (sphericalCellKernel d s R)
      (measurable_sphericalCellKernel d s R)
      (diffuseFillerLaw_pair_lintegral_le (d+1) b (sphericalCellKernel d s R)
        (measurable_sphericalCellKernel d s R)) (lt_top_iff_ne_top.mpr hRetpair) hBg
  refine ⟨independentAmbientSumLaw (d+1) (positiveIndependentLaw (d+1) m Λ)
      (diffuseFillerLaw (d+1) b), independentAmbientSumLaw_probability (d+1) _ _, hΓgood, ?_,
    independentAmbientSumLaw_secondMoment (d+1) _ _ hRetsecond
      (diffuseFillerLaw_secondMoment (d+1) b), hΓpair, hΓint, ?_, ?_⟩
  · exact fun E hE => by
      simpa only [hpartition] using independentAmbientSumLaw_mean (d+1)
        (positiveIndependentLaw (d+1) m Λ) (diffuseFillerLaw (d+1) b) aRet b
        (fun B hB => by simpa only [aRet, FiniteMeasure.toMeasure_sum] using hRetmean B hB)
        (diffuseFillerLaw_mean (d+1) b) E hE
  · have hfullreal : (cellMeanCrossIntegral (d+1) (sphericalCellKernel d s R)
        (aRet+b : Measure (Rd (d+1))) (aRet+b : Measure (Rd (d+1)))).toReal =
          R^(-s) * ((N : ℝ)^2 * V_K d s) := by
      simp only [hpartition, positiveSphericalMean_full_background d N hd s R hs hsd hR,
        ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hR.le (-s))
          (mul_nonneg (sq_nonneg _) (Riesz.Asymptotics.positiveExponent_background_pos
            d s (by omega) hs hsd).le))]
    have hsum : (∑ i, ((∫ μ, cellRealEnergy (d+1) (sphericalCellKernel d s R) μ ∂Λ i) -
        (cellMeanCrossIntegral (d+1) (sphericalCellKernel d s R) (a i) (a i)).toReal)) ≤
          (m : ℝ) * ((1-δ)^(-s) * (∫ μ, cellRealEnergy d (positiveCellKernel d s) μ ∂Q) -
            (1+δ)^(-s) * (positiveCellBackground d s L).toReal) := by
      simpa [Λ, T, a, C, positiveSphericalMean, cellMeanCrossIntegral, nsmul_eq_mul, mul_sub] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hΛenergy i).2.2.2)
    simpa only [hfullreal] using hΓcost.trans
      (by simpa only [aRet, FiniteMeasure.toMeasure_sum] using hRetcost.trans hsum)
  · rw [independentAmbientSumLaw_massReal_variance_add (d+1) _ _ hRetsecond
      (diffuseFillerLaw_secondMoment (d+1) b), hRetvar]
    have hvarΛ (i : Fin m) : variance (fun μ => μ.real Set.univ) (Λ i) =
        variance (fun μ => μ.real Set.univ) Q :=
      finiteCellTransportLaw_massReal_variance d (d+1) Q (T i) (hTmeas i)
    simpa only [hvarΛ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      add_le_add (le_refl (∑ i, variance (fun μ => μ.real Set.univ) (Λ i)))
        (diffuseFillerLaw_massReal_variance_le_quarter (d+1) b)

theorem retained_spherical_cells_pairwise_disjoint (d n : ℕ) (ell : ℝ) (hell : 0 < ell)
    (D : Fin n → Set (Rd d)) (F : Fin n → Rd d → Sphere d)
    (I : Fin n → Finset (GridIndex d)) (hFi : ∀ i, Set.InjOn (F i) (D i))
    (hcell : ∀ i z, z ∈ I i → latticeCell d ell 0 z ⊆ D i)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i '' D i) (F j '' D j))) :
    Pairwise (fun a b : Σ i, ↥(I i) => Disjoint
      (F a.1 '' latticeCell d ell 0 a.2.val) (F b.1 '' latticeCell d ell 0 b.2.val)) := by
  rintro ⟨i, zi⟩ ⟨j, zj⟩ hne
  by_cases hij : i = j
  · subst j
    have hz : zi.val ≠ zj.val := fun h => hne
      (congrArg (fun z : ↥(I i) => (⟨i, z⟩ : Σ j, ↥(I j))) (Subtype.ext h))
    exact (latticeCells_pairwise_disjoint d ell hell 0 hz).image (hFi i)
      (hcell i zi.val zi.property) (hcell i zj.val zj.property)
  · exact (hdisjoint hij).mono (Set.image_mono (hcell i zi.val zi.property))
      (Set.image_mono (hcell j zj.val zj.property))

theorem positiveSphericalMean_cell_mass (d N : ℕ) (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (hRN : R^d * omega d = N) (z : GridIndex d) (D : Set (Rd d))
    (F : Rd d → Sphere d) (hD : MeasurableSet D) (hF : ContinuousOn F D) (hFi : Set.InjOn F D)
    (harea : ∀ E, MeasurableSet E → E ⊆ D → sphericalMeasure d (F '' E) =
      (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E)
    (hcell : latticeCell d (L/R) 0 z ⊆ D) :
    (positiveSphericalMean d N (F '' latticeCell d (L/R) 0 z) : Measure (Rd (d+1))) Set.univ =
      ENNReal.ofReal (L^d) := by
  have hmap : (volume.restrict (cube d L)).map (sphericalCellMap d L R D F z) =
      (positiveSphericalMean d N (F '' latticeCell d (L/R) 0 z) : Measure (Rd (d+1))) := by
    simpa [hRN, positiveSphericalMean] using
      map_cube_volume_sphericalCellMap d L R hR z D F hD hF hFi harea hcell
  rw [← hmap, map_univ_count d (d+1) _ (measurable_sphericalCellMap d L R D F hD hF z),
    Measure.restrict_apply_univ, volume_cube, ← ENNReal.ofReal_pow hL.le]

theorem positiveSphericalMean_mass (d N : ℕ) (C : Set (Sphere d)) :
    (positiveSphericalMean d N C : Measure (Rd (d+1))) Set.univ =
      ENNReal.ofReal (N : ℝ) * sphericalMeasure d C := by
  simp [positiveSphericalMean, Measure.map_apply continuous_subtype_val.measurable,
    Measure.smul_apply]

theorem positiveSphericalMean_partition_mass (d N m : ℕ) (L : ℝ) (hL : 0 < L)
    (C : Fin m → Set (Sphere d)) (hC : ∀ i, MeasurableSet (C i))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hmass : ∀ i, (positiveSphericalMean d N (C i) : Measure (Rd (d+1))) Set.univ =
      ENNReal.ofReal (L^d)) :
    (m : ℝ)*L^d + (N : ℝ)*(sphericalMeasure d).real (⋃ i, C i)ᶜ = (N : ℝ) := by
  have h := congrArg (fun μ : Measure (Rd (d+1)) => μ Set.univ)
    (positiveSphericalMean_partition d N m C hC hdisjoint)
  simp only [Measure.add_apply, Measure.finsetSum_apply, hmass,
    positiveSphericalMean_mass, measure_univ, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  simpa only [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp : (m : ℝ≥0∞) ≠ ∞) ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (pow_nonneg hL.le d),
    ENNReal.toReal_ofReal (Nat.cast_nonneg N), Measure.real] using congrArg ENNReal.toReal h

theorem eventually_exists_positiveSphericalTrial (d : ℕ) (hd : 2 ≤ d)
    (s L δ eta : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ < 1) (heta : 0 < eta)
    (Q : ConfigurationLaw d) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ μ ∂Q, IsSimpleConfiguration d μ ∧ μ (cube d L)ᶜ = 0 ∧ μ Set.univ < ⊤)
    (hmeanQ : ∀ E, MeasurableSet E → (∫⁻ μ, μ E ∂Q) = (volume.restrict (cube d L)) E)
    (hsecondQ : (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂Q) < ⊤)
    (hpairQ : (∫⁻ μ, windowPairIntegral d (positiveCellKernel d s) μ ∂Q) ≠ ⊤)
    (hbackgroundQ : positiveCellBackground d s L ≠ ⊤) :
    ∀ᶠ N : ℕ in atTop, ∃ m : ℕ, ∃ Γ : ConfigurationLaw (d+1),
      IsProbabilityMeasure Γ ∧
      (∀ᵐ μ ∂Γ, IsSimpleConfiguration (d+1) μ ∧
        μ (positiveAmbientSphere d)ᶜ = 0 ∧ μ Set.univ < ⊤) ∧
      (∀ E, MeasurableSet E → (∫⁻ μ, μ E ∂Γ) =
        (positiveSphericalMean d N Set.univ : Measure (Rd (d+1))) E) ∧
      (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂Γ) < ⊤ ∧
      (∫⁻ μ, windowPairIntegral (d+1) (sphericalCellKernel d s (sphericalRadius d N)) μ ∂Γ) ≠ ⊤ ∧
      Integrable (cellRealEnergy (d+1) (sphericalCellKernel d s (sphericalRadius d N))) Γ ∧
      ((∫ μ, cellRealEnergy (d+1) (sphericalCellKernel d s (sphericalRadius d N)) μ ∂Γ) -
        (sphericalRadius d N)^(-s) * ((N : ℝ)^2 * V_K d s) ≤
          (m : ℝ) * ((1-δ)^(-s) * (∫ μ, cellRealEnergy d (positiveCellKernel d s) μ ∂Q) -
            (1+δ)^(-s) * (positiveCellBackground d s L).toReal)) ∧
      variance (fun μ => μ.real Set.univ) Γ ≤
        (m : ℝ) * variance (fun μ => μ.real Set.univ) Q + (1 : ℝ)/4 ∧
      (m : ℝ)*L^d ≤ (N : ℝ) ∧ 1-(m : ℝ)*L^d/(N : ℝ) < eta := by
  filter_upwards [eventually_exists_positiveSphericalGrid d hd L δ eta hL hδ hδ1 heta,
    eventually_gt_atTop (0 : ℕ)] with N hgrid hN
  obtain ⟨n, D, F, I, hD, hdisjoint, harea, hmetric, hcell, hmiss⟩ := hgrid
  let e : Fin (Fintype.card (Σ i, ↥(I i))) ≃ (Σ i, ↥(I i)) :=
    (Fintype.equivFin (Σ i, ↥(I i))).symm
  have hcell' (j : Fin (Fintype.card (Σ i, ↥(I i)))) :
      latticeCell d (L / sphericalRadius d N) 0 (e j).2.val ⊆ D (e j).1 :=
    subset_closure.trans (hcell (e j).1 (e j).2.val (e j).2.property)
  have hdisjoint' : Pairwise (fun i j => Disjoint
      (F (e i).1 '' latticeCell d (L / sphericalRadius d N) 0 (e i).2.val)
      (F (e j).1 '' latticeCell d (L / sphericalRadius d N) 0 (e j).2.val)) :=
    fun i j hij => retained_spherical_cells_pairwise_disjoint d n _
      (div_pos hL (sphericalRadius_pos d N hN)) D F I (fun i => (hD i).2.2.2)
      (fun i z hz => subset_closure.trans (hcell i z hz)) hdisjoint
      (fun h => hij (e.injective h))
  obtain ⟨Γ, hΓprob, hΓgood, hΓmean, hΓsecond, hΓpair, hΓint, hΓcost, hΓvar⟩ :=
    exists_positiveSphericalLaw_of_cells d hd s L (sphericalRadius d N) δ hs hsd
      (sphericalRadius_pos d N hN) N (sphericalRadius_area_normalization d N (by omega)) hδ.le hδ1
      Q hQ hmeanQ hsecondQ hpairQ hbackgroundQ _ (fun j => D (e j).1)
      (fun j => F (e j).1) (fun j => (e j).2.val)
      (fun j => (hD (e j).1).1.measurableSet) (fun j => (hD (e j).1).2.2.1)
      (fun j => (hD (e j).1).2.2.2) (fun j => harea (e j).1) hcell'
      (fun j => hmetric (e j).1) hdisjoint'
  have hmass := positiveSphericalMean_partition_mass d N (Fintype.card (Σ i, ↥(I i))) L hL
    (fun j => F (e j).1 '' latticeCell d (L / sphericalRadius d N) 0 (e j).2.val)
    (fun j => (latticeCell_measurable d _ 0 _).image_of_continuousOn_injOn
      ((hD (e j).1).2.2.1.mono (hcell' j)) ((hD (e j).1).2.2.2.mono (hcell' j)))
    hdisjoint' (fun j => positiveSphericalMean_cell_mass d N L _ hL
      (sphericalRadius_pos d N hN) (sphericalRadius_area_normalization d N (by omega))
      (e j).2.val _ _ (hD (e j).1).1.measurableSet (hD (e j).1).2.2.1
      (hD (e j).1).2.2.2 (harea (e j).1) (hcell' j))
  have hunion : (⋃ j, F (e j).1 '' latticeCell d (L / sphericalRadius d N) 0 (e j).2.val) =
      ⋃ i, ⋃ z ∈ I i, F i '' latticeCell d (L / sphericalRadius d N) 0 z := by
    rw [e.surjective.iUnion_comp (fun a : Σ i, ↥(I i) =>
      F a.1 '' latticeCell d (L / sphericalRadius d N) 0 a.2.val), Set.iUnion_sigma]
    simp only [Set.iUnion_subtype]
  have hmass' : (Fintype.card (Σ i, ↥(I i)) : ℝ)*L^d + (N : ℝ)*
      (sphericalMeasure d).real (⋃ i, ⋃ z ∈ I i,
        F i '' latticeCell d (L / sphericalRadius d N) 0 z)ᶜ = (N : ℝ) :=
    by simpa only [hunion] using hmass
  refine ⟨_, Γ, hΓprob, hΓgood, hΓmean, hΓsecond, hΓpair, hΓint, hΓcost, hΓvar, ?_, ?_⟩
  · nlinarith only [hmass', mul_nonneg (Nat.cast_nonneg N)
      (measureReal_nonneg : 0 ≤ (sphericalMeasure d).real (⋃ i, ⋃ z ∈ I i,
        F i '' latticeCell d (L / sphericalRadius d N) 0 z)ᶜ)]
  · have hratio : 1-(Fintype.card (Σ i, ↥(I i)) : ℝ)*L^d/(N : ℝ) =
        (sphericalMeasure d).real (⋃ i, ⋃ z ∈ I i,
          F i '' latticeCell d (L / sphericalRadius d N) 0 z)ᶜ := by
      field_simp
      linarith only [hmass']
    exact hratio.trans_lt (ENNReal.toReal_lt_of_lt_ofReal hmiss)

theorem positiveSphericalLaw_massReal_integral (d N : ℕ)
    (Γ : ConfigurationLaw (d+1))
    (hmean : ∀ E, MeasurableSet E → (∫⁻ μ, μ E ∂Γ) =
      (positiveSphericalMean d N Set.univ : Measure (Rd (d+1))) E) :
    (∫ μ, μ.real Set.univ ∂Γ) = (N : ℝ) := by
  have h := hmean Set.univ MeasurableSet.univ
  have hfinite : (∫⁻ μ, μ Set.univ ∂Γ) ≠ ⊤ := by
    simp only [h, positiveSphericalMean_mass, measure_univ, mul_one, ENNReal.ofReal_ne_top, ne_eq, not_false_eq_true]
  simpa only [Measure.real, h, positiveSphericalMean_mass, measure_univ, mul_one,
    ENNReal.toReal_ofReal (Nat.cast_nonneg N)] using
    integral_toReal (Measure.measurable_coe MeasurableSet.univ).aemeasurable
      (ae_lt_top' (Measure.measurable_coe MeasurableSet.univ).aemeasurable hfinite)

theorem exists_positive_centered_distortion_parameter (s A B a eps : ℝ)
    (ha : 0 < a) (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      (((1-δ)^(-s)-1)*A+(1-(1+δ)^(-s))*B)/a < eps := by
  have hα : ContinuousAt (fun δ : ℝ => (1-δ)^(-s)) 0 :=
    (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by norm_num))
  have hβ : ContinuousAt (fun δ : ℝ => (1+δ)^(-s)) 0 :=
    (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))
  have hg : ContinuousAt (fun δ : ℝ =>
      (((1-δ)^(-s)-1)*A+(1-(1+δ)^(-s))*B)/a) 0 :=
    (((hα.sub continuousAt_const).mul continuousAt_const).add
      ((continuousAt_const.sub hβ).mul continuousAt_const)).div continuousAt_const ha.ne'
  have hbudget : ∀ᶠ δ in 𝓝[Set.Ioi 0] (0 : ℝ),
      (((1-δ)^(-s)-1)*A+(1-(1+δ)^(-s))*B)/a < eps :=
    nhdsWithin_le_nhds ((tendsto_order.mp hg.tendsto).2 eps (by simpa using heps))
  have hone : ∀ᶠ δ in 𝓝[Set.Ioi 0] (0 : ℝ), δ < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one))
  exact ((show ∀ᶠ δ in 𝓝[Set.Ioi 0] (0 : ℝ), 0 < δ from self_mem_nhdsWithin).and
    (hone.and hbudget)).exists

theorem sphericalRadius_repair_normalization (d N : ℕ) (s : ℝ) (hN : 0 < N) :
    (sphericalRadius d N)^(-s)/(N : ℝ) =
      (omega d)^(s/(d : ℝ))/(N : ℝ)^(1+s/(d : ℝ)) := by
  unfold sphericalRadius
  rw [← Real.rpow_mul (div_nonneg (Nat.cast_nonneg N) (sphericalArea_pos d).le),
    show (1 / (d : ℝ)) * (-s) = -(s / (d : ℝ)) by ring,
    Real.div_rpow (Nat.cast_nonneg N) (sphericalArea_pos d).le,
    Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_neg (sphericalArea_pos d).le,
    Real.rpow_add (Nat.cast_pos.mpr hN), Real.rpow_one]
  field_simp [(Nat.cast_ne_zero.mpr hN.ne' : (N : ℝ) ≠ 0),
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) (s/(d : ℝ))).ne',
    (Real.rpow_pos_of_pos (sphericalArea_pos d) (s/(d : ℝ))).ne']

theorem positive_spherical_upper_of_finite_cell (d : ℕ) (hd : 2 ≤ d)
    (s L b : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) (hL : 0 < L)
    (Q : ConfigurationLaw d) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ μ ∂Q, IsSimpleConfiguration d μ ∧ μ (cube d L)ᶜ = 0 ∧ μ Set.univ < ⊤)
    (hmeanQ : ∀ E, MeasurableSet E → (∫⁻ μ, μ E ∂Q) = (volume.restrict (cube d L)) E)
    (hsecondQ : (∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂Q) < ⊤)
    (hpairQ : (∫⁻ μ, windowPairIntegral d (positiveCellKernel d s) μ ∂Q) ≠ ⊤)
    (hbackgroundQ : positiveCellBackground d s L ≠ ⊤)
    (hb : ((∫ μ, cellRealEnergy d (positiveCellKernel d s) μ ∂Q) -
      (positiveCellBackground d s L).toReal)/L^d < b) :
    ∀ᶠ N : ℕ in atTop, Riesz.Asymptotics.scaledOptimalKernelEnergy d s N < b := by
  let A := ∫ μ, cellRealEnergy d (positiveCellKernel d s) μ ∂Q
  let B := (positiveCellBackground d s L).toReal
  let c := (A-B)/L^d
  have heps : 0 < (b-c)/4 := div_pos (sub_pos.mpr hb) (by norm_num)
  obtain ⟨δ, hδ, hδ1, hδcost⟩ := exists_positive_centered_distortion_parameter
    s A B (L^d) ((b-c)/4) (pow_pos hL d) heps
  have heta : 0 < ((b-c)/4)/(|c|+1) := div_pos heps (by positivity)
  let K := variance (fun μ => μ.real Set.univ) Q / L^d + 1
  have hK : 0 ≤ K := add_nonneg
    (div_nonneg (ProbabilityTheory.variance_nonneg _ _) (pow_pos hL d).le) zero_le_one
  let err : ℕ → ℝ := fun N =>
    (2*Problem1.part5_energy_constants_positive d s*(omega d)^(s/(d : ℝ))) *
      (((N : ℝ)^(s/(d : ℝ))*Real.sqrt (K*(N : ℝ)) +
        (N : ℝ)^(s/(d : ℝ)-1)*(K*(N : ℝ)))/(N : ℝ)^(1+s/(d : ℝ)))
  have hlim : Tendsto err atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (Riesz.Asymptotics.countRepairMomentRatio_tendsto_zero (s/(d : ℝ)) K hK).const_mul
        (2*Problem1.part5_energy_constants_positive d s*(omega d)^(s/(d : ℝ)))
  filter_upwards [eventually_exists_positiveSphericalTrial d hd s L δ (((b-c)/4)/(|c|+1))
    hs hsd hL hδ hδ1 heta Q hQ hmeanQ hsecondQ hpairQ hbackgroundQ,
    (tendsto_order.mp hlim).2 ((b-c)/4) heps, eventually_ge_atTop (2 : ℕ)] with N htrial herr hN
  obtain ⟨m, Γ, hΓprob, hΓgood, hΓmean, hΓsecond, hΓpair, hΓint, hΓcost, hΓvar, hm, hmiss⟩ := htrial
  letI : IsProbabilityMeasure Γ := hΓprob
  have hrepair := positive_sphere_law_scaled_count_repair_bound d hd s hs hsd N hN
    (sphericalRadius d N) (sphericalRadius_pos d N (by omega)) Γ hΓgood hΓsecond
    (positiveSphericalLaw_massReal_integral d N Γ hΓmean) hΓint
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmvar : (m : ℝ)*variance (fun μ => μ.real Set.univ) Q ≤
      (N : ℝ)*(variance (fun μ => μ.real Set.univ) Q/L^d) := by
    calc
      _ = ((m : ℝ)*L^d)*(variance (fun μ => μ.real Set.univ) Q/L^d) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hm
        (div_nonneg (ProbabilityTheory.variance_nonneg _ _) (pow_pos hL d).le)
  have hvar : variance (fun μ => μ.real Set.univ) Γ ≤ K*(N : ℝ) := by
    dsimp only [K]
    nlinarith only [hΓvar, hmvar, show (2 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
  have hpre : (sphericalRadius d N)^(-s)*(E_K d s N - V_K d s*(N : ℝ)^2) ≤
      (m : ℝ)*((1-δ)^(-s)*A-(1+δ)^(-s)*B) +
        (2*Problem1.part5_energy_constants_positive d s*(sphericalRadius d N)^(-s))*
          ((N : ℝ)^(s/(d : ℝ))*Real.sqrt (K*(N : ℝ)) +
            (N : ℝ)^(s/(d : ℝ)-1)*(K*(N : ℝ))) :=
    hrepair.trans (add_le_add (by nlinarith only [hΓcost])
      (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar)
          (Real.rpow_nonneg hNr.le _))
          (mul_le_mul_of_nonneg_left hvar (Real.rpow_nonneg hNr.le _)))
        (mul_nonneg (mul_nonneg (by norm_num)
          ((Problem1.part5_energy_constant_signs d hd).1 s hs hsd).le)
          (Real.rpow_nonneg (sphericalRadius_pos d N (by omega)).le _))))
  have hnormalize : ((2*Problem1.part5_energy_constants_positive d s*(sphericalRadius d N)^(-s))*
      ((N : ℝ)^(s/(d : ℝ))*Real.sqrt (K*(N : ℝ)) +
        (N : ℝ)^(s/(d : ℝ)-1)*(K*(N : ℝ))))/(N : ℝ) = err N := by
    dsimp only [err]
    linear_combination (2*Problem1.part5_energy_constants_positive d s *
      ((N : ℝ)^(s/(d : ℝ))*Real.sqrt (K*(N : ℝ)) +
        (N : ℝ)^(s/(d : ℝ)-1)*(K*(N : ℝ)))) *
      sphericalRadius_repair_normalization d N s (by omega)
  have hscaled : Riesz.Asymptotics.scaledOptimalKernelEnergy d s N ≤
      (m : ℝ)*((1-δ)^(-s)*A-(1+δ)^(-s)*B)/(N : ℝ) + err N := by
    calc
      _ = ((sphericalRadius d N)^(-s)*(E_K d s N - V_K d s*(N : ℝ)^2))/(N : ℝ) := by
        simp only [Riesz.Asymptotics.scaledOptimalKernelEnergy, div_mul_eq_mul_div]
      _ ≤ _ := div_le_div_of_nonneg_right hpre hNr.le
      _ = _ := by rw [add_div, hnormalize]
  have he : 0 ≤ (((1-δ)^(-s)-1)*A+(1-(1+δ)^(-s))*B)/L^d :=
    (positive_centered_distortion_bound s δ A B ((1-δ)^(-s)*A) ((1+δ)^(-s)*B) (L^d)
      hs hδ.le hδ1 (integral_nonneg (fun _ => ENNReal.toReal_nonneg))
      ENNReal.toReal_nonneg (pow_pos hL d) le_rfl le_rfl).1
  have hpack := centered_pack_bound c
    ((((1-δ)^(-s)-1)*A+(1-(1+δ)^(-s))*B)/L^d) ((m : ℝ)*L^d/(N : ℝ))
    ((div_le_one hNr).mpr hm) he
  have hdistid : (m : ℝ)*((1-δ)^(-s)*A-(1+δ)^(-s)*B)/(N : ℝ) =
      ((m : ℝ)*L^d/(N : ℝ)) *
        (c+(((1-δ)^(-s)-1)*A+(1-(1+δ)^(-s))*B)/L^d) := by
    dsimp only [c]
    field_simp [c]
    ring
  have hmisscost : (1-(m : ℝ)*L^d/(N : ℝ))*|c| < (b-c)/4 := by
    calc
      _ ≤ (1-(m : ℝ)*L^d/(N : ℝ))*(|c|+1) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
          (sub_nonneg.mpr ((div_le_one hNr).mpr hm))
      _ < _ := (lt_div_iff₀ (by positivity)).mp hmiss
  linarith only [hscaled, hpack, hdistid, hmisscost, hδcost, herr, heps]

theorem exists_admissible_finite_W_lt (d : ℕ) (hd : 0 < d) (s b : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) (hb : e d s < b) :
    ∃ P : ConfigurationLaw d, Admissible d P ∧ W d s P ≠ ⊤ ∧ (W d s P).toReal < b := by
  have he : eExtended d s < (b : EReal) := by
    simpa only [(positive_constant_finiteness_and_sign d hd s hs hsd).1,
      EReal.coe_lt_coe_iff] using hb
  obtain ⟨w, ⟨P, hP, rfl⟩, hW⟩ := sInf_lt_iff.mp he
  have htop : W d s P ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top b) hW.le
  have hbot : W d s P ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe (c0 d s)).trans_le (c0_le_W d s P))
  exact ⟨P, hP, htop, EReal.coe_lt_coe_iff.mp ((EReal.coe_toReal htop hbot).trans_lt hW)⟩

theorem positive_spherical_upper (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) :
    ∀ b : ℝ, e d s < b →
      ∀ᶠ N : ℕ in atTop, Riesz.Asymptotics.scaledOptimalKernelEnergy d s N < b := by
  intro b hb
  obtain ⟨P, hP, hW, hWb⟩ := exists_admissible_finite_W_lt d (by omega) s b hs hsd hb
  obtain ⟨L, hL, Q, hQprob, hQgood, hQmean, hQsecond, hQpair, hQbackground, hQint, hQcost⟩ :=
    exists_positiveFilledCell_near_optimal d s hs hsd P hP hW ((b-(W d s P).toReal)/2)
      (half_pos (sub_pos.mpr hWb))
  letI : IsProbabilityMeasure Q := hQprob
  apply positive_spherical_upper_of_finite_cell d hd s L b hs hsd hL Q
    hQgood hQmean hQsecond hQpair hQbackground
  simpa only [div_eq_mul_inv, mul_comm] using hQcost.trans_lt
    (show (W d s P).toReal + (b-(W d s P).toReal)/2 < b by linarith only [hWb])

end Riesz.Configuration

namespace Riesz.Asymptotics

/-- The positive branch follows from actual finite-cell laws and spherical trials. -/
theorem positive_analyticClaims (d : ℕ) (hd : 2 ≤ d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) : AnalyticClaims d s :=
  positive_analyticClaims_of_spherical_upper d hd s hs hsd
    (Riesz.Configuration.positive_spherical_upper d hd s hs hsd)

end Riesz.Asymptotics
