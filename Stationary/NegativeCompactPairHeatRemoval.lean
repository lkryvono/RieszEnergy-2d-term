import Riesz.Stationary.CompactPairHeatRemoval
import Riesz.Stationary.NegativeDisplacement

/-! Physical compact-pair heat removal from the original finite energy above -2. -/

noncomputable section

open MeasureTheory Filter RieszShowcase Riesz.Configuration
open scoped ENNReal Classical Topology CompactlySupported

namespace Riesz.Stationary

theorem compactPairHeatRegularization_originalGamma_tendsto_of_neg_two_lt
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (ψ : C_c(Rd d × Rd d, ℝ)) (hψ : ∀ q, 0 ≤ ψ q)
    (f : Rd d → ℝ≥0∞) (hf : Measurable f)
    (M R B : ℝ) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hbound : ∀ a, f a ≤ ENNReal.ofReal M)
    (hsupp : ∀ a, R < ‖a‖ → f a = 0)
    (hfin : (∫⁻ a, f a ∂volume) ≠ ∞)
    (hψbound : ∀ q : Rd d × Rd d,
      ENNReal.ofReal (ψ q) ≤ ENNReal.ofReal B * (f q.1 * f q.2))
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    (∫⁻ q, ENNReal.ofReal (ψ q) ∂originalAdmissibleFactorialMeasure d P hP) ≠ ∞ ∧
      (∫⁻ x, ENNReal.ofReal (ψ (x, x)) ∂volume) ≠ ∞ ∧
      Tendsto (fun n => ∫⁻ q, compactPairHeatRegularization d ((ε n) ^ 2) ψ q
        ∂originalAdmissibleFactorialMeasure d P hP) atTop
          (𝓝 (∫⁻ q, ENNReal.ofReal (ψ q) ∂originalAdmissibleFactorialMeasure d P hP)) ∧
      Tendsto (fun n => ∫⁻ x, compactPairHeatRegularization d ((ε n) ^ 2) ψ (x, x) ∂volume)
        atTop (𝓝 (∫⁻ x, ENNReal.ofReal (ψ (x, x)) ∂volume)) := by
  let Γ := originalAdmissibleFactorialMeasure d P hP
  obtain ⟨D, hD, hEnv⟩ := exists_uniform_nonnegativeHeatWindow_envelope
    d 1 zero_lt_one f M R hM hR hbound hsupp hfin
  simp only [mul_one] at hEnv
  let H := originalHeatEnvelope d (Metric.closedBall (0 : Rd d) (2 * R)) M D 8
  obtain ⟨hΓH, hdiagH⟩ := originalHeatEnvelope_pair_and_diagonal_ne_top
    d P hP (Metric.closedBall 0 (2 * R)) measurableSet_closedBall
      Metric.isBounded_closedBall M D 8 hM hD (by norm_num)
        (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs P hW _ (by positivity))
  have hΓbound : (∫⁻ q, ENNReal.ofReal B * (H q.1 * H q.2) ∂Γ) ≠ ∞ :=
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans_ne
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΓH)
  have hdiagbound : (∫⁻ x, ENNReal.ofReal B * (H x) ^ 2 ∂volume) ≠ ∞ :=
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans_ne
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdiagH)
  have htend : Tendsto (fun n => (ε n) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow two_ne_zero] using hε.pow 2
  have hsmall : ∀ᶠ n in atTop, (ε n) ^ 2 ≤ 1 :=
    (htend.eventually (Iio_mem_nhds zero_lt_one)).mono (fun _ hn => hn.le)
  have hdom (n : ℕ) (hn : (ε n) ^ 2 ≤ 1) (z : Rd d × Rd d) :
      compactPairHeatRegularization d ((ε n) ^ 2) ψ z ≤
        ENNReal.ofReal B * (H z.1 * H z.2) :=
    (compactPairHeatRegularization_le_heatWindow_product d ((ε n) ^ 2) ψ f hf B hψbound z).trans
      (mul_le_mul_right (mul_le_mul'
        (hEnv ((ε n) ^ 2) (sq_pos_of_pos (hεpos n)) hn z.1)
        (hEnv ((ε n) ^ 2) (sq_pos_of_pos (hεpos n)) hn z.2)) (ENNReal.ofReal B))
  have hpoint (z : Rd d × Rd d) :=
    tendsto_compactPairHeatRegularization_of_square_scale d ψ hψ ε hεpos hε z
  have htarget (z : Rd d × Rd d) :
      ENNReal.ofReal (ψ z) ≤ ENNReal.ofReal B * (H z.1 * H z.2) :=
    le_of_tendsto (hpoint z) (hsmall.mono (fun n hn => hdom n hn z))
  refine ⟨ne_top_of_le_ne_top hΓbound (lintegral_mono htarget),
    ne_top_of_le_ne_top hdiagbound (lintegral_mono (fun x => by
      simpa only [pow_two] using htarget (x, x))), ?_, ?_⟩
  · exact tendsto_lintegral_filter_of_dominated_convergence (μ := Γ)
      (fun q => ENNReal.ofReal B * (H q.1 * H q.2))
      (Filter.Eventually.of_forall (fun n => measurable_compactPairHeatRegularization d _ ψ))
      (hsmall.mono (fun n hn => Filter.Eventually.of_forall (hdom n hn)))
      hΓbound (Filter.Eventually.of_forall hpoint)
  · exact tendsto_lintegral_filter_of_dominated_convergence (μ := (volume : Measure (Rd d)))
      (fun x => ENNReal.ofReal B * (H x) ^ 2)
      (Filter.Eventually.of_forall (fun n =>
        (measurable_compactPairHeatRegularization d ((ε n) ^ 2) ψ).comp
          (measurable_id.prodMk measurable_id)))
      (hsmall.mono (fun n hn => Filter.Eventually.of_forall (fun x => by
        simpa only [pow_two] using hdom n hn (x, x))))
      hdiagbound (Filter.Eventually.of_forall (fun x => hpoint (x, x)))


/-- The compact support itself supplies every envelope hypothesis. -/
theorem compactPair_covariance_tendsto_nonneg_of_neg_two_lt
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (ψ : C_c(Rd d × Rd d, ℝ)) (hψ : ∀ q, 0 ≤ ψ q)
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    Integrable ψ (originalAdmissibleFactorialMeasure d P hP) ∧
      (∀ᶠ n in atTop, Integrable (fun q : Rd d × Rd d =>
        ψ q * originalHeatCovariance d P ((ε n) ^ 2) (q.2 - q.1))
          ((volume : Measure (Rd d)).prod volume)) ∧
      Tendsto (fun n => ∫ q : Rd d × Rd d,
        ψ q * originalHeatCovariance d P ((ε n) ^ 2) (q.2 - q.1)
          ∂(volume : Measure (Rd d)).prod volume) atTop
        (𝓝 ((∫ q, ψ q ∂originalAdmissibleFactorialMeasure d P hP) +
          (∫ x : Rd d, ψ (x, x) ∂volume) -
            ∫ q : Rd d × Rd d, ψ q ∂(volume : Measure (Rd d)).prod volume)) := by
  let Γ := originalAdmissibleFactorialMeasure d P hP
  obtain ⟨R₀, hR₀⟩ := ((ψ.hasCompactSupport.image continuous_fst).union
    (ψ.hasCompactSupport.image continuous_snd)).isBounded.exists_norm_le
  let R := max R₀ 1
  let K : Set (Rd d) := Metric.closedBall 0 R
  let f : Rd d → ℝ≥0∞ := K.indicator (fun _ => 1)
  have hK : MeasurableSet K := measurableSet_closedBall
  have hsupport : tsupport ψ ⊆ K ×ˢ K := by
    intro q hq
    constructor
    · simpa only [K, Metric.mem_closedBall, dist_zero_right] using
        (hR₀ q.1 (Or.inl ⟨q, hq, rfl⟩)).trans (le_max_left R₀ 1)
    · simpa only [K, Metric.mem_closedBall, dist_zero_right] using
        (hR₀ q.2 (Or.inr ⟨q, hq, rfl⟩)).trans (le_max_left R₀ 1)
  have hf : Measurable f := measurable_const.indicator hK
  have hbound (a : Rd d) : f a ≤ ENNReal.ofReal 1 := by
    by_cases ha : a ∈ K <;> simp [f, ha]
  have hsupp (a : Rd d) (ha : R < ‖a‖) : f a = 0 := by
    have hnot : a ∉ K := by
      simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using ha
    simp [f, hnot]
  have hfin : (∫⁻ a, f a ∂volume) ≠ ∞ := by
    change (∫⁻ a, K.indicator (fun _ => (1 : ℝ≥0∞)) a ∂volume) ≠ ∞
    rw [lintegral_indicator_fun_one hK]
    exact ((isCompact_closedBall (0 : Rd d) R).measure_lt_top (μ := volume)).ne
  have hψbound (q : Rd d × Rd d) :
      ENNReal.ofReal (ψ q) ≤
        ENNReal.ofReal ‖ψ.toBoundedContinuousFunction‖ * (f q.1 * f q.2) := by
    by_cases hq : q ∈ K ×ˢ K
    · simp only [f, Set.indicator_of_mem hq.1, Set.indicator_of_mem hq.2,
        mul_one]
      exact ENNReal.ofReal_le_ofReal
        ((le_abs_self (ψ q)).trans (by
          simpa only [Real.norm_eq_abs,
            CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
            ψ.toBoundedContinuousFunction.norm_coe_le_norm q))
    · have hz : ψ q = 0 := image_eq_zero_of_notMem_tsupport
        (fun hp => hq (hsupport hp))
      simp only [hz, ENNReal.ofReal_zero, zero_le]
  have hψmeas : Measurable (fun q => ENNReal.ofReal (ψ q)) :=
    ψ.continuous.measurable.ennreal_ofReal
  have hψdiagmeas : Measurable (fun x : Rd d => ENNReal.ofReal (ψ (x, x))) :=
    hψmeas.comp (measurable_id.prodMk measurable_id)
  obtain ⟨hΓfin, hdiagfin, hΓlim, hdiaglim⟩ :=
    compactPairHeatRegularization_originalGamma_tendsto_of_neg_two_lt
      d s hs P hP hW ψ hψ f hf 1 R ‖ψ.toBoundedContinuousFunction‖
        zero_le_one (le_max_right R₀ 1) hbound hsupp hfin hψbound ε hεpos hε
  have hψint : Integrable ψ Γ :=
    (integrable_toReal_of_lintegral_ne_top hψmeas.aemeasurable hΓfin).congr
      (Filter.Eventually.of_forall (fun q => ENNReal.toReal_ofReal (hψ q)))
  have hΓtarget : (∫⁻ q, ENNReal.ofReal (ψ q) ∂Γ).toReal = ∫ q, ψ q ∂Γ :=
    (integral_toReal hψmeas.aemeasurable (ae_lt_top hψmeas hΓfin)).symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall (fun q =>
        ENNReal.toReal_ofReal (hψ q))))
  have hdiagtarget : (∫⁻ x, ENNReal.ofReal (ψ (x, x)) ∂volume).toReal =
      ∫ x : Rd d, ψ (x, x) ∂volume :=
    (integral_toReal hψdiagmeas.aemeasurable
      (ae_lt_top hψdiagmeas hdiagfin)).symm.trans
        (integral_congr_ae (Filter.Eventually.of_forall (fun x =>
          ENNReal.toReal_ofReal (hψ (x, x)))))
  have hΓn : ∀ᶠ n in atTop, (∫⁻ q, compactPairHeatRegularization d ((ε n) ^ 2) ψ q
      ∂Γ) ≠ ∞ :=
    (hΓlim.eventually (Iio_mem_nhds (lt_top_iff_ne_top.mpr hΓfin))).mono
      (fun _ hn => hn.ne)
  have hdiagn : ∀ᶠ n in atTop, (∫⁻ x, compactPairHeatRegularization d ((ε n) ^ 2)
      ψ (x, x) ∂volume) ≠ ∞ :=
    (hdiaglim.eventually (Iio_mem_nhds (lt_top_iff_ne_top.mpr hdiagfin))).mono
      (fun _ hn => hn.ne)
  have hreal := ((ENNReal.tendsto_toReal hΓfin).comp hΓlim).add
    ((ENNReal.tendsto_toReal hdiagfin).comp hdiaglim)
  have hbackground : Tendsto (fun _ : ℕ =>
      ∫ q : Rd d × Rd d, ψ q ∂(volume : Measure (Rd d)).prod volume)
      atTop (𝓝 (∫ q : Rd d × Rd d, ψ q
        ∂(volume : Measure (Rd d)).prod volume)) := tendsto_const_nhds
  have hreal' := hreal.sub hbackground
  rw [hΓtarget, hdiagtarget] at hreal'
  have hcov : ∀ᶠ n in atTop,
      Integrable (fun q : Rd d × Rd d =>
        ψ q * originalHeatCovariance d P ((ε n) ^ 2) (q.2 - q.1))
          ((volume : Measure (Rd d)).prod volume) ∧
      (∫ q : Rd d × Rd d, ψ q * originalHeatCovariance d P ((ε n) ^ 2) (q.2 - q.1)
          ∂(volume : Measure (Rd d)).prod volume) =
        (∫⁻ q, compactPairHeatRegularization d ((ε n) ^ 2) ψ q ∂Γ).toReal +
          (∫⁻ x, compactPairHeatRegularization d ((ε n) ^ 2) ψ (x, x) ∂volume).toReal -
            ∫ q : Rd d × Rd d, ψ q ∂(volume : Measure (Rd d)).prod volume := by
    filter_upwards [hΓn, hdiagn] with n hnΓ hndiag
    exact compactPairHeatRegularization_covariance_integral d P hP ((ε n) ^ 2)
      (sq_pos_of_pos (hεpos n))
      (Q_ne_top_of_W_ne_top_of_neg_two_lt d s hs P hW _
        (one_div_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos (hεpos n)))))
        ψ hψ hnΓ hndiag
  exact ⟨hψint, hcov.mono (fun _ h => h.1),
    hreal'.congr' (hcov.mono (fun _ h => h.2.symm))⟩

/-- Signed compact tests need only the two nonnegative parts, not polarization. -/
theorem compactPair_covariance_tendsto_of_neg_two_lt
    (d : ℕ) (s : ℝ) (hs : -2 < s) (P : ConfigurationLaw d)
    (hP : Admissible d P) (hW : W d s P ≠ ⊤)
    (ψ : C_c(Rd d × Rd d, ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    Integrable ψ (originalAdmissibleFactorialMeasure d P hP) ∧
      Tendsto (fun n => ∫ q : Rd d × Rd d,
        ψ q * originalHeatCovariance d P ((ε n) ^ 2) (q.2 - q.1)
          ∂(volume : Measure (Rd d)).prod volume) atTop
        (𝓝 ((∫ q, ψ q ∂originalAdmissibleFactorialMeasure d P hP) +
          (∫ x : Rd d, ψ (x, x) ∂volume) -
            ∫ q : Rd d × Rd d, ψ q ∂(volume : Measure (Rd d)).prod volume)) := by
  let Γ := originalAdmissibleFactorialMeasure d P hP
  let ψp : C_c(Rd d × Rd d, ℝ) := ψ ⊔ 0
  let ψm : C_c(Rd d × Rd d, ℝ) := (-ψ) ⊔ 0
  have hp (q : Rd d × Rd d) : 0 ≤ ψp q := le_max_right _ _
  have hm (q : Rd d × Rd d) : 0 ≤ ψm q := le_max_right _ _
  have hdecomp (q : Rd d × Rd d) : ψ q = ψp q - ψm q := by
    simpa only [ψp, ψm, CompactlySupportedContinuousMap.sup_apply,
      CompactlySupportedContinuousMap.zero_apply,
      CompactlySupportedContinuousMap.neg_apply] using (max_zero_sub_eq_self (ψ q)).symm
  obtain ⟨hpint, hpevent, hplim⟩ :=
    compactPair_covariance_tendsto_nonneg_of_neg_two_lt d s hs P hP hW ψp hp ε hεpos hε
  obtain ⟨hmint, hmevent, hmlim⟩ :=
    compactPair_covariance_tendsto_nonneg_of_neg_two_lt d s hs P hP hW ψm hm ε hεpos hε
  have hψint : Integrable ψ Γ := (hpint.sub hmint).congr
    (Filter.Eventually.of_forall (fun q => (hdecomp q).symm))
  have hΓid : (∫ q, ψ q ∂Γ) = (∫ q, ψp q ∂Γ) - ∫ q, ψm q ∂Γ :=
    (integral_congr_ae (Filter.Eventually.of_forall hdecomp)).trans
      (integral_sub hpint hmint)
  have hdiagid : (∫ x : Rd d, ψ (x, x) ∂volume) =
      (∫ x : Rd d, ψp (x, x) ∂volume) - ∫ x : Rd d, ψm (x, x) ∂volume :=
    (integral_congr_ae (Filter.Eventually.of_forall (fun x => hdecomp (x, x)))).trans
      (integral_sub (countingDiagonalTest d ψp).integrable
        (countingDiagonalTest d ψm).integrable)
  have hbackid : (∫ q : Rd d × Rd d, ψ q ∂(volume : Measure (Rd d)).prod volume) =
      (∫ q : Rd d × Rd d, ψp q ∂(volume : Measure (Rd d)).prod volume) -
        ∫ q : Rd d × Rd d, ψm q ∂(volume : Measure (Rd d)).prod volume :=
    (integral_congr_ae (Filter.Eventually.of_forall hdecomp)).trans
      (integral_sub ψp.integrable ψm.integrable)
  have htarget :
      ((∫ q, ψp q ∂Γ) + (∫ x : Rd d, ψp (x, x) ∂volume) -
        ∫ q : Rd d × Rd d, ψp q ∂(volume : Measure (Rd d)).prod volume) -
      ((∫ q, ψm q ∂Γ) + (∫ x : Rd d, ψm (x, x) ∂volume) -
        ∫ q : Rd d × Rd d, ψm q ∂(volume : Measure (Rd d)).prod volume) =
      (∫ q, ψ q ∂Γ) + (∫ x : Rd d, ψ (x, x) ∂volume) -
        ∫ q : Rd d × Rd d, ψ q ∂(volume : Measure (Rd d)).prod volume := by
    rw [hΓid, hdiagid, hbackid]
    ring
  have hlim := hplim.sub hmlim
  change Tendsto _ atTop (𝓝 (_ - _)) at hlim
  rw [htarget] at hlim
  refine ⟨hψint, hlim.congr' ?_⟩
  filter_upwards [hpevent, hmevent] with n hpn hmn
  symm
  calc
    _ = ∫ q : Rd d × Rd d,
        (ψp q * originalHeatCovariance d P ((ε n) ^ 2) (q.2 - q.1) -
          ψm q * originalHeatCovariance d P ((ε n) ^ 2) (q.2 - q.1))
            ∂(volume : Measure (Rd d)).prod volume :=
      integral_congr_ae (Filter.Eventually.of_forall (fun q => by rw [hdecomp, sub_mul]))
    _ = _ := integral_sub hpn hmn

end Riesz.Stationary
