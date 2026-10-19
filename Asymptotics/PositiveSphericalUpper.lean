import Riesz.Stationary.PositiveFiniteCell

/-! Actual finite-cell transport for the positive spherical upper construction. -/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Negative
open scoped ENNReal Classical

namespace Riesz.Configuration

def finiteCellTransportLaw (d e : ℕ) (Q : ConfigurationLaw d)
    (T : Rd d → Rd e) : ConfigurationLaw e :=
  Q.map (fun μ => μ.map T)

theorem tupleCounting_map_measurable (d e n : ℕ)
    (T : Rd d → Rd e) (hT : Measurable T) (x : Fin n → Rd d) :
    (tupleCounting d n x).map T = tupleCounting e n (fun i => T (x i)) := by
  simp only [tupleCounting,
    Measure.map_finset_sum' (m := fun i : Fin n => Measure.dirac (x i))
      (f := T) hT.aemeasurable,
    Measure.map_dirac' (f := T) hT]

theorem finiteSimple_map_good (d e : ℕ)
    (S : Set (Rd d)) (hS : MeasurableSet S)
    (T : Rd d → Rd e) (hT : Measurable T) (hTi : Set.InjOn T S)
    (hTS : MeasurableSet (T '' S)) (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ < ⊤) :
    IsSimpleConfiguration e (μ.map T) ∧
      (μ.map T) (T '' S)ᶜ = 0 ∧ (μ.map T) Set.univ < ⊤ := by
  rcases hμ with ⟨hμsimple, hμS, hμfin⟩
  obtain ⟨n, x, hx, rfl⟩ := simple_finite_count_representation d μ hμsimple hμfin
  have hxS : ∀ i, x i ∈ S :=
    (tupleCounting_compl_eq_zero_iff d n x S hS).mp hμS
  have hTx : Function.Injective (fun i => T (x i)) :=
    fun i j hij => hx (hTi (hxS i) (hxS j) hij)
  simp only [tupleCounting_map_measurable d e n T hT x]
  exact ⟨tupleCounting_simple e n _ hTx,
    (tupleCounting_compl_eq_zero_iff e n _ (T '' S) hTS).mpr
      (fun i => ⟨x i, hxS i, rfl⟩),
    (tupleCounting_univ e n _).trans_lt (ENNReal.natCast_lt_top n)⟩

theorem windowPairIntegral_map_finiteSimple (d e : ℕ)
    (S : Set (Rd d)) (hS : MeasurableSet S)
    (T : Rd d → Rd e) (hT : Measurable T) (hTi : Set.InjOn T S)
    (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ < ⊤)
    (k : Rd e × Rd e → ℝ≥0∞) :
    windowPairIntegral e k (μ.map T) =
      windowPairIntegral d (fun p => k (T p.1, T p.2)) μ := by
  obtain ⟨n, x, hx, rfl⟩ := simple_finite_count_representation d μ hμ.1 hμ.2.2
  have hxS : ∀ i, x i ∈ S :=
    (tupleCounting_compl_eq_zero_iff d n x S hS).mp hμ.2.1
  have hTx : Function.Injective (fun i => T (x i)) :=
    fun i j hij => hx (hTi (hxS i) (hxS j) hij)
  rw [tupleCounting_map_measurable d e n T hT x]
  exact (tupleCounting_offSite_lintegral e n (fun i => T (x i)) hTx k).trans
    (tupleCounting_offSite_lintegral d n x hx (fun p => k (T p.1, T p.2))).symm

theorem finiteCellTransportLaw_probability (d e : ℕ) (Q : ConfigurationLaw d)
    [IsProbabilityMeasure Q] (T : Rd d → Rd e) (hT : Measurable T) :
    IsProbabilityMeasure (finiteCellTransportLaw d e Q T) := by
  exact Measure.isProbabilityMeasure_map (Measure.measurable_map T hT).aemeasurable

theorem finiteCellTransportLaw_good (d e : ℕ) (Q : ConfigurationLaw d)
    (S : Set (Rd d)) (hS : MeasurableSet S)
    (T : Rd d → Rd e) (hT : Measurable T) (hTi : Set.InjOn T S)
    (hTS : MeasurableSet (T '' S))
    (hQ : ∀ᵐ μ ∂Q, IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ < ⊤) :
    ∀ᵐ η ∂finiteCellTransportLaw d e Q T,
      IsSimpleConfiguration e η ∧ η (T '' S)ᶜ = 0 ∧ η Set.univ < ⊤ := by
  exact (ae_map_iff (Measure.measurable_map T hT).aemeasurable
    (measurableSet_windowFiniteGood e (T '' S) hTS)).mpr
      (hQ.mono (fun μ hμ => finiteSimple_map_good d e S hS T hT hTi hTS μ hμ))

theorem finiteCellTransportLaw_mean (d e : ℕ)
    (Q : ConfigurationLaw d) (ν : Measure (Rd d))
    (T : Rd d → Rd e) (hT : Measurable T)
    (hmean : ∀ D, MeasurableSet D → (∫⁻ μ, μ D ∂Q) = ν D)
    (D : Set (Rd e)) (hD : MeasurableSet D) :
    (∫⁻ η, η D ∂finiteCellTransportLaw d e Q T) = (ν.map T) D := by
  rw [finiteCellTransportLaw,
    lintegral_map (Measure.measurable_coe hD) (Measure.measurable_map T hT)]
  simp_rw [Measure.map_apply hT hD]
  exact hmean (T ⁻¹' D) (hT hD)

theorem map_univ_count (d e : ℕ) (T : Rd d → Rd e) (hT : Measurable T)
    (μ : Measure (Rd d)) : (μ.map T) Set.univ = μ Set.univ := by
  rw [Measure.map_apply hT MeasurableSet.univ, Set.preimage_univ]

theorem finiteCellTransportLaw_countSquare (d e : ℕ) (Q : ConfigurationLaw d)
    (T : Rd d → Rd e) (hT : Measurable T) :
    (∫⁻ η, (η Set.univ)^(2 : ℕ) ∂finiteCellTransportLaw d e Q T) =
      ∫⁻ μ, (μ Set.univ)^(2 : ℕ) ∂Q := by
  rw [finiteCellTransportLaw,
    lintegral_map ((Measure.measurable_coe MeasurableSet.univ).pow_const 2)
      (Measure.measurable_map T hT)]
  simp_rw [map_univ_count d e T hT]

theorem finiteCellTransportLaw_pair (d e : ℕ) (Q : ConfigurationLaw d)
    (S : Set (Rd d)) (hS : MeasurableSet S)
    (T : Rd d → Rd e) (hT : Measurable T) (hTi : Set.InjOn T S)
    (hTS : MeasurableSet (T '' S))
    (hQ : ∀ᵐ μ ∂Q, IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ < ⊤)
    (k : Rd e × Rd e → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ η, windowPairIntegral e k η ∂finiteCellTransportLaw d e Q T) =
      ∫⁻ μ, windowPairIntegral d (fun p => k (T p.1, T p.2)) μ ∂Q := by
  have hgood := finiteCellTransportLaw_good d e Q S hS T hT hTi hTS hQ
  have hpair : AEMeasurable (windowPairIntegral e k)
      (finiteCellTransportLaw d e Q T) :=
    aemeasurable_windowPairIntegral_of_simple e _ (hgood.mono (fun _ h => h.1)) k hk
  exact (lintegral_map' hpair (Measure.measurable_map T hT).aemeasurable).trans
    (lintegral_congr_ae (hQ.mono (fun μ hμ =>
      windowPairIntegral_map_finiteSimple d e S hS T hT hTi μ hμ k)))

theorem positive_kernel_relative_distortion
    (s δ r ρ : ℝ) (hs : 0 < s)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hr : 0 ≤ r) (hρ : 0 ≤ ρ)
    (hlo : (1 - δ) * r ≤ ρ) (hhi : ρ ≤ (1 + δ) * r) :
    (1 + δ)^(-s) * K_s s r ≤ K_s s ρ ∧
      K_s s ρ ≤ (1 - δ)^(-s) * K_s s r := by
  have hm : 0 < 1 - δ := sub_pos.mpr hδ1
  have hp : 0 < 1 + δ := by linarith only [hδ0]
  by_cases hz : r = 0
  · have hρz : ρ = 0 := le_antisymm (by simpa only [hz, mul_zero] using hhi) hρ
    simp [hz, hρz, positive_K_s_zero s hs]
  have hrp : 0 < r := by positivity
  have hrhop : 0 < ρ := (mul_pos hm hrp).trans_le hlo
  constructor
  · simpa only [K_s, Real.mul_rpow hp.le hr, mul_div_assoc] using
      div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hrhop hhi (neg_nonpos.mpr hs.le)) hs.le
  · simpa only [K_s, Real.mul_rpow hm.le hr, mul_div_assoc] using
      div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (mul_pos hm hrp) hlo
          (neg_nonpos.mpr hs.le)) hs.le

theorem centered_pack_bound (c e q : ℝ) (hq : q ≤ 1) (he : 0 ≤ e) :
    q * (c + e) ≤ c + (1 - q) * |c| + e := by
  have hc := mul_le_mul_of_nonneg_left (neg_le_abs c) (sub_nonneg.mpr hq)
  nlinarith only [hc, mul_le_mul_of_nonneg_right hq he]

theorem positive_centered_distortion_bound
    (s δ A B A' B' a : ℝ) (hs : 0 < s) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a)
    (hupper : A' ≤ (1 - δ)^(-s) * A)
    (hlower : (1 + δ)^(-s) * B ≤ B') :
    0 ≤ (((1 - δ)^(-s) - 1) * A + (1 - (1 + δ)^(-s)) * B) / a ∧
    (A' - B') / a ≤ (A - B) / a +
      (((1 - δ)^(-s) - 1) * A + (1 - (1 + δ)^(-s)) * B) / a := by
  have hα : 1 ≤ (1 - δ)^(-s) := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos
      (sub_pos.mpr hδ1) (sub_le_self 1 hδ0) (neg_nonpos.mpr hs.le)
  have hβ : (1 + δ)^(-s) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos
      zero_lt_one (le_add_of_nonneg_right hδ0) (neg_nonpos.mpr hs.le)
  refine ⟨div_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr hα) hA)
    (mul_nonneg (sub_nonneg.mpr hβ) hB)) ha.le, ?_⟩
  rw [← add_div, div_le_div_iff_of_pos_right ha]
  nlinarith only [hupper, hlower]

theorem windowPairIntegral_le_mul_of_finiteSimple (d : ℕ)
    (S : Set (Rd d)) (hS : MeasurableSet S) (μ : Measure (Rd d))
    (hμ : IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ < ⊤)
    (k l : Rd d × Rd d → ℝ≥0∞) (c : ℝ≥0∞)
    (hkl : ∀ x ∈ S, ∀ y ∈ S, k (x, y) ≤ c * l (x, y)) :
    windowPairIntegral d k μ ≤ c * windowPairIntegral d l μ := by
  obtain ⟨n, x, hx, rfl⟩ := simple_finite_count_representation d μ hμ.1 hμ.2.2
  have hxS : ∀ i, x i ∈ S :=
    (tupleCounting_compl_eq_zero_iff d n x S hS).mp hμ.2.1
  rw [tupleCounting_offSite_lintegral d n x hx k, tupleCounting_offSite_lintegral d n x hx l]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
    (fun j _ => hkl (x i) (hxS i) (x j) (hxS j)))

theorem finiteCellTransportLaw_pair_le (d e : ℕ) (Q : ConfigurationLaw d)
    (S : Set (Rd d)) (hS : MeasurableSet S)
    (T : Rd d → Rd e) (hT : Measurable T) (hTi : Set.InjOn T S)
    (hTS : MeasurableSet (T '' S))
    (hQ : ∀ᵐ μ ∂Q, IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ < ⊤)
    (k : Rd d × Rd d → ℝ≥0∞) (l : Rd e × Rd e → ℝ≥0∞) (hl : Measurable l)
    (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hkl : ∀ x ∈ S, ∀ y ∈ S, l (T x, T y) ≤ c * k (x, y)) :
    (∫⁻ η, windowPairIntegral e l η ∂finiteCellTransportLaw d e Q T) ≤
      c * ∫⁻ μ, windowPairIntegral d k μ ∂Q := by
  rw [finiteCellTransportLaw_pair d e Q S hS T hT hTi hTS hQ l hl]
  exact (lintegral_mono_ae (hQ.mono (fun μ hμ =>
    windowPairIntegral_le_mul_of_finiteSimple d S hS μ hμ
      (fun p => l (T p.1, T p.2)) k c hkl))).trans_eq
        (lintegral_const_mul' c (fun μ => windowPairIntegral d k μ) hc)

theorem transported_restrict_background_bounds (d e : ℕ)
    (ν : Measure (Rd d)) [SFinite ν] (S : Set (Rd d)) (hS : MeasurableSet S)
    (T : Rd d → Rd e) (hT : Measurable T)
    (k : Rd d × Rd d → ℝ≥0∞) (l : Rd e × Rd e → ℝ≥0∞) (hl : Measurable l)
    (α β : ℝ≥0∞) (hα : α ≠ ⊤) (hβ : β ≠ ⊤)
    (hlo : ∀ x ∈ S, ∀ y ∈ S, β * k (x, y) ≤ l (T x, T y))
    (hhi : ∀ x ∈ S, ∀ y ∈ S, l (T x, T y) ≤ α * k (x, y)) :
    β * (∫⁻ p, k p ∂(ν.restrict S).prod (ν.restrict S)) ≤
        (∫⁻ p, l p ∂((ν.restrict S).map T).prod ((ν.restrict S).map T)) ∧
    (∫⁻ p, l p ∂((ν.restrict S).map T).prod ((ν.restrict S).map T)) ≤
        α * ∫⁻ p, k p ∂(ν.restrict S).prod (ν.restrict S) := by
  rw [Measure.map_prod_map (ν.restrict S) (ν.restrict S) hT hT,
    lintegral_map hl (hT.prodMap hT), Measure.prod_restrict]
  have hmem : ∀ᵐ p ∂(ν.prod ν).restrict (S.prod S), p.1 ∈ S ∧ p.2 ∈ S :=
    ae_restrict_mem (hS.prod hS)
  exact ⟨(lintegral_const_mul' β k hβ).symm.trans_le
      (lintegral_mono_ae (hmem.mono (fun p hp => hlo p.1 hp.1 p.2 hp.2))),
    (lintegral_mono_ae (hmem.mono (fun p hp => hhi p.1 hp.1 p.2 hp.2))).trans_eq
      (lintegral_const_mul' α k hα)⟩

/-- A deterministic kernel comparison gives finite energy and a centered bound
for the actual pushed law. No transported mean or energy bound is assumed. -/
theorem finiteCellTransportLaw_centered_energy (d e : ℕ)
    (ν : Measure (Rd d)) [SFinite ν] (Q : ConfigurationLaw d)
    (S : Set (Rd d)) (hS : MeasurableSet S)
    (T : Rd d → Rd e) (hT : Measurable T) (hTi : Set.InjOn T S)
    (hTS : MeasurableSet (T '' S))
    (hQ : ∀ᵐ μ ∂Q, IsSimpleConfiguration d μ ∧ μ Sᶜ = 0 ∧ μ Set.univ < ⊤)
    (k : Rd d × Rd d → ℝ≥0∞) (hk : Measurable k)
    (l : Rd e × Rd e → ℝ≥0∞) (hl : Measurable l)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hlo : ∀ x ∈ S, ∀ y ∈ S, ENNReal.ofReal β * k (x, y) ≤ l (T x, T y))
    (hhi : ∀ x ∈ S, ∀ y ∈ S, l (T x, T y) ≤ ENNReal.ofReal α * k (x, y))
    (hpair : (∫⁻ μ, windowPairIntegral d k μ ∂Q) ≠ ⊤)
    (hbackground : (∫⁻ p, k p ∂(ν.restrict S).prod (ν.restrict S)) ≠ ⊤) :
    (∫⁻ η, windowPairIntegral e l η ∂finiteCellTransportLaw d e Q T) ≠ ⊤ ∧
    (∫⁻ p, l p ∂((ν.restrict S).map T).prod ((ν.restrict S).map T)) ≠ ⊤ ∧
    Integrable (cellRealEnergy e l) (finiteCellTransportLaw d e Q T) ∧
    (∫ η, cellRealEnergy e l η ∂finiteCellTransportLaw d e Q T) -
        (∫⁻ p, l p ∂((ν.restrict S).map T).prod ((ν.restrict S).map T)).toReal ≤
      α * (∫ μ, cellRealEnergy d k μ ∂Q) -
        β * (∫⁻ p, k p ∂(ν.restrict S).prod (ν.restrict S)).toReal := by
  have hupper := finiteCellTransportLaw_pair_le d e Q S hS T hT hTi hTS hQ
    k l hl (ENNReal.ofReal α) ENNReal.ofReal_ne_top hhi
  have hbg := transported_restrict_background_bounds d e ν S hS T hT k l hl
    (ENNReal.ofReal α) (ENNReal.ofReal β) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hlo hhi
  have htarget := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpair) hupper
  have htargetBg := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbackground) hbg.2
  have hsourceMeas := aemeasurable_windowPairIntegral_of_simple d Q
    (hQ.mono (fun _ h => h.1)) k hk
  have htargetMeas := aemeasurable_windowPairIntegral_of_simple e _
    ((finiteCellTransportLaw_good d e Q S hS T hT hTi hTS hQ).mono (fun _ h => h.1)) l hl
  have hrealUpper : (∫⁻ η, windowPairIntegral e l η ∂finiteCellTransportLaw d e Q T).toReal ≤
      α * (∫⁻ μ, windowPairIntegral d k μ ∂Q).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpair) hupper
  have hrealLower : β * (∫⁻ p, k p ∂(ν.restrict S).prod (ν.restrict S)).toReal ≤
      (∫⁻ p, l p ∂((ν.restrict S).map T).prod ((ν.restrict S).map T)).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hβ] using
      ENNReal.toReal_mono htargetBg hbg.1
  refine ⟨htarget, htargetBg, integrable_toReal_of_lintegral_ne_top htargetMeas htarget, ?_⟩
  simpa only [cellRealEnergy, integral_toReal htargetMeas (ae_lt_top' htargetMeas htarget),
    integral_toReal hsourceMeas (ae_lt_top' hsourceMeas hpair)] using
      sub_le_sub hrealUpper hrealLower

end Riesz.Configuration
