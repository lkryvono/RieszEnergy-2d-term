import Riesz.Negative.Translations
import Riesz.Negative.SampledRounding
import Riesz.Asymptotics.PositiveSphericalCell

/-!
Actual bounded signed-energy transport and fixed-count balanced-cell chart laws.
The scalar estimate includes coincident points. Actual transported means,
simplicity, support and energy integrability are obtained from the original
balanced law and the checked spherical chart map.
-/

noncomputable section

open MeasureTheory RieszShowcase Riesz.Configuration Riesz.Stationary Riesz.Geometry
open scoped ENNReal Classical

namespace Riesz.Negative

theorem negative_rpow_relative_error_le (q δ r ρ : ℝ)
    (hq : 0 < q) (hq2 : q < 2) (hδ0 : 0 ≤ δ) (hδh : δ ≤ 1 / 2)
    (hr : 0 ≤ r) (hlo : (1 - δ) * r ≤ ρ) (hhi : ρ ≤ (1 + δ) * r) :
    |ρ ^ q - r ^ q| ≤ 3 * δ * r ^ q := by
  have hm : 0 < 1 - δ := by linarith
  have hp : 0 ≤ 1 + δ := by linarith
  have hbot : 1 - 2 * δ ≤ (1 - δ) ^ q := by
    have h := Real.rpow_le_rpow_of_exponent_ge hm
      (show 1 - δ ≤ 1 by linarith) hq2.le
    rw [Real.rpow_two] at h
    nlinarith [sq_nonneg δ]
  have htop : (1 + δ) ^ q ≤ 1 + 3 * δ := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ 1 + δ by linarith) hq2.le
    rw [Real.rpow_two] at h
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hδh)]
  have hrl := Real.rpow_le_rpow (mul_nonneg hm.le hr) hlo hq.le
  have hrh := Real.rpow_le_rpow ((mul_nonneg hm.le hr).trans hlo) hhi hq.le
  rw [Real.mul_rpow hm.le hr] at hrl
  rw [Real.mul_rpow hp hr] at hrh
  have hrq := Real.rpow_nonneg hr q
  have hl := (mul_le_mul_of_nonneg_right hbot hrq).trans hrl
  have hh := hrh.trans (mul_le_mul_of_nonneg_right htop hrq)
  exact abs_le.mpr (by constructor <;> nlinarith [mul_nonneg hδ0 hrq])

def negativeTransportTuple (d a n : ℕ) (T : Rd d → Rd a)
    (x : Fin n → Rd d) : Fin n → Rd a := fun i => T (x i)

theorem measurable_negativeTransportTuple (d a n : ℕ)
    (T : Rd d → Rd a) (hT : Measurable T) :
    Measurable (negativeTransportTuple d a n T) := by
  exact measurable_pi_lambda _ (fun i => hT.comp (measurable_pi_apply i))

theorem tupleMeanMeasure_negativeTransportTuple (d a n : ℕ)
    (T : Rd d → Rd a) (hT : Measurable T) (Q : Measure (Fin n → Rd d)) :
    tupleMeanMeasure a n (Q.map (negativeTransportTuple d a n T)) =
      (tupleMeanMeasure d n Q).map T := by
  unfold tupleMeanMeasure
  rw [Measure.map_finset_sum hT.aemeasurable]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Measure.map_map (measurable_pi_apply i)
      (measurable_negativeTransportTuple d a n T hT),
    Measure.map_map hT (measurable_pi_apply i)]
  rfl

theorem negativeTransportTuple_good (d a n : ℕ)
    (Q : Measure (Fin n → Rd d)) (S : Set (Rd d))
    (T : Rd d → Rd a) (hT : Measurable T) (hTi : Set.InjOn T S)
    (hTS : MeasurableSet (T '' S))
    (hQ : ∀ᵐ x ∂Q, Function.Injective x ∧ ∀ i, x i ∈ S) :
    ∀ᵐ y ∂Q.map (negativeTransportTuple d a n T),
      Function.Injective y ∧ ∀ i, y i ∈ T '' S := by
  have hgood : MeasurableSet {y : Fin n → Rd a |
      Function.Injective y ∧ ∀ i, y i ∈ T '' S} :=
    (measurableSet_injective_tuples a n).inter
      (by
        change MeasurableSet {y : Fin n → Rd a | ∀ i, y i ∈ T '' S}
        rw [Set.setOf_forall]
        exact MeasurableSet.iInter (fun i : Fin n => hTS.preimage (measurable_pi_apply i)))
  apply (ae_map_iff (measurable_negativeTransportTuple d a n T hT).aemeasurable
    hgood).mpr
  exact hQ.mono (fun x hx => ⟨fun i j hij => hx.1 (hTi (hx.2 i) (hx.2 j) hij),
    fun i => ⟨x i, hx.2 i, rfl⟩⟩)

def negativeTupleSignedEnergy (d n : ℕ) (q : ℝ)
    (ν : FiniteMeasure (Rd d)) (x : Fin n → Rd d) : ℝ :=
  letI := tupleCounting_isFiniteMeasure d n x
  Riesz.Analysis.signedDiscrepancyEnergy q
    ((tupleCounting d n x).toSignedMeasure - (ν : Measure (Rd d)).toSignedMeasure)

private theorem negative_map_concentrated (d a : ℕ)
    (T : Rd d → Rd a) (hT : Measurable T) (μ : Measure (Rd d))
    (S : Set (Rd d)) (U : Set (Rd a)) (hU : MeasurableSet U)
    (hμ : μ Sᶜ = 0) (hmap : Set.MapsTo T S U) : (μ.map T) Uᶜ = 0 := by
  rw [Measure.map_apply hT hU.compl]
  exact measure_mono_null (fun x hx hxS => hx (hmap hxS)) hμ

private theorem negative_signed_difference_eq_rpow (a : ℕ) (q L : ℝ)
    (hq : 0 < q) (hq2 : q < 2) (μ ν : Measure (Rd a))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real Set.univ = ν.real Set.univ)
    (S : Set (Rd a)) (hS : MeasurableSet S) (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L) :
    Riesz.Analysis.signedDiscrepancyEnergy q (μ.toSignedMeasure - ν.toSignedMeasure) =
      -(1 / q) * Riesz.Analysis.differenceKernelQuadratic
        (fun x y : Rd a => ‖x - y‖ ^ q) μ ν := by
  rw [Riesz.Analysis.signedDiscrepancyEnergy_sub_toSignedMeasure
    q L hq hq2 μ ν hmass S hS hμ hν hdiam]
  simp only [Riesz.Analysis.differenceKernelQuadratic, K_s, neg_neg,
    div_neg, integral_neg, integral_div]
  ring

private theorem negative_rpow_integral_map_prod (d a : ℕ) (q : ℝ)
    (T : Rd d → Rd a) (hT : Measurable T) (μ ν : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ p : Rd a × Rd a, ‖p.1 - p.2‖ ^ q ∂(μ.map T).prod (ν.map T)) =
      ∫ p : Rd d × Rd d, ‖T p.1 - T p.2‖ ^ q ∂μ.prod ν := by
  rw [Measure.map_prod_map μ ν hT hT]
  simpa only [Function.comp_apply, Prod.map_fst, Prod.map_snd] using
    (integral_map (μ := μ.prod ν) (f := fun p : Rd a × Rd a => ‖p.1 - p.2‖ ^ q)
      (hT.prodMap hT).aemeasurable
      (((measurable_fst.sub measurable_snd).norm.pow_const q).aestronglyMeasurable))

private theorem negative_pair_integral_error_le (d n : ℕ) (B : ℝ)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμmass : μ Set.univ = n) (hνmass : ν Set.univ = n)
    (f g : Rd d × Rd d → ℝ) (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) (hfg : ∀ᵐ p ∂μ.prod ν, |f p - g p| ≤ B) :
    |(∫ p, f p ∂μ.prod ν) - ∫ p, g p ∂μ.prod ν| ≤ B * (n : ℝ) ^ 2 := by
  have h := norm_integral_le_of_norm_le_const (f := fun p => f p - g p) (C := B)
    (hfg.mono (fun p hp => by simpa only [Real.norm_eq_abs] using hp))
  rw [integral_sub hf hg] at h
  have hm : (μ.prod ν).real Set.univ = (n : ℝ) ^ 2 := by
    rw [Measure.real, ← Set.univ_prod_univ, Measure.prod_prod, hμmass, hνmass]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, pow_two]
  simpa only [Real.norm_eq_abs, hm] using h

theorem negative_signed_transport_error_le (d a n : ℕ) (q δ L L' : ℝ)
    (hq : 0 < q) (hq2 : q < 2) (hδ0 : 0 ≤ δ) (hδh : δ ≤ 1 / 2)
    (T : Rd d → Rd a) (hT : Measurable T)
    (S : Set (Rd d)) (U : Set (Rd a)) (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hmap : Set.MapsTo T S U)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L)
    (hdiam' : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ L')
    (hmetric : ∀ x ∈ S, ∀ y ∈ S,
      (1 - δ) * ‖x - y‖ ≤ ‖T x - T y‖ ∧ ‖T x - T y‖ ≤ (1 + δ) * ‖x - y‖)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμmass : μ Set.univ = n) (hνmass : ν Set.univ = n)
    (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0) :
    |Riesz.Analysis.signedDiscrepancyEnergy q
        ((μ.map T).toSignedMeasure - (ν.map T).toSignedMeasure) -
      Riesz.Analysis.signedDiscrepancyEnergy q (μ.toSignedMeasure - ν.toSignedMeasure)| ≤
        12 * δ * L ^ q * (n : ℝ) ^ 2 / q := by
  have hμT := negative_map_concentrated d a T hT μ S U hU hμ hmap
  have hνT := negative_map_concentrated d a T hT ν S U hU hν hmap
  have hmass : μ.real Set.univ = ν.real Set.univ :=
    congrArg ENNReal.toReal (hμmass.trans hνmass.symm)
  have hmassT : (μ.map T).real Set.univ = (ν.map T).real Set.univ := by
    simpa only [Measure.real, Measure.map_apply hT MeasurableSet.univ,
      Set.preimage_univ] using hmass
  let f : Rd d × Rd d → ℝ := fun p => ‖T p.1 - T p.2‖ ^ q
  let g : Rd d × Rd d → ℝ := fun p => ‖p.1 - p.2‖ ^ q
  let B : ℝ := 3 * δ * L ^ q
  have hpair (ρ σ : Measure (Rd d)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
      (hρm : ρ Set.univ = n) (hσm : σ Set.univ = n)
      (hρ : ρ Sᶜ = 0) (hσ : σ Sᶜ = 0) :
      |(∫ p, f p ∂ρ.prod σ) - ∫ p, g p ∂ρ.prod σ| ≤ B * (n : ℝ) ^ 2 := by
    have hρT := negative_map_concentrated d a T hT ρ S U hU hρ hmap
    have hσT := negative_map_concentrated d a T hT σ S U hU hσ hmap
    have hg : Integrable g (ρ.prod σ) :=
      Riesz.Analysis.integrable_rpow_distance q L hq.le ρ σ
        (Riesz.Analysis.ae_distance_le_of_concentrated ρ σ S L hρ hσ hdiam)
    have hfT := Riesz.Analysis.integrable_rpow_distance q L' hq.le (ρ.map T) (σ.map T)
      (Riesz.Analysis.ae_distance_le_of_concentrated (ρ.map T) (σ.map T) U L' hρT hσT hdiam')
    rw [Measure.map_prod_map ρ σ hT hT] at hfT
    have hf : Integrable f (ρ.prod σ) := hfT.comp_measurable (hT.prodMap hT)
    apply negative_pair_integral_error_le d n B ρ σ hρm hσm f g hf hg
    filter_upwards [show ∀ᵐ p : Rd d × Rd d ∂ρ.prod σ, p ∈ S ×ˢ S from
      mem_ae_iff.mpr (Measure.measure_prod_compl_eq_zero hρ hσ)] with p hp
    exact (negative_rpow_relative_error_le q δ ‖p.1 - p.2‖ ‖T p.1 - T p.2‖
      hq hq2 hδ0 hδh (norm_nonneg _) (hmetric p.1 hp.1 p.2 hp.2).1
        (hmetric p.1 hp.1 p.2 hp.2).2).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (hdiam p.1 hp.1 p.2 hp.2) hq.le)
        (by positivity : 0 ≤ 3 * δ))
  have h00 := hpair μ μ hμmass hμmass hμ hμ
  have h01 := hpair μ ν hμmass hνmass hμ hν
  have h11 := hpair ν ν hνmass hνmass hν hν
  have hquad : |Riesz.Analysis.differenceKernelQuadratic (fun x y => ‖T x - T y‖ ^ q) μ ν -
      Riesz.Analysis.differenceKernelQuadratic (fun x y => ‖x - y‖ ^ q) μ ν| ≤
        4 * B * (n : ℝ) ^ 2 := by
    rcases abs_le.mp h00 with ⟨h00l, h00u⟩
    rcases abs_le.mp h01 with ⟨h01l, h01u⟩
    rcases abs_le.mp h11 with ⟨h11l, h11u⟩
    change |((∫ p, f p ∂μ.prod μ) - 2 * (∫ p, f p ∂μ.prod ν) + ∫ p, f p ∂ν.prod ν) -
      ((∫ p, g p ∂μ.prod μ) - 2 * (∫ p, g p ∂μ.prod ν) + ∫ p, g p ∂ν.prod ν)| ≤ _
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [negative_signed_difference_eq_rpow a q L' hq hq2 (μ.map T) (ν.map T)
    hmassT U hU hμT hνT hdiam',
    negative_signed_difference_eq_rpow d q L hq hq2 μ ν hmass S hS hμ hν hdiam]
  simp only [Riesz.Analysis.differenceKernelQuadratic,
    negative_rpow_integral_map_prod d a q T hT] at hquad ⊢
  rw [← mul_sub, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hq)]
  calc
    _ ≤ (1 / q) * (4 * B * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hquad (one_div_nonneg.mpr hq.le)
    _ = _ := by dsimp only [B]; ring

theorem negativeTupleTransport_expected_energy_le (d a n : ℕ) (q δ L L' : ℝ)
    (hq : 0 < q) (hq2 : q < 2) (hδ0 : 0 ≤ δ) (hδh : δ ≤ 1 / 2)
    (T : Rd d → Rd a) (hT : Measurable T)
    (S : Set (Rd d)) (U : Set (Rd a)) (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hmap : Set.MapsTo T S U)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L)
    (hdiam' : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ L')
    (hmetric : ∀ x ∈ S, ∀ y ∈ S,
      (1 - δ) * ‖x - y‖ ≤ ‖T x - T y‖ ∧ ‖T x - T y‖ ≤ (1 + δ) * ‖x - y‖)
    (ν : FiniteMeasure (Rd d)) (hνmass : (ν : Measure (Rd d)) Set.univ = n)
    (hν : (ν : Measure (Rd d)) Sᶜ = 0)
    (Q : Measure (Fin n → Rd d)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, ∀ i, x i ∈ S) :
    Integrable (negativeTupleSignedEnergy a n q (ν.map T))
        (Q.map (negativeTransportTuple d a n T)) ∧
      (∫ x, negativeTupleSignedEnergy a n q (ν.map T) x
        ∂Q.map (negativeTransportTuple d a n T)) ≤
      (∫ x, negativeTupleSignedEnergy d n q ν x ∂Q) +
        12 * δ * L ^ q * (n : ℝ) ^ 2 / q := by
  letI : ∀ x : Fin n → Rd d, IsFiniteMeasure (tupleCounting d n x) :=
    fun x => tupleCounting_isFiniteMeasure d n x
  letI : ∀ x : Fin n → Rd a, IsFiniteMeasure (tupleCounting a n x) :=
    fun x => tupleCounting_isFiniteMeasure a n x
  have hmapTuple := measurable_negativeTransportTuple d a n T hT
  letI : IsProbabilityMeasure (Q.map (negativeTransportTuple d a n T)) :=
    Measure.isProbabilityMeasure_map hmapTuple.aemeasurable
  have hQ' : ∀ᵐ x ∂Q.map (negativeTransportTuple d a n T), ∀ i, x i ∈ U := by
    apply (ae_map_iff hmapTuple.aemeasurable
      (show MeasurableSet {y : Fin n → Rd a | ∀ i, y i ∈ U} from by
        rw [Set.setOf_forall]
        exact MeasurableSet.iInter (fun i : Fin n => hU.preimage (measurable_pi_apply i)))).mpr
    exact hQ.mono (fun x hx i => hmap (hx i))
  have hνT := negative_map_concentrated d a T hT ν S U hU hν hmap
  have hνTm : (ν.map T : Measure (Rd a)) Set.univ = n := by
    change ((ν : Measure (Rd d)).map T) Set.univ = n
    rw [Measure.map_apply hT MeasurableSet.univ, Set.preimage_univ, hνmass]
  have hInt : Integrable (negativeTupleSignedEnergy d n q ν) Q := by
    exact finiteDifferenceDiscrepancy_integrable Q d n q L hq hq2
      (tupleCounting d n) (measurable_tupleCounting d n) ν hνmass S hS hν hdiam
      (hQ.mono (fun x hx => ⟨(tupleCounting_compl_eq_zero_iff d n x S hS).mpr hx,
        tupleCounting_univ d n x⟩))
  have hInt' : Integrable (negativeTupleSignedEnergy a n q (ν.map T))
      (Q.map (negativeTransportTuple d a n T)) := by
    exact finiteDifferenceDiscrepancy_integrable _ a n q L' hq hq2
      (tupleCounting a n) (measurable_tupleCounting a n) (ν.map T) hνTm U hU hνT hdiam'
      (hQ'.mono (fun x hx => ⟨(tupleCounting_compl_eq_zero_iff a n x U hU).mpr hx,
        tupleCounting_univ a n x⟩))
  have hcomp := hInt'.comp_measurable hmapTuple
  have hpoint : ∀ᵐ x ∂Q,
      negativeTupleSignedEnergy a n q (ν.map T) (negativeTransportTuple d a n T x) ≤
        negativeTupleSignedEnergy d n q ν x + 12 * δ * L ^ q * (n : ℝ) ^ 2 / q := by
    filter_upwards [hQ] with x hx
    have herr := negative_signed_transport_error_le d a n q δ L L' hq hq2 hδ0 hδh
      T hT S U hS hU hmap hdiam hdiam' hmetric (tupleCounting d n x) ν
      (tupleCounting_univ d n x) hνmass
      ((tupleCounting_compl_eq_zero_iff d n x S hS).mpr hx) hν
    rw [Measure.toSignedMeasure_congr (tupleCounting_map_measurable d a n T hT x)] at herr
    have hu := (le_abs_self _).trans herr
    change negativeTupleSignedEnergy a n q (ν.map T) (negativeTransportTuple d a n T x) -
      negativeTupleSignedEnergy d n q ν x ≤ _ at hu
    linarith
  have hb := integral_mono_ae hcomp (hInt.add (integrable_const
    (12 * δ * L ^ q * (n : ℝ) ^ 2 / q))) hpoint
  simp only [Pi.add_apply] at hb
  rw [integral_add hInt (integrable_const _), integral_const] at hb
  refine ⟨hInt', ?_⟩
  exact (integral_map hmapTuple.aemeasurable hInt'.aestronglyMeasurable).trans_le
    (by simpa only [Function.comp_def, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using hb)

def negativeCubeBackground (d m : ℕ) : FiniteMeasure (Rd d) :=
  ⟨volume.restrict (cube d (m : ℝ)), cube_background_isFiniteMeasure d m⟩

def negativePhysicalCellMap (d m : ℕ) (R : ℝ) (D : Set (Rd d))
    (F : Rd d → Sphere d) (z : GridIndex d) (x : Rd d) : Rd (d + 1) :=
  R • sphericalCellMap d (m : ℝ) R D F z x

theorem measurable_negativePhysicalCellMap (d m : ℕ) (R : ℝ) (D : Set (Rd d))
    (F : Rd d → Sphere d) (hD : MeasurableSet D) (hF : ContinuousOn F D)
    (z : GridIndex d) : Measurable (negativePhysicalCellMap d m R D F z) := by
  exact (measurable_sphericalCellMap d (m : ℝ) R D F hD hF z).const_smul R

theorem norm_negativePhysicalCellMap (d m : ℕ) (R : ℝ) (hR : 0 < R)
    (D : Set (Rd d)) (F : Rd d → Sphere d) (z : GridIndex d) (x : Rd d) :
    ‖negativePhysicalCellMap d m R D F z x‖ = R := by
  simp only [negativePhysicalCellMap, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  change R * ‖(sphericalCellChartExtension d D F (sphericalCellAffine d (m : ℝ) R z x)).val‖ = R
  rw [(sphericalCellChartExtension d D F (sphericalCellAffine d (m : ℝ) R z x)).property, mul_one]

private theorem negative_cube_diameter (d : ℕ) (L : ℝ) (hL : 0 < L)
    (x : Rd d) (hx : x ∈ cube d L) (y : Rd d) (hy : y ∈ cube d L) :
    ‖x - y‖ ≤ Real.sqrt d * L := by
  have hc (i : Fin d) : |x i - y i| ≤ L :=
    abs_le.mpr ⟨by linarith [(hx i).1, (hy i).2], by linarith [(hy i).1, (hx i).2]⟩
  have hsquare : ‖x - y‖ ^ 2 ≤ (d : ℝ) * L ^ 2 := by
    calc
      _ = ∑ i : Fin d, (x i - y i) ^ 2 := EuclideanSpace.real_norm_sq_eq (x - y)
      _ ≤ ∑ _i : Fin d, L ^ 2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hL.le).2 (hc i))
      _ = _ := by simp
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hL.le)).mp
    (by simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] using hsquare)

theorem negativePhysicalCellTuple_mean (d m N : ℕ) (R : ℝ) (hR : 0 < R)
    (hRN : R ^ d * omega d = N) (D : Set (Rd d)) (F : Rd d → Sphere d)
    (hD : MeasurableSet D) (hF : ContinuousOn F D) (hFi : Set.InjOn F D)
    (harea : ∀ E : Set (Rd d), MeasurableSet E → E ⊆ D →
      sphericalMeasure d (F '' E) =
        (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E)
    (z : GridIndex d) (hcell : latticeCell d ((m : ℝ) / R) 0 z ⊆ D)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    tupleMeanMeasure (d + 1) (m ^ d)
      (Q.map (negativeTransportTuple d (d + 1) (m ^ d) (negativePhysicalCellMap d m R D F z))) =
      (ENNReal.ofReal (N : ℝ) •
        (sphericalMeasure d).restrict (F '' latticeCell d ((m : ℝ) / R) 0 z)).map
          (fun p : Sphere d => R • p.val) := by
  have hT := measurable_negativePhysicalCellMap d m R D F hD hF z
  rw [tupleMeanMeasure_negativeTransportTuple d (d + 1) (m ^ d) _ hT,
    tupleBalanced_tupleMeanMeasure d m Q hQ]
  change (volume.restrict (cube d (m : ℝ))).map
    ((fun p : Rd (d + 1) => R • p) ∘ sphericalCellMap d (m : ℝ) R D F z) = _
  rw [← Measure.map_map (measurable_const_smul R)
    (measurable_sphericalCellMap d (m : ℝ) R D F hD hF z),
    map_cube_volume_sphericalCellMap d (m : ℝ) R hR z D F hD hF hFi harea hcell, hRN,
    Measure.map_map (measurable_const_smul R) continuous_subtype_val.measurable]
  rfl

theorem negativePhysicalCellTuple_probability (d m : ℕ) (R : ℝ)
    (D : Set (Rd d)) (F : Rd d → Sphere d) (hD : MeasurableSet D)
    (hF : ContinuousOn F D) (z : GridIndex d)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    IsProbabilityMeasure (Q.map (negativeTransportTuple d (d + 1) (m ^ d)
      (negativePhysicalCellMap d m R D F z))) := by
  letI : IsProbabilityMeasure Q := hQ.1
  exact Measure.isProbabilityMeasure_map
    (measurable_negativeTransportTuple d (d + 1) (m ^ d) _
      (measurable_negativePhysicalCellMap d m R D F hD hF z)).aemeasurable

theorem negativePhysicalCellTuple_good (d m : ℕ) (R : ℝ) (hR : 0 < R)
    (D : Set (Rd d)) (F : Rd d → Sphere d)
    (hD : MeasurableSet D) (hF : ContinuousOn F D) (hFi : Set.InjOn F D)
    (z : GridIndex d) (hcell : latticeCell d ((m : ℝ) / R) 0 z ⊆ D)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    ∀ᵐ x ∂Q.map (negativeTransportTuple d (d + 1) (m ^ d) (negativePhysicalCellMap d m R D F z)),
      Function.Injective x ∧ ∀ i, x i ∈ negativePhysicalCellMap d m R D F z '' cube d (m : ℝ) := by
  have hTi : Set.InjOn (negativePhysicalCellMap d m R D F z) (cube d (m : ℝ)) := by
    intro x hx y hy hxy
    apply injOn_sphericalCellMap d (m : ℝ) R hR z D F hFi hcell hx hy
    have h := congrArg (fun v : Rd (d + 1) => R⁻¹ • v) hxy
    simpa only [negativePhysicalCellMap, smul_smul, inv_mul_cancel₀ hR.ne', one_smul] using h
  have hTc : ContinuousOn (negativePhysicalCellMap d m R D F z) (cube d (m : ℝ)) :=
    (continuousOn_sphericalCellMap d (m : ℝ) R hR z D F hF hcell).const_smul R
  exact negativeTransportTuple_good d (d + 1) (m ^ d) Q _ _
    (measurable_negativePhysicalCellMap d m R D F hD hF z) hTi
    ((measurableSet_cube d (m : ℝ)).image_of_continuousOn_injOn hTc hTi) hQ.2.1

theorem negativePhysicalCellTuple_expected_energy_le (d m : ℕ) (q δ R : ℝ)
    (hm : 0 < m) (hq : 0 < q) (hq2 : q < 2)
    (hδ0 : 0 ≤ δ) (hδh : δ ≤ 1 / 2) (hR : 0 < R)
    (D : Set (Rd d)) (F : Rd d → Sphere d) (hD : MeasurableSet D)
    (hF : ContinuousOn F D) (z : GridIndex d)
    (hcell : latticeCell d ((m : ℝ) / R) 0 z ⊆ D)
    (hmetric : ∀ x ∈ D, ∀ y ∈ D,
      (1 - δ) * ‖x - y‖ ≤ chord d (F x) (F y) ∧
        chord d (F x) (F y) ≤ (1 + δ) * ‖x - y‖)
    (Q : Measure (Fin (m ^ d) → Rd d)) (hQ : TupleBalancedAdmissible d m Q) :
    let T := negativePhysicalCellMap d m R D F z
    let ν := (negativeCubeBackground d m).map T
    let QT := Q.map (negativeTransportTuple d (d + 1) (m ^ d) T)
    Integrable (negativeTupleSignedEnergy (d + 1) (m ^ d) q ν) QT ∧
      (∫ x, negativeTupleSignedEnergy (d + 1) (m ^ d) q ν x ∂QT) ≤
        (∫ x, Riesz.Analysis.signedDiscrepancyEnergy q (tupleDiscrepancy d m x) ∂Q) +
          12 * δ * (Real.sqrt d * (m : ℝ)) ^ q * ((m ^ d : ℕ) : ℝ) ^ 2 / q := by
  let T := negativePhysicalCellMap d m R D F z
  letI : IsProbabilityMeasure Q := hQ.1
  have hTm := measurable_negativePhysicalCellMap d m R D F hD hF z
  have hmap : Set.MapsTo T (cube d (m : ℝ)) (Metric.closedBall 0 R) := by
    intro x _hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (norm_negativePhysicalCellMap d m R hR D F z x).le
  have hdiam' : ∀ x ∈ Metric.closedBall (0 : Rd (d + 1)) R,
      ∀ y ∈ Metric.closedBall (0 : Rd (d + 1)) R, ‖x - y‖ ≤ 2 * R := by
    intro x hx y hy
    have hx' : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hy' : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    exact (norm_sub_le x y).trans (by linarith)
  have hmet : ∀ x ∈ cube d (m : ℝ), ∀ y ∈ cube d (m : ℝ),
      (1 - δ) * ‖x - y‖ ≤ ‖T x - T y‖ ∧ ‖T x - T y‖ ≤ (1 + δ) * ‖x - y‖ := by
    intro x hx y hy
    simpa only [T, negativePhysicalCellMap, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hR] using
      sphericalCellMap_relative_distance d (m : ℝ) R δ hR z D F hcell hmetric y hy x hx
  have hν : (negativeCubeBackground d m : Measure (Rd d)) (cube d (m : ℝ))ᶜ = 0 := by
    change (volume.restrict (cube d (m : ℝ))) (cube d (m : ℝ))ᶜ = 0
    simp only [Measure.restrict_apply (measurableSet_cube d (m : ℝ)).compl,
      Set.compl_inter_self, measure_empty]
  have h := negativeTupleTransport_expected_energy_le d (d + 1) (m ^ d)
    q δ (Real.sqrt d * (m : ℝ)) (2 * R) hq hq2 hδ0 hδh T hTm
    (cube d (m : ℝ)) (Metric.closedBall 0 R) (measurableSet_cube d (m : ℝ))
    Metric.isClosed_closedBall.measurableSet hmap
    (negative_cube_diameter d (m : ℝ) (Nat.cast_pos.mpr hm)) hdiam' hmet
    (negativeCubeBackground d m) (cube_background_mass d m) hν Q
    (hQ.2.1.mono (fun x hx => hx.2))
  exact h

end Riesz.Negative
