import Riesz.Stationary.GridScaleGaussian
import Riesz.Stationary.GaussianCorrection

/-! The positive-exponent finite competitor, proved directly from the
Gaussian profile of the existing randomly shifted one-point-per-cell law. -/

noncomputable section

open MeasureTheory RieszShowcase Filter
open scoped ENNReal Classical Topology

namespace Riesz.Stationary

/-- The integrable reference subtracted from the positive Gaussian energy. -/
def weightedPositiveReference (d : ℕ) (s t : ℝ) : ℝ :=
  t ^ (s / 2 - 1) * min 1 (B d t)

theorem weightedPositiveReference_tail (d : ℕ) (s t : ℝ) (ht : Real.pi < t) :
    weightedPositiveReference d s t =
      Real.pi ^ ((d : ℝ) / 2) * t ^ ((s - (d : ℝ)) / 2 - 1) := by
  rw [weightedPositiveReference, min_eq_right (B_le_one_of_pi_le d t ht.le), B,
    Real.div_rpow Real.pi_pos.le (Real.pi_pos.trans ht).le,
    div_eq_mul_inv (Real.pi ^ ((d : ℝ) / 2)) (t ^ ((d : ℝ) / 2)),
    ← Real.rpow_neg (Real.pi_pos.trans ht).le]
  rw [mul_left_comm, ← Real.rpow_add (Real.pi_pos.trans ht)]
  rw [show s / 2 - 1 + -((d : ℝ) / 2) = (s - (d : ℝ)) / 2 - 1 by ring]

theorem weightedPositiveReference_head (d : ℕ) (s t : ℝ)
    (ht : 0 < t) (hpi : t ≤ Real.pi) :
    weightedPositiveReference d s t = t ^ (s / 2 - 1) := by
  simp only [weightedPositiveReference, min_eq_left (one_le_B_of_le_pi d t ht hpi), mul_one]

theorem weightedPositiveReference_indicator (d : ℕ) (s : ℝ) :
    weightedPositiveReference d s =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t => (Set.Ioc (0 : ℝ) Real.pi).indicator (fun t => t ^ (s / 2 - 1)) t +
        (Set.Ioi Real.pi).indicator (fun t =>
          Real.pi ^ ((d : ℝ) / 2) * t ^ ((s - (d : ℝ)) / 2 - 1)) t) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rcases le_or_gt t Real.pi with hpi | hpi
  · simp only [weightedPositiveReference_head d s t ht hpi,
      Set.indicator_of_mem (show t ∈ Set.Ioc (0 : ℝ) Real.pi from ⟨ht, hpi⟩),
      Set.indicator_of_notMem (show t ∉ Set.Ioi Real.pi from not_lt.mpr hpi), add_zero]
  · simp only [weightedPositiveReference_tail d s t hpi,
      Set.indicator_of_notMem (show t ∉ Set.Ioc (0 : ℝ) Real.pi from fun h =>
        (not_le.mpr hpi) h.2),
      Set.indicator_of_mem (show t ∈ Set.Ioi Real.pi from hpi), zero_add]

theorem weightedPositiveReference_integrable (d : ℕ) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) :
    IntegrableOn (weightedPositiveReference d s) (Set.Ioi 0) := by
  have hhead : IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1))
      (Set.Ioc (0 : ℝ) Real.pi) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff Real.pi_pos).2 (by linarith)
  have htail : IntegrableOn (fun t : ℝ =>
      Real.pi ^ ((d : ℝ) / 2) * t ^ ((s - (d : ℝ)) / 2 - 1)) (Set.Ioi Real.pi) :=
    (integrableOn_Ioi_rpow_of_lt
      (by linarith : (s - (d : ℝ)) / 2 - 1 < -1) Real.pi_pos).const_mul _
  exact (((hhead.integrable_indicator measurableSet_Ioc).add
    (htail.integrable_indicator measurableSet_Ioi)).mono_measure
      Measure.restrict_le_self).congr (weightedPositiveReference_indicator d s).symm

theorem integral_weightedPositiveReference_split (d : ℕ) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) :
    (∫ t : ℝ in Set.Ioi 0, weightedPositiveReference d s t) =
      (∫ t : ℝ in Set.Ioc 0 Real.pi, t ^ (s / 2 - 1)) +
        Real.pi ^ ((d : ℝ) / 2) *
          ∫ t : ℝ in Set.Ioi Real.pi, t ^ ((s - (d : ℝ)) / 2 - 1) := by
  rw [integral_congr_ae (weightedPositiveReference_indicator d s)]
  have hhead : IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1))
      (Set.Ioc (0 : ℝ) Real.pi) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).mpr
      ((intervalIntegral.integrableOn_Ioo_rpow_iff Real.pi_pos).2 (by linarith))
  have htail : IntegrableOn (fun t : ℝ =>
      Real.pi ^ ((d : ℝ) / 2) * t ^ ((s - (d : ℝ)) / 2 - 1)) (Set.Ioi Real.pi) :=
    (integrableOn_Ioi_rpow_of_lt
      (by linarith : (s - (d : ℝ)) / 2 - 1 < -1) Real.pi_pos).const_mul _
  rw [integral_add
    ((hhead.integrable_indicator measurableSet_Ioc).mono_measure Measure.restrict_le_self)
    ((htail.integrable_indicator measurableSet_Ioi).mono_measure Measure.restrict_le_self),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi]
  simp only [Measure.restrict_restrict measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioc_inter_Ioi, max_self,
    Set.Ioi_inter_Ioi, max_eq_left Real.pi_pos.le, integral_const_mul]

theorem integral_weightedPositiveReference (d : ℕ) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) :
    (∫ t : ℝ in Set.Ioi 0, weightedPositiveReference d s t) =
      (2 * (d : ℝ) * Real.pi ^ (s / 2)) / (s * ((d : ℝ) - s)) := by
  rw [integral_weightedPositiveReference_split d s hs hsd,
    ← intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_rpow (Or.inl (by linarith : -1 < s / 2 - 1)),
    integral_Ioi_rpow_of_lt
      (by linarith : (s - (d : ℝ)) / 2 - 1 < -1) Real.pi_pos]
  simp only [sub_add_cancel, Real.zero_rpow (by linarith : s / 2 ≠ 0), sub_zero]
  rw [← mul_div_assoc, mul_neg, ← Real.rpow_add Real.pi_pos,
    show (d : ℝ) / 2 + (s - (d : ℝ)) / 2 = s / 2 by ring]
  field_simp [hs.ne', (sub_pos.mpr hsd).ne', (sub_neg.mpr hsd).ne]
  ring

theorem gamma_positive_reference_eq_neg_c0 (d : ℕ) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) :
    gamma_s s * (∫ t : ℝ in Set.Ioi 0, weightedPositiveReference d s t) =
      -c0 d s := by
  rw [integral_weightedPositiveReference d s hs hsd, gamma_s, c0]
  field_simp

/-- The within-cell Gaussian background omitted by a one-point-per-cell grid. -/
def unitCellGaussianBackground (d : ℕ) (t : ℝ) : ℝ :=
  ∫ p : Rd d × Rd d, Real.exp (-t * ‖p.1 - p.2‖ ^ 2)
    ∂(volume.restrict (cube d 1)).prod (volume.restrict (cube d 1))

theorem tupleOffSiteGaussian_one (d : ℕ) (t : ℝ) (x : Fin 1 → Rd d) :
    tupleOffSiteGaussian d 1 t x = 0 := by
  simp [tupleOffSiteGaussian, tuplePairSum, offSiteGaussianKernel]

theorem Q_unitGrid_gaussian_balance (d : ℕ)
    (Qcell : Measure (Fin (1 ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d 1 Qcell)
    (t : ℝ) (ht : 0 < t) :
    (Q d (randomShiftGridLaw d 1 Qcell) t).toReal + unitCellGaussianBackground d t =
      B d t := by
  have h := congrArg ENNReal.toReal
    (Q_randomShiftGridLaw_gaussian_balance d 1 Nat.zero_lt_one Qcell hQ t ht)
  have hzero : ∀ x : Fin (1 ^ d) → Rd d, tupleOffSiteGaussian d (1 ^ d) t x = 0 := by
    exact (Nat.one_pow d).symm ▸ tupleOffSiteGaussian_one d t
  simp only [Nat.cast_one, one_pow, inv_one, one_mul, hzero,
    lintegral_zero, add_zero] at h
  have hfinite : (∫⁻ p, gaussianPairKernel d t p
      ∂(volume.restrict (cube d 1)).prod (volume.restrict (cube d 1))) ≠ ∞ := by
    simpa only [Nat.cast_one] using cubeGaussian_lintegral_ne_top d 1 t ht.le
  rw [ENNReal.toReal_add
      (Q_randomShiftGridLaw_ne_top d 1 Nat.zero_lt_one Qcell hQ t ht) hfinite,
    gaussianPair_lintegral_toReal,
    ENNReal.toReal_ofReal (show 0 ≤ B d t from
      (Real.rpow_pos_of_pos (div_pos Real.pi_pos ht) ((d : ℝ) / 2)).le)] at h
  exact h

theorem unitCellVolume_probability (d : ℕ) :
    IsProbabilityMeasure (volume.restrict (cube d 1)) := by
  constructor
  simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Riesz.Negative.volume_cube, ENNReal.ofReal_one, one_pow]

theorem unitCellGaussianBackground_bounds (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 < unitCellGaussianBackground d t ∧ unitCellGaussianBackground d t ≤ 1 := by
  letI := unitCellVolume_probability d
  refine ⟨integral_exp_pos (Riesz.Analysis.integrable_gaussian_prod_measure t ht _ _), ?_⟩
  simpa only [unitCellGaussianBackground, integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul] using integral_mono
      (Riesz.Analysis.integrable_gaussian_prod_measure t ht
        (volume.restrict (cube d 1)) (volume.restrict (cube d 1))) (integrable_const (1 : ℝ))
      (fun p => Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg ‖p.1 - p.2‖)))

theorem unitCellGaussianBackground_le_reference (d : ℕ)
    (Qcell : Measure (Fin (1 ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d 1 Qcell)
    (t : ℝ) (ht : 0 < t) :
    unitCellGaussianBackground d t ≤ min 1 (B d t) := by
  exact le_min (unitCellGaussianBackground_bounds d t ht.le).2
    ((le_add_of_nonneg_left (show 0 ≤ (Q d (randomShiftGridLaw d 1 Qcell) t).toReal from
      ENNReal.toReal_nonneg)).trans_eq (Q_unitGrid_gaussian_balance d Qcell hQ t ht))

def weightedUnitCellGaussianBackground (d : ℕ) (s t : ℝ) : ℝ :=
  t ^ (s / 2 - 1) * unitCellGaussianBackground d t

theorem weightedUnitCellGaussianBackground_stronglyMeasurable (d : ℕ) (s : ℝ) :
    StronglyMeasurable (weightedUnitCellGaussianBackground d s) := by
  letI := unitCellVolume_probability d
  exact (measurable_id.pow_const (s / 2 - 1)).stronglyMeasurable.mul
    (gaussian_pair_scale_stronglyMeasurable d
      (volume.restrict (cube d 1)) (volume.restrict (cube d 1)))

theorem weightedUnitCellGaussianBackground_pos (d : ℕ) (s t : ℝ) (ht : 0 < t) :
    0 < weightedUnitCellGaussianBackground d s t := by
  exact mul_pos (Real.rpow_pos_of_pos ht _) (unitCellGaussianBackground_bounds d t ht.le).1

theorem weightedUnitCellGaussianBackground_integrable (d : ℕ) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ))
    (Qcell : Measure (Fin (1 ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d 1 Qcell) :
    IntegrableOn (weightedUnitCellGaussianBackground d s) (Set.Ioi 0) := by
  refine (weightedPositiveReference_integrable d s hs hsd).mono_nonneg
    (weightedUnitCellGaussianBackground_stronglyMeasurable d s).aestronglyMeasurable ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
      (weightedUnitCellGaussianBackground_pos d s t ht).le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
      mul_le_mul_of_nonneg_left (unitCellGaussianBackground_le_reference d Qcell hQ t ht)
        (Real.rpow_nonneg ht.le _)

theorem integral_weightedUnitCellGaussianBackground_pos (d : ℕ) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ))
    (Qcell : Measure (Fin (1 ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d 1 Qcell) :
    0 < ∫ t : ℝ in Set.Ioi 0, weightedUnitCellGaussianBackground d s t := by
  have hpos : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      0 < weightedUnitCellGaussianBackground d s t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
      weightedUnitCellGaussianBackground_pos d s t ht
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono (fun _ h => h.le))
    (weightedUnitCellGaussianBackground_integrable d s hs hsd Qcell hQ)]
  have hsupp : Function.support (weightedUnitCellGaussianBackground d s)
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] Set.univ :=
    hpos.mono (fun t ht => propext (iff_of_true ht.ne' (Set.mem_univ t)))
  simp [measure_congr hsupp]

theorem gaussianRemainder_unitGrid (d : ℕ)
    (Qcell : Measure (Fin (1 ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d 1 Qcell)
    (t : ℝ) (ht : 0 < t) :
    gaussianRemainder d (randomShiftGridLaw d 1 Qcell) t =
      ENNReal.ofReal (min 1 (B d t) - unitCellGaussianBackground d t) := by
  rw [gaussianRemainder, ← ENNReal.ofReal_toReal
    (Q_randomShiftGridLaw_ne_top d 1 Nat.zero_lt_one Qcell hQ t ht)]
  rw [← ENNReal.ofReal_sub _ (le_max_right (B d t - 1) 0)]
  congr 1
  have hbalance := Q_unitGrid_gaussian_balance d Qcell hQ t ht
  grind

theorem gaussianRemainder_unitGrid_lintegral (d : ℕ) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ))
    (Qcell : Measure (Fin (1 ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d 1 Qcell) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (s / 2 - 1)) *
      gaussianRemainder d (randomShiftGridLaw d 1 Qcell) t) =
        ENNReal.ofReal ((∫ t : ℝ in Set.Ioi 0, weightedPositiveReference d s t) -
          ∫ t : ℝ in Set.Ioi 0, weightedUnitCellGaussianBackground d s t) := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t => weightedPositiveReference d s t - weightedUnitCellGaussianBackground d s t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
      sub_nonneg.mpr (mul_le_mul_of_nonneg_left
        (unitCellGaussianBackground_le_reference d Qcell hQ t ht) (Real.rpow_nonneg ht.le _))
  rw [← integral_sub (weightedPositiveReference_integrable d s hs hsd)
    (weightedUnitCellGaussianBackground_integrable d s hs hsd Qcell hQ),
    ofReal_integral_eq_lintegral_ofReal
      (f := fun t : ℝ => weightedPositiveReference d s t - weightedUnitCellGaussianBackground d s t)
      ((weightedPositiveReference_integrable d s hs hsd).sub
        (weightedUnitCellGaussianBackground_integrable d s hs hsd Qcell hQ)) hnonneg]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [gaussianRemainder_unitGrid d Qcell hQ t ht,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), mul_sub]
  rfl

theorem W_unitGrid_pos_eq (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (Qcell : Measure (Fin (1 ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d 1 Qcell) :
    W d s (randomShiftGridLaw d 1 Qcell) =
      ((-gamma_s s * ∫ t : ℝ in Set.Ioi 0, weightedUnitCellGaussianBackground d s t : ℝ) : EReal) := by
  rw [W, gaussianRemainder_unitGrid_lintegral d s hs hsd Qcell hQ,
    ← ENNReal.ofReal_mul (Riesz.Analysis.gamma_s_pos s (by linarith)).le,
    EReal.coe_ennreal_ofReal]
  have hdiff : 0 ≤ (∫ t : ℝ in Set.Ioi 0, weightedPositiveReference d s t) -
      ∫ t : ℝ in Set.Ioi 0, weightedUnitCellGaussianBackground d s t :=
    sub_nonneg.mpr (integral_mono_ae
      (weightedUnitCellGaussianBackground_integrable d s hs hsd Qcell hQ)
      (weightedPositiveReference_integrable d s hs hsd) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
          mul_le_mul_of_nonneg_left (unitCellGaussianBackground_le_reference d Qcell hQ t ht)
            (Real.rpow_nonneg ht.le _)))
  rw [max_eq_left (mul_nonneg (Riesz.Analysis.gamma_s_pos s (by linarith)).le hdiff),
    ← EReal.coe_add]
  congr 1
  rw [mul_sub, gamma_positive_reference_eq_neg_c0 d s hs hsd]
  ring

theorem W_unitGrid_pos_neg (d : ℕ) (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ))
    (Qcell : Measure (Fin (1 ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d 1 Qcell) :
    W d s (randomShiftGridLaw d 1 Qcell) < 0 := by
  rw [W_unitGrid_pos_eq d s hs hsd Qcell hQ]
  exact EReal.coe_lt_coe_iff.mpr (mul_neg_of_neg_of_pos
    (neg_neg_of_pos (Riesz.Analysis.gamma_s_pos s (by linarith)))
    (integral_weightedUnitCellGaussianBackground_pos d s hs hsd Qcell hQ))

/-- A concrete strictly negative competitor for every positive admissible exponent. -/
theorem exists_admissible_negative_energy_pos (d : ℕ) (hd : 0 < d)
    (s : ℝ) (hs : 0 < s) (hsd : s < (d : ℝ)) :
    ∃ P : ConfigurationLaw d, Admissible d P ∧ W d s P < 0 := by
  obtain ⟨Pcell, hPcell⟩ := Riesz.Negative.exists_balanced_law d 1 hd Nat.zero_lt_one
  obtain ⟨Qcell, hQcell, _, hgrid⟩ := exists_admissible_grid_law_of_balanced
    d 1 Nat.zero_lt_one Pcell hPcell
  exact ⟨_, hgrid, W_unitGrid_pos_neg d s hs hsd Qcell hQcell⟩

/-- Finiteness and both constant signs in the main theorem's positive branch. -/
theorem positive_constant_finiteness_and_sign (d : ℕ) (hd : 0 < d) (s : ℝ)
    (hs : 0 < s) (hsd : s < (d : ℝ)) :
    eExtended d s = (e d s : EReal) ∧ e d s < 0 ∧ C d s < 0 := by
  obtain ⟨P, hP, hW⟩ := exists_admissible_negative_energy_pos d hd s hs hsd
  have h := infimumFinite_and_e_neg_of_competitor d s P hP hW
  exact ⟨h.1, h.2, mul_neg_of_pos_of_neg hs h.2⟩

/-- All finiteness and sign clauses for the exact constants in the showcase. -/
theorem constant_finiteness_and_sign (d : ℕ) (s : ℝ) (hd : 2 ≤ d)
    (hs_lower : -2 < s) (hs_upper : s < (d : ℝ)) (hs_ne : s ≠ 0) :
    eExtended d s = (e d s : EReal) ∧
      (0 < s → e d s < 0) ∧ (s < 0 → 0 < e d s) ∧ C d s < 0 := by
  rcases lt_or_gt_of_ne hs_ne with hs_neg | hs_pos
  · have h := negative_constant_finiteness_and_sign d hd s hs_lower hs_neg
    exact ⟨h.1, fun hp => (not_lt_of_ge hs_neg.le hp).elim, fun _ => h.2.1, h.2.2⟩
  · have h := positive_constant_finiteness_and_sign d
      (Nat.lt_of_lt_of_le (by decide) hd) s hs_pos hs_upper
    exact ⟨h.1, fun _ => h.2.1, fun hn => (not_lt_of_ge hs_pos.le hn).elim, h.2.2⟩

end Riesz.Stationary
