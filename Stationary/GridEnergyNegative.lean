import Riesz.Stationary.GridScaleGaussian
import Riesz.Stationary.GaussianCorrection

/-! The negative-exponent energy of the concrete stationary grid law equals
the expected balanced finite-cell discrepancy density. -/

noncomputable section

open MeasureTheory RieszShowcase Filter
open scoped ENNReal Classical Topology

namespace Riesz.Stationary

theorem gaussianRemainder_add_correction (d : ℕ) (P : ConfigurationLaw d) (t : ℝ)
    (hQ : Q d P t ≠ ∞) (hcov : 0 ≤ (Q d P t).toReal + 1 - B d t) :
    ENNReal.ofReal (gaussianCorrection d t) + gaussianRemainder d P t =
      ENNReal.ofReal ((Q d P t).toReal + 1 - B d t) := by
  have hrem : gaussianRemainder d P t =
      ENNReal.ofReal ((Q d P t).toReal - max (B d t - 1) 0) := by
    unfold gaussianRemainder
    conv_lhs => rw [← ENNReal.ofReal_toReal hQ]
    exact (ENNReal.ofReal_sub _ (le_max_right (B d t - 1) 0)).symm
  have hnonneg : 0 ≤ (Q d P t).toReal - max (B d t - 1) 0 :=
    sub_nonneg.mpr (max_le (by linarith) ENNReal.toReal_nonneg)
  rw [hrem, gaussianCorrection, ← ENNReal.ofReal_add (le_max_right (1 - B d t) 0) hnonneg]
  congr 1
  grind

theorem Q_randomShiftGridLaw_remainder_correction_lintegral (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (q : ℝ) (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-q / 2 - 1)) *
      ENNReal.ofReal (gaussianCorrection d t)) +
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-q / 2 - 1)) *
        gaussianRemainder d (randomShiftGridLaw d m Qcell) t) =
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-q / 2 - 1)) *
        ENNReal.ofReal ((Q d (randomShiftGridLaw d m Qcell) t).toReal + 1 - B d t) := by
  have hmeas : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (-q / 2 - 1)) *
      ENNReal.ofReal (gaussianCorrection d t)) :=
    (measurable_id.pow_const _).ennreal_ofReal.mul (gaussianCorrection_measurable d).ennreal_ofReal
  rw [← lintegral_add_left hmeas]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [← mul_add, gaussianRemainder_add_correction d _ t
    (Q_randomShiftGridLaw_ne_top d m hm Qcell hQ t ht)
    (Q_randomShiftGridLaw_covariance_nonneg d m hd hm Qcell hQ t ht)]

/-- Exact energy identity, including the diagonal, Gamma coefficient and `c0` shift. -/
theorem W_randomShiftGridLaw_neg_eq (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) :
    W d (-q) (randomShiftGridLaw d m Qcell) =
      (((m : ℝ) ^ d)⁻¹ * ∫ x, Riesz.Analysis.signedDiscrepancyEnergy q
        (Riesz.Negative.tupleDiscrepancy d m x) ∂Qcell : ℝ) := by
  unfold W
  have hdpos : 0 < d := Nat.lt_of_lt_of_le (by decide) hd
  have hc0 : 0 ≤ c0 d (-q) := (c0_pos_of_neg d (-q) hd (neg_lt_neg hq_two)
    ((neg_lt_zero.mpr hq).trans_le (Nat.cast_nonneg d)) (neg_lt_zero.mpr hq)).le
  have hc0coe : (c0 d (-q) : EReal) = (ENNReal.ofReal (c0 d (-q)) : EReal) := by
    simp only [EReal.coe_ennreal_ofReal, max_eq_left hc0]
  rw [hc0coe, ← gamma_correction_lintegral_eq_c0 d (-q) (neg_lt_neg hq_two) (neg_lt_zero.mpr hq),
    ← EReal.coe_ennreal_add, ← mul_add,
    Q_randomShiftGridLaw_remainder_correction_lintegral d m hdpos hm q Qcell hQ]
  rw [Q_randomShiftGridLaw_weighted_covariance_lintegral d m hdpos hm q hq hq_two Qcell hQ,
    ← ENNReal.ofReal_mul (Riesz.Analysis.gamma_s_pos (-q) (neg_lt_neg hq_two)).le,
    Q_randomShiftGridLaw_integrated_signedGaussian d m hdpos hm q hq hq_two Qcell hQ,
    EReal.coe_ennreal_ofReal]
  rw [max_eq_left (mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg m) d))
    (integral_nonneg_of_ae (hQ.2.1.mono (fun x hx =>
      (Riesz.Negative.tuple_signedDiscrepancyEnergy_gaussian d m q hdpos hq hq_two x hx.2).2))))]

theorem e_neg_le_expected_grid_energy_density (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2)
    (Qcell : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Qcell) :
    e d (-q) ≤ ((m : ℝ) ^ d)⁻¹ * ∫ x, Riesz.Analysis.signedDiscrepancyEnergy q
      (Riesz.Negative.tupleDiscrepancy d m x) ∂Qcell := by
  apply EReal.coe_le_coe_iff.mp
  rw [← infimumFinite_neg d (Nat.lt_of_lt_of_le (by decide) hd) q hq hq_two,
    ← W_randomShiftGridLaw_neg_eq d m hd hm q hq hq_two Qcell hQ]
  exact sInf_le ⟨randomShiftGridLaw d m Qcell,
    randomShiftGridLaw_admissible d m hm Qcell hQ, rfl⟩

theorem e_neg_le_balanced_density (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2) :
    e d (-q) ≤ b d q m / (m : ℝ) ^ d := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hvolume : 0 < (m : ℝ) ^ d := pow_pos (Nat.cast_pos.mpr hm) d
  obtain ⟨Qcell, hQcell, _, _, henergy⟩ := Riesz.Negative.exists_near_optimal_signed_tuple_law
    d m q (ε * (m : ℝ) ^ d) (Nat.lt_of_lt_of_le (by decide) hd) hm hq hq_two (mul_pos hε hvolume)
  have hstationary := e_neg_le_expected_grid_energy_density d m hd hm q hq hq_two Qcell hQcell
  have hscaled := mul_lt_mul_of_pos_left henergy (inv_pos.mpr hvolume)
  have hfactor : ((m : ℝ) ^ d)⁻¹ * (b d q m + ε * (m : ℝ) ^ d) =
      b d q m / (m : ℝ) ^ d + ε := by field_simp
  exact hstationary.trans (hscaled.trans_eq hfactor).le

/-- Both assertions of the paper's cube-limit lemma for the exact showcase energies. -/
theorem balanced_cube_density_limit_and_stationary_bound (d : ℕ) (hd : 2 ≤ d)
    (q : ℝ) (hq : 0 < q) (hq_two : q < 2) :
    Tendsto (fun m : ℕ => b d q m / (m : ℝ) ^ d) atTop
      (nhds (sInf {r : ℝ | ∃ m : ℕ, 1 ≤ m ∧ r = b d q m / (m : ℝ) ^ d})) ∧
      e d (-q) ≤ sInf {r : ℝ | ∃ m : ℕ, 1 ≤ m ∧ r = b d q m / (m : ℝ) ^ d} := by
  refine ⟨Riesz.Negative.balanced_cube_density_limit d q
    (Nat.lt_of_lt_of_le (by decide) hd) hq hq_two,
    le_csInf (Riesz.Negative.balancedDensityValues_nonempty d q) ?_⟩
  rintro r ⟨m, hm, rfl⟩
  exact e_neg_le_balanced_density d m hd (Nat.zero_lt_of_lt hm) q hq hq_two

end Riesz.Stationary
