import Riesz.Definitions
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Smooth windows with square mass arbitrarily close to the unit cube volume

The support stays inside the exact half-open Showcase cube. These windows
retain the sharp constant when the full physical window limit is used.
-/

noncomputable section

open MeasureTheory Filter RieszShowcase
open scoped ENNReal Topology CompactlySupported ContDiff Manifold

namespace Riesz.Stationary

theorem exists_nearIndicator_smooth_window_of_open_volume_one
    (d : ℕ) (U : Set (Rd d)) (hU : IsOpen U) (hvol : volume U = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ χ : C_c(Rd d, ℝ), ContDiff ℝ ∞ χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ tsupport χ ⊆ U ∧
      0 < (∫ x : Rd d, (χ x)^2) ∧
      1-ε < (∫ x : Rd d, (χ x)^2) ∧ (∫ x : Rd d, (χ x)^2) ≤ 1 := by
  classical
  let r : ℝ := max (1-ε) (1/2)
  have hrpos : 0 < r :=
    (half_pos (zero_lt_one : (0 : ℝ) < 1)).trans_le (le_max_right _ _)
  have hrone : r < 1 := max_lt (sub_lt_self 1 hε) (half_lt_self zero_lt_one)
  have hr : ENNReal.ofReal r < volume U :=
    (ENNReal.ofReal_lt_one.mpr hrone).trans_eq hvol.symm
  obtain ⟨K0, hK0U, hK0, hK0mass⟩ :=
    hU.measurableSet.exists_lt_isCompact_of_ne_top
      (hvol.trans_ne ENNReal.one_ne_top) hr
  obtain ⟨C, hC, hK0C, hCU⟩ := exists_compact_between hK0 hU hK0U
  obtain ⟨f, hf0, hf1, hfrange⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed
      (𝓘(ℝ, Rd d)) (M := Rd d) (n := (⊤ : ℕ∞))
      (s := (interior C)ᶜ) (t := K0)
      isOpen_interior.isClosed_compl hK0.isClosed
      (Set.disjoint_compl_left_iff_subset.mpr hK0C)
  have hfsm : ContDiff ℝ ∞ (f : Rd d → ℝ) := f.contMDiff.contDiff
  have hsupp : Function.support (f : Rd d → ℝ) ⊆ C := fun x hx =>
    Classical.byContradiction (fun hxC =>
      hx (hf0 (fun hxI => hxC (interior_subset hxI))))
  have hts : tsupport (f : Rd d → ℝ) ⊆ C := closure_minimal hsupp hC.isClosed
  have hfcs : HasCompactSupport (f : Rd d → ℝ) :=
    hC.of_isClosed_subset isClosed_closure hts
  let χ : C_c(Rd d, ℝ) := ⟨⟨(f : Rd d → ℝ), hfsm.continuous⟩, hfcs⟩
  have hχbound (x : Rd d) : 0 ≤ χ x ∧ χ x ≤ 1 := hfrange x
  have hχone (x : Rd d) (hx : x ∈ K0) : χ x = 1 := hf1 hx
  have hχzero (x : Rd d) (hx : x ∉ U) : χ x = 0 :=
    Classical.byContradiction (fun hne => hx (hCU (hsupp hne)))
  have hsq : Integrable (fun x : Rd d => (χ x)^2) volume :=
    Continuous.integrable_of_hasCompactSupport (μ := volume)
      (f := fun x : Rd d => (χ x)^2) (χ.continuous.pow 2)
      (χ.hasCompactSupport.comp_left (g := fun t : ℝ => t^2) (zero_pow two_ne_zero))
  have hK0le : volume K0 ≤ ENNReal.ofReal (∫ x : Rd d, (χ x)^2) :=
    hsq.measure_le_integral (Eventually.of_forall (fun x => sq_nonneg (χ x)))
      (fun x hx => by simpa only [hχone x hx, one_pow] using le_refl (1 : ℝ))
  have hlower : r < (∫ x : Rd d, (χ x)^2) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hrpos.le).1 (hK0mass.trans_le hK0le)
  have hupperNN : ENNReal.ofReal (∫ x : Rd d, (χ x)^2) ≤ volume U :=
    integral_le_measure (μ := (volume : Measure (Rd d))) (s := U)
      (f := fun x => (χ x)^2)
      (fun x _ => pow_le_one₀ (hχbound x).1 (hχbound x).2)
      (fun x hx => by
        simpa only [hχzero x hx, zero_pow two_ne_zero] using le_refl (0 : ℝ))
  have hupper : (∫ x : Rd d, (χ x)^2) ≤ 1 :=
    ENNReal.ofReal_le_one.mp (hupperNN.trans_eq hvol)
  exact ⟨χ, hfsm, hχbound, hts.trans hCU, hrpos.trans hlower,
    (le_max_left (1-ε) (1/2)).trans_lt hlower, hupper⟩

theorem exists_nearIndicator_smooth_cube_window
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ χ : C_c(Rd d, ℝ), ContDiff ℝ ∞ χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ tsupport χ ⊆ cube d 1 ∧
      0 < (∫ x : Rd d, (χ x)^2) ∧
      1-ε < (∫ x : Rd d, (χ x)^2) ∧ (∫ x : Rd d, (χ x)^2) ≤ 1 := by
  let U : Set (Rd d) := {x | ∀ i : Fin d, 0 < x i ∧ x i < 1}
  have hU : IsOpen U := by
    simpa only [U, Set.setOf_forall, Set.preimage, Set.mem_Ioo] using
      isOpen_iInter_of_finite (fun i : Fin d =>
        (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)).preimage
          (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i))
  have hvol : volume U = 1 := by
    simpa only [U, Set.preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_Ioo, Real.volume_pi_Ioo, sub_zero, ENNReal.ofReal_one,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow] using
      (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
        (MeasurableSet.univ_pi (fun _ : Fin d =>
          measurableSet_Ioo (a := (0 : ℝ)) (b := 1))).nullMeasurableSet
  have hUS : U ⊆ cube d 1 := fun x hx i => ⟨(hx i).1.le, (hx i).2⟩
  obtain ⟨χ, hsm, hb, hts, ha, hnear, hle⟩ :=
    exists_nearIndicator_smooth_window_of_open_volume_one d U hU hvol ε hε
  exact ⟨χ, hsm, hb, hts.trans hUS, ha, hnear, hle⟩

end Riesz.Stationary
