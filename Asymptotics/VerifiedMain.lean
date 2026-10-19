import Riesz.Asymptotics.PositiveSphericalAssembly
import Riesz.Asymptotics.NegativeAttainment
import Riesz.Asymptotics.Assembly

/-! Exact main-theorem assembly from the actual positive and negative analytic producers. -/

noncomputable section
open MeasureTheory Filter RieszShowcase
open scoped Topology Asymptotics
namespace Riesz.Asymptotics

/-- Actual positive and negative producers cover the original exponent range. -/
theorem analyticClaims_of_range
    (d : ℕ) (s : ℝ) (hd : 2 ≤ d) (hs_lower : -2 < s)
    (hs_upper : s < (d : ℝ)) (hs_ne : s ≠ 0) : AnalyticClaims d s := by
  rcases lt_or_gt_of_ne hs_ne with hn | hp
  · simpa only [neg_neg] using
      negative_analyticClaims d hd (-s) (neg_pos.mpr hn)
        (by linarith only [hs_lower] : -s < 2)
  · exact positive_analyticClaims d hd s hp hs_upper

/-- Every original showcase clause from genuine analytic producers. -/
theorem verified_main_theorem
    (d : ℕ) (s : ℝ)
    (hd : 2 ≤ d) (hs_lower : -2 < s) (hs_upper : s < (d : ℝ)) (hs_ne : s ≠ 0) :
    (fun N : ℕ =>
      E_s d s N -
        (V_s d s * (N : ℝ) ^ (2 : ℕ) +
          C d s / (omega d) ^ (s / (d : ℝ)) * (N : ℝ) ^ (1 + s / (d : ℝ))))
      =o[atTop] (fun N : ℕ => (N : ℝ) ^ (1 + s / (d : ℝ))) ∧
    C d s = s * e d s ∧
    C d s < 0 ∧
    Tendsto
      (fun N : ℕ =>
        (E_K d s N - V_K d s * (N : ℝ) ^ (2 : ℕ)) /
          (N : ℝ) ^ (1 + s / (d : ℝ)))
      atTop (nhds ((omega d) ^ (-s / (d : ℝ)) * e d s)) ∧
    eExtended d s = (e d s : EReal) ∧
    (0 < s → e d s < 0) ∧
    (s < 0 → 0 < e d s) ∧
    (∃ P : ConfigurationLaw d, Admissible d P ∧ W d s P = (e d s : EReal)) ∧
    (∀ q : ℝ, 0 < q → q < 2 → s = -q →
      Tendsto (fun m : ℕ => b d q m / (m : ℝ) ^ d)
        atTop (nhds (e d (-q))) ∧
      e d (-q) = sInf {r : ℝ | ∃ m : ℕ, 1 ≤ m ∧ r = b d q m / (m : ℝ) ^ d}) := by
  exact main_theorem_of_analyticClaims d s hd hs_lower hs_upper hs_ne
    (analyticClaims_of_range d s hd hs_lower hs_upper hs_ne)

end Riesz.Asymptotics
