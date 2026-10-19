import Riesz.Stationary.Grid
import Riesz.Configuration.LocalSimplicity

/-! Admissibility of the infinite, independently filled and randomly shifted grid.
The energy comparison required by the paper is a separate proof obligation. -/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Classical

namespace Riesz.Stationary

/-- Simplicity holds on the actual pushforward law of configurations. -/
theorem randomShiftGridLaw_ae_simple (d m : ℕ) (hm : 0 < m)
    (Q : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q) :
    ∀ᵐ μ ∂randomShiftGridLaw d m Q, IsSimpleConfiguration d μ := by
  letI : IsProbabilityMeasure Q := hQ.1
  letI := gridMarksLaw_probability d (m ^ d) Q
  letI := Riesz.Negative.cubeUniform_probability d m hm
  apply (ae_map_iff (measurable_gridConfiguration d (m ^ d) (m : ℝ)).aemeasurable
    (Riesz.Configuration.measurableSet_isSimpleConfiguration d)).mpr
  have hmarks := ae_of_ae_map measurable_snd.aemeasurable
    ((measurePreserving_snd (μ := Riesz.Negative.cubeUniform d m)
      (ν := gridMarksLaw d (m ^ d) Q)).map_eq.symm ▸
        gridMarksLaw_good d (m ^ d) (m : ℝ) Q hQ.2.1)
  exact hmarks.mono (fun p hp => gridConfiguration_simple d (m ^ d) (m : ℝ)
    (Nat.cast_pos.mpr hm) p.1 p.2 hp)

/-- Every balanced finite cell law produces an admissible stationary simple law. -/
theorem randomShiftGridLaw_admissible (d m : ℕ) (hm : 0 < m)
    (Q : Measure (Fin (m ^ d) → Rd d))
    (hQ : Riesz.Negative.TupleBalancedAdmissible d m Q) :
    Admissible d (randomShiftGridLaw d m Q) := by
  letI : IsProbabilityMeasure Q := hQ.1
  exact ⟨randomShiftGridLaw_probability d m hm Q, randomShiftGridLaw_ae_simple d m hm Q hQ,
    randomShiftGridLaw_stationary d m hm Q,
    fun D hD _ => randomShiftGridLaw_mean d m hm Q hQ D hD,
    randomShiftGridLaw_local_second_moment d m hm Q hQ⟩

/-- The construction applies to the showcase's measure-valued balanced laws. -/
theorem exists_admissible_grid_law_of_balanced (d m : ℕ) (hm : 0 < m)
    (P : ConfigurationLaw d) (hP : BalancedAdmissible d m P) :
    ∃ Q : Measure (Fin (m ^ d) → Rd d),
      Riesz.Negative.TupleBalancedAdmissible d m Q ∧
      Measure.map (Riesz.Negative.tupleCounting d (m ^ d)) Q = P ∧
      Admissible d (randomShiftGridLaw d m Q) := by
  obtain ⟨Q, hQ, hmap⟩ := Riesz.Negative.exists_tuple_balanced_law d m P hP
  exact ⟨Q, hQ, hmap, randomShiftGridLaw_admissible d m hm Q hQ⟩

/-- The stationary simple class in the Euclidean infimum is nonempty. -/
theorem exists_admissible_law (d : ℕ) (hd : 0 < d) :
    ∃ P : ConfigurationLaw d, Admissible d P := by
  obtain ⟨P, hP⟩ := Riesz.Negative.exists_balanced_law d 1 hd Nat.zero_lt_one
  obtain ⟨Q, _, _, h⟩ := exists_admissible_grid_law_of_balanced d 1 Nat.zero_lt_one P hP
  exact ⟨_, h⟩

end Riesz.Stationary
