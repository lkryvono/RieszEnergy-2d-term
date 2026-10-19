import Riesz.Negative.ReverseCubeLocalization
import Riesz.Negative.LocalizedSignedInput
import Riesz.Negative.ReverseCubeMixture
import Riesz.Stationary.NegativeLocalization
import Riesz.Stationary.NearIndicatorWindow
import Riesz.Stationary.GridEnergyNegative

/-! Constructed balanced cube competitors and the reverse comparison with the original stationary energy. -/

noncomputable section
open MeasureTheory Filter RieszShowcase Riesz.Configuration Riesz.Stationary
open scoped ENNReal Classical Topology ComplexConjugate CompactlySupported RealInnerProductSpace ContDiff

namespace Riesz.Negative
def countStratumRoundedOutput (d m k : ℕ) (R : ℝ)
    (χ h : Rd d → ℝ)
    (p : Measure (Rd d) × RandomRepairedMarks (halfUnitDiffuseCount d m)) :
    Measure (Rd d) :=
  let C := cube d (m : ℝ)
  let n := windowInputCount d C p.1
  let x := windowLabel d n (p.1.restrict C)
  randomRepairedHalfUnitBranch d n m k R x (fun i => χ (x i))
    (cubeRepairedDiffuse d m χ h p.1) p.2

theorem measurable_countStratumRoundedOutput (d m k : ℕ) (R : ℝ)
    (χ h : Rd d → ℝ) (hχ : Measurable χ) (hh : Measurable h) :
    Measurable (countStratumRoundedOutput d m k R χ h) := by
  let C := cube d (m : ℝ)
  let x : (a : ℕ) → Measure (Rd d) → (Fin a → Rd d) :=
    fun a μ => windowLabel d a (μ.restrict C)
  have hx (a : ℕ) : Measurable (x a) :=
    (measurable_windowLabel d a).comp
      (measurable_restrict d C (measurableSet_cube d _))
  have hw (a : ℕ) : Measurable (fun μ i => χ (x a μ i)) :=
    measurable_pi_iff.mpr (fun i => hχ.comp ((measurable_pi_apply i).comp (hx a)))
  let F := fun (a : ℕ)
    (p : Measure (Rd d) × RandomRepairedMarks (halfUnitDiffuseCount d m)) =>
    randomRepairedHalfUnitBranch d a m k R (x a p.1)
      (fun i => χ (x a p.1 i)) (cubeRepairedDiffuse d m χ h p.1) p.2
  have hF (a : ℕ) : Measurable (F a) :=
    jointly_measurable_randomRepairedHalfUnitBranch d a m k
      (fun _ => R) measurable_const (x a) (hx a)
      (fun μ i => χ (x a μ i)) (hw a)
      (cubeRepairedDiffuse d m χ h)
      (measurable_cubeRepairedDiffuse d m χ h hχ hh)
  have hfamily : Measurable (fun p :
      (Measure (Rd d) × RandomRepairedMarks (halfUnitDiffuseCount d m)) × ℕ =>
      F p.2 p.1) := measurable_from_prod_countable_left hF
  have hn : Measurable (fun p : Measure (Rd d) ×
      RandomRepairedMarks (halfUnitDiffuseCount d m) => windowInputCount d C p.1) :=
    (measurable_windowInputCount d C (measurableSet_cube d _)).comp measurable_fst
  exact hfamily.comp (measurable_id.prodMk hn)

def cubeGoodRoundedLaw (d m k : ℕ) (R : ℝ) (χ h : Rd d → ℝ)
    (δ H : ℝ) (P : ConfigurationLaw d) : ConfigurationLaw d :=
  ((P.restrict (cubeRepairGoodEvent d m χ δ H)).prod
    (randomRepairedInputMarks (halfUnitDiffuseCount d m))).map
      (countStratumRoundedOutput d m k R χ h)

def cubeGoodRoundedMean (d m k : ℕ) (R : ℝ) (χ h : Rd d → ℝ)
    (δ H : ℝ) (P : ConfigurationLaw d) : Measure (Rd d) :=
  (cubeGoodRoundedLaw d m k R χ h δ H P).bind id

theorem cubeGoodRoundedMean_apply (d m k : ℕ) (R : ℝ) (χ h : Rd d → ℝ)
    (δ H : ℝ) (P : ConfigurationLaw d) (D : Set (Rd d)) (hD : MeasurableSet D) :
    cubeGoodRoundedMean d m k R χ h δ H P D =
      ∫⁻ μ, μ D ∂cubeGoodRoundedLaw d m k R χ h δ H P := by
  exact Measure.bind_apply hD measurable_id.aemeasurable

theorem cubeGoodRoundedLaw_mass (d m k : ℕ) (R : ℝ) (χ h : Rd d → ℝ)
    (hχ : Measurable χ) (hh : Measurable h) (δ H : ℝ)
    (P : ConfigurationLaw d) [IsFiniteMeasure P] :
    cubeGoodRoundedLaw d m k R χ h δ H P Set.univ =
      P (cubeRepairGoodEvent d m χ δ H) := by
  rw [cubeGoodRoundedLaw, Measure.map_apply
    (measurable_countStratumRoundedOutput d m k R χ h hχ hh) MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ]
  simp only [measure_univ, mul_one]

theorem cubeGoodRoundedLaw_isFiniteMeasure (d m k : ℕ) (R : ℝ)
    (χ h : Rd d → ℝ) (hχ : Measurable χ) (hh : Measurable h) (δ H : ℝ)
    (P : ConfigurationLaw d) [IsFiniteMeasure P] :
    IsFiniteMeasure (cubeGoodRoundedLaw d m k R χ h δ H P) := by
  refine ⟨?_⟩
  rw [cubeGoodRoundedLaw_mass d m k R χ h hχ hh δ H P]
  exact measure_lt_top P _

private theorem measurableSet_cubeFixedSimpleClass (d m : ℕ) :
    MeasurableSet {μ : Measure (Rd d) | IsSimpleConfiguration d μ ∧
      μ (cube d (m : ℝ))ᶜ = 0 ∧ μ Set.univ = (m^d : ℕ)} :=
  (measurableSet_isSimpleConfiguration d).inter
    ((measurableSet_eq_fun (Measure.measurable_coe (measurableSet_cube d _).compl)
      measurable_const).inter
      (measurableSet_eq_fun (Measure.measurable_coe MeasurableSet.univ) measurable_const))

theorem cubeGoodRoundedLaw_class (d m k : ℕ) (hd : 2 ≤ d)
    (R : ℝ) (hR : 0 < R) (hsize : (m : ℝ) = (2 : ℝ)^k*R)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H)
    (P : ConfigurationLaw d) (hP : Admissible d P) :
    ∀ᵐ μ ∂cubeGoodRoundedLaw d m k R χ h δ H P,
      IsSimpleConfiguration d μ ∧ μ (cube d (m : ℝ))ᶜ = 0 ∧
        μ Set.univ = (m^d : ℕ) := by
  letI := hP.1
  let G := cubeRepairGoodEvent d m χ δ H
  let M := randomRepairedInputMarks (halfUnitDiffuseCount d m)
  let F := countStratumRoundedOutput d m k R χ h
  have hF : Measurable F := measurable_countStratumRoundedOutput d m k R χ h
    hinput.cutoff_measurable hinput.correction_measurable
  have hclass := measurableSet_cubeFixedSimpleClass d m
  change ∀ᵐ μ ∂((P.restrict G).prod M).map F,
    IsSimpleConfiguration d μ ∧ μ (cube d (m : ℝ))ᶜ = 0 ∧ μ Set.univ = (m^d : ℕ)
  apply (ae_map_iff hF.aemeasurable hclass).2
  apply (Measure.ae_prod_iff_ae_ae (hclass.preimage hF)).2
  filter_upwards [ae_restrict_of_ae hP.2.1,
    ae_restrict_mem (measurableSet_cubeRepairGoodEvent d m χ hinput.cutoff_measurable δ H)]
      with μ hμ hgood
  let a := windowInputCount d (cube d (m : ℝ)) μ
  let x := windowLabel d a (μ.restrict (cube d (m : ℝ)))
  have hl := window_selected_bounded_label_spec d μ hμ (cube d (m : ℝ))
    (measurableSet_cube d _) (cube_isBounded d _)
  have hs := (randomRepairedHalfUnitBranch_cube_input d m a k hd R hR hsize
    χ h δ H hinput μ hgood x hl.1 hl.2.1).1
  exact hs.mono (fun p hp => ⟨hp.1.1, hp.2, hp.1.2⟩)

theorem cubeGoodRoundedMean_mass (d m k : ℕ) (hd : 2 ≤ d)
    (R : ℝ) (hR : 0 < R) (hsize : (m : ℝ) = (2 : ℝ)^k*R)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H)
    (P : ConfigurationLaw d) (hP : Admissible d P) :
    cubeGoodRoundedMean d m k R χ h δ H P Set.univ =
      ((m^d : ℕ) : ℝ≥0∞)*P (cubeRepairGoodEvent d m χ δ H) := by
  letI := hP.1
  rw [cubeGoodRoundedMean_apply d m k R χ h δ H P Set.univ MeasurableSet.univ]
  calc
    _ = ∫⁻ _μ, ((m^d : ℕ) : ℝ≥0∞)
        ∂cubeGoodRoundedLaw d m k R χ h δ H P :=
      lintegral_congr_ae ((cubeGoodRoundedLaw_class d m k hd R hR hsize χ h δ H
        hinput P hP).mono (fun _ hμ => hμ.2.2))
    _ = _ := by
      rw [lintegral_const, cubeGoodRoundedLaw_mass d m k R χ h
        hinput.cutoff_measurable hinput.correction_measurable δ H P]

theorem cubeGoodRoundedMean_isFiniteMeasure (d m k : ℕ) (hd : 2 ≤ d)
    (R : ℝ) (hR : 0 < R) (hsize : (m : ℝ) = (2 : ℝ)^k*R)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H)
    (P : ConfigurationLaw d) (hP : Admissible d P) :
    IsFiniteMeasure (cubeGoodRoundedMean d m k R χ h δ H P) := by
  letI := hP.1
  refine ⟨?_⟩
  rw [cubeGoodRoundedMean_mass d m k hd R hR hsize χ h δ H hinput P hP]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (measure_lt_top P _)

theorem cubeGoodRoundedMean_eq_repaired (d m k : ℕ) (hd : 2 ≤ d)
    (R : ℝ) (hR : 0 < R) (hsize : (m : ℝ) = (2 : ℝ)^k*R)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H)
    (P : ConfigurationLaw d) (hP : Admissible d P)
    (D : Set (Rd d)) (hD : MeasurableSet D) :
    cubeGoodRoundedMean d m k R χ h δ H P D =
      ∫⁻ μ in cubeRepairGoodEvent d m χ δ H,
        ((μ.restrict (cube d (m : ℝ))).withDensity (fun x => ENNReal.ofReal (χ x)) +
          (cubeRepairedDiffuse d m χ h μ : Measure (Rd d))) D ∂P := by
  letI := hP.1
  let G := cubeRepairGoodEvent d m χ δ H
  let M := randomRepairedInputMarks (halfUnitDiffuseCount d m)
  let F := countStratumRoundedOutput d m k R χ h
  have hF : Measurable F := measurable_countStratumRoundedOutput d m k R χ h
    hinput.cutoff_measurable hinput.correction_measurable
  rw [cubeGoodRoundedMean_apply d m k R χ h δ H P D hD]
  change (∫⁻ ν, ν D ∂((P.restrict G).prod M).map F) = _
  rw [lintegral_map (Measure.measurable_coe hD) hF]
  rw [show (∫⁻ p, (F p) D ∂(P.restrict G).prod M) =
      ∫⁻ μ, ∫⁻ z, (F (μ, z)) D ∂M ∂P.restrict G from
    lintegral_prod (fun p => (F p) D) ((Measure.measurable_coe hD).comp hF).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hP.2.1,
    ae_restrict_mem (measurableSet_cubeRepairGoodEvent d m χ hinput.cutoff_measurable δ H)]
      with μ hμ hgood
  let a := windowInputCount d (cube d (m : ℝ)) μ
  let x := windowLabel d a (μ.restrict (cube d (m : ℝ)))
  have hl := window_selected_bounded_label_spec d μ hμ (cube d (m : ℝ))
    (measurableSet_cube d _) (cube_isBounded d _)
  exact (randomRepairedHalfUnitBranch_cube_input d m a k hd R hR hsize
    χ h δ H hinput μ hgood x hl.1 hl.2.1).2 D hD

theorem cubeCutoffDiscrepancy_integrable_and_mean_zero (d m : ℕ)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H)
    (P : ConfigurationLaw d) (hP : Admissible d P) :
    Integrable (cubeCutoffDiscrepancy d m χ) P ∧
      (∫ μ, cubeCutoffDiscrepancy d m χ μ ∂P) = 0 := by
  letI := hP.1
  let C := cube d (m : ℝ)
  let ρ := (volume : Measure (Rd d)).restrict C
  let F : Measure (Rd d) → ℝ≥0∞ :=
    fun μ => ∫⁻ x, ENNReal.ofReal (χ x) ∂μ.restrict C
  have hC : MeasurableSet C := measurableSet_cube d _
  letI : IsFiniteMeasure ρ := cube_background_isFiniteMeasure d m
  have hFm : Measurable F :=
    (Measure.measurable_lintegral hinput.cutoff_measurable.ennreal_ofReal).comp
      (measurable_restrict d C hC)
  have hχnn : 0 ≤ᵐ[ρ] χ := by
    filter_upwards [ae_restrict_mem hC] with x hx
    exact (hinput.cutoff_bounds x hx).1
  have hχInt : Integrable χ ρ := by
    refine (integrable_const (1 : ℝ)).mono'
      hinput.cutoff_measurable.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hC] with x hx
    rw [Real.norm_of_nonneg (hinput.cutoff_bounds x hx).1]
    exact (hinput.cutoff_bounds x hx).2.trans (by linarith [hinput.slack_pos])
  have hNNmean : (∫⁻ μ, F μ ∂P) = ∫⁻ x, ENNReal.ofReal (χ x) ∂ρ := by
    calc
      _ = ∫⁻ μ, (∫⁻ x, C.indicator (fun x => ENNReal.ofReal (χ x)) x ∂μ) ∂P :=
        lintegral_congr (fun μ => (lintegral_indicator hC (fun x => ENNReal.ofReal (χ x))).symm)
      _ = ∫⁻ x, C.indicator (fun x => ENNReal.ofReal (χ x)) x ∂volume :=
        Riesz.Stationary.originalAdmissible_mean_lintegral d P hP
          (C.indicator (fun x => ENNReal.ofReal (χ x)))
          (hinput.cutoff_measurable.ennreal_ofReal.indicator hC)
      _ = _ := lintegral_indicator hC (fun x => ENNReal.ofReal (χ x))
  have hvolfin : (∫⁻ x, ENNReal.ofReal (χ x) ∂ρ) ≠ ⊤ :=
    (ofReal_integral_eq_lintegral_ofReal hχInt hχnn).symm.trans_ne ENNReal.ofReal_ne_top
  have hFfin : (∫⁻ μ, F μ ∂P) ≠ ⊤ := hNNmean.trans_ne hvolfin
  have hIF : Integrable (fun μ => (F μ).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hFm.aemeasurable hFfin
  have hmeanReal : (∫ μ, (F μ).toReal ∂P) = ∫ x in C, χ x ∂volume := by
    calc
      _ = (∫⁻ μ, F μ ∂P).toReal :=
        integral_toReal hFm.aemeasurable (ae_lt_top hFm hFfin)
      _ = (∫⁻ x, ENNReal.ofReal (χ x) ∂ρ).toReal := congrArg ENNReal.toReal hNNmean
      _ = _ := (integral_eq_lintegral_of_nonneg_ae hχnn
        hinput.cutoff_measurable.aestronglyMeasurable).symm
  refine ⟨hIF.sub (integrable_const _), ?_⟩
  change (∫ μ, (F μ).toReal - (∫ x in C, χ x ∂volume) ∂P) = 0
  rw [integral_sub hIF (integrable_const _), hmeanReal, integral_const]
  simp only [probReal_univ, one_smul, sub_self]

theorem cubeRepairDensity_good_average (d m : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H)
    (P : ConfigurationLaw d) (hP : Admissible d P)
    (x : Rd d) (hx : x ∈ cube d (m : ℝ)) :
    (∫⁻ μ in cubeRepairGoodEvent d m χ δ H,
      cubeRepairDensity d m χ h μ x ∂P) =
      ENNReal.ofReal
        (P.real (cubeRepairGoodEvent d m χ δ H) * (1 - χ x) -
          (∫ μ in cubeRepairGoodEvent d m χ δ H,
            cubeCutoffDiscrepancy d m χ μ ∂P) * h x) := by
  letI := hP.1
  let G := cubeRepairGoodEvent d m χ δ H
  have hG : MeasurableSet G :=
    measurableSet_cubeRepairGoodEvent d m χ hinput.cutoff_measurable δ H
  have hDi := (cubeCutoffDiscrepancy_integrable_and_mean_zero d m χ h δ H
    hinput P hP).1
  have hrawi : Integrable (fun μ => cubeRepairRawDensity d m χ h μ x)
      (P.restrict G) :=
    (integrable_const (1 - χ x)).sub (hDi.integrableOn.mul_const (h x))
  have hrawnn : 0 ≤ᵐ[P.restrict G]
      (fun μ => cubeRepairRawDensity d m χ h μ x) := by
    filter_upwards [ae_restrict_mem hG] with μ hμ
    exact (half_pos hinput.slack_pos).le.trans
      (cubeRepairRawDensity_bounds d m χ h δ H hinput μ hμ x hx).1
  calc
    _ = ∫⁻ μ in G, ENNReal.ofReal (cubeRepairRawDensity d m χ h μ x) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hG] with μ hμ
      exact min_eq_right (by
        simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal
          (cubeRepairRawDensity_bounds d m χ h δ H hinput μ hμ x hx).2)
    _ = ENNReal.ofReal (∫ μ in G, cubeRepairRawDensity d m χ h μ x ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hrawi hrawnn).symm
    _ = _ := by
      congr 1
      change (∫ μ in G, (1 - χ x) - cubeCutoffDiscrepancy d m χ μ * h x ∂P) = _
      rw [integral_sub (integrable_const _) (hDi.integrableOn.mul_const (h x)),
        integral_const, integral_mul_const]
      simp only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
      rfl

private theorem measurable_cubeCutoffEvaluation (d m : ℕ) (χ : Rd d → ℝ)
    (hχ : Measurable χ) (E : Set (Rd d)) (hE : MeasurableSet E) :
    Measurable (fun μ : Measure (Rd d) =>
      (μ.restrict (cube d (m : ℝ))).withDensity (fun x => ENNReal.ofReal (χ x)) E) := by
  let C := cube d (m : ℝ)
  let a : Rd d → ℝ≥0∞ := C.indicator (E.indicator (fun x => ENNReal.ofReal (χ x)))
  have ha : Measurable a :=
    (hχ.ennreal_ofReal.indicator hE).indicator (measurableSet_cube d _)
  have heq : (fun μ : Measure (Rd d) =>
      (μ.restrict C).withDensity (fun x => ENNReal.ofReal (χ x)) E) =
      (fun μ => ∫⁻ x, a x ∂μ) := by
    funext μ
    rw [withDensity_apply _ hE, ← lintegral_indicator hE,
      ← lintegral_indicator (measurableSet_cube d _)]
  rw [heq]
  exact Measure.measurable_lintegral ha

theorem cubeGoodCutoffMean_le (d m : ℕ) (χ : Rd d → ℝ) (hχ : Measurable χ)
    (δ H : ℝ) (P : ConfigurationLaw d) (hP : Admissible d P)
    (E : Set (Rd d)) (hE : MeasurableSet E) :
    (∫⁻ μ in cubeRepairGoodEvent d m χ δ H,
      (μ.restrict (cube d (m : ℝ))).withDensity
        (fun x => ENNReal.ofReal (χ x)) E ∂P) ≤
      (volume.restrict (cube d (m : ℝ))).withDensity
        (fun x => ENNReal.ofReal (χ x)) E := by
  let C := cube d (m : ℝ)
  let a : Rd d → ℝ≥0∞ := C.indicator (E.indicator (fun x => ENNReal.ofReal (χ x)))
  have ha : Measurable a :=
    (hχ.ennreal_ofReal.indicator hE).indicator (measurableSet_cube d _)
  calc
    _ ≤ ∫⁻ μ, (μ.restrict C).withDensity (fun x => ENNReal.ofReal (χ x)) E ∂P :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ μ, ∫⁻ x, a x ∂μ ∂P := by
      apply lintegral_congr
      intro μ
      rw [withDensity_apply _ hE, ← lintegral_indicator hE,
        ← lintegral_indicator (measurableSet_cube d _)]
    _ = ∫⁻ x, a x ∂volume :=
      Riesz.Stationary.originalAdmissible_mean_lintegral d P hP a ha
    _ = _ := by
      rw [withDensity_apply _ hE, ← lintegral_indicator hE,
        ← lintegral_indicator (measurableSet_cube d _)]

theorem cubeGoodRoundedMean_le (d m k : ℕ) (hd : 2 ≤ d)
    (R : ℝ) (hR : 0 < R) (hsize : (m : ℝ) = (2 : ℝ)^k*R)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H)
    (P : ConfigurationLaw d) (hP : Admissible d P) :
    cubeGoodRoundedMean d m k R χ h δ H P ≤
      (1 + ENNReal.ofReal (H *
        |∫ μ in cubeRepairGoodEvent d m χ δ H,
          cubeCutoffDiscrepancy d m χ μ ∂P| / (m : ℝ)^d)) •
        volume.restrict (cube d (m : ℝ)) := by
  letI := hP.1
  let C := cube d (m : ℝ)
  let G := cubeRepairGoodEvent d m χ δ H
  let ρ : Measure (Rd d) := volume.restrict C
  let e : ℝ := ∫ μ in G, cubeCutoffDiscrepancy d m χ μ ∂P
  let ε : ℝ := H * |e| / (m : ℝ)^d
  letI : IsFiniteMeasure ρ := cube_background_isFiniteMeasure d m
  have hV : 0 < (m : ℝ)^d := pow_pos (Nat.cast_pos.mpr hinput.side_pos) d
  have hε : 0 ≤ ε := div_nonneg (mul_nonneg
    hinput.correction_bound_pos.le (abs_nonneg e)) hV.le
  have hg : P.real G ≤ 1 := by
    simpa only [probReal_univ] using
      (measureReal_mono (μ := P) (Set.subset_univ G))
  have hrawm : Measurable (fun p : Measure (Rd d) × Rd d =>
      cubeRepairDensity d m χ h p.1 p.2) :=
    measurable_const.min (((measurable_const.sub
      (hinput.cutoff_measurable.comp measurable_snd)).sub
      (((measurable_cubeCutoffDiscrepancy d m χ hinput.cutoff_measurable).comp
        measurable_fst).mul (hinput.correction_measurable.comp measurable_snd))).ennreal_ofReal)
  have hpoint (x : Rd d) (hx : x ∈ C) :
      ENNReal.ofReal (χ x) +
        (∫⁻ μ in G, cubeRepairDensity d m χ h μ x ∂P) ≤
      1 + ENNReal.ofReal ε := by
    rw [cubeRepairDensity_good_average d m χ h δ H hinput P hP x hx]
    let b : ℝ := (1 - χ x) + |e| * h x
    have hχnn := (hinput.cutoff_bounds x hx).1
    have hχle : χ x ≤ 1 := (hinput.cutoff_bounds x hx).2.trans
      (by linarith [hinput.slack_pos])
    have hhnn := (hinput.correction_bounds x hx).1
    have hmeanle : P.real G * (1 - χ x) - e * h x ≤ b := by
      have h1 := mul_le_mul_of_nonneg_right hg (sub_nonneg.mpr hχle)
      have h2 := mul_le_mul_of_nonneg_right (neg_le_abs e) hhnn
      dsimp only [b]
      nlinarith only [h1, h2]
    have hb : 0 ≤ b := add_nonneg (sub_nonneg.mpr hχle)
      (mul_nonneg (abs_nonneg e) hhnn)
    have hcorr : |e| * h x ≤ ε := by
      calc
        _ ≤ |e| * (H / (m : ℝ)^d) :=
          mul_le_mul_of_nonneg_left (hinput.correction_bounds x hx).2 (abs_nonneg e)
        _ = ε := by dsimp only [ε]; ring
    calc
      _ ≤ ENNReal.ofReal (χ x) + ENNReal.ofReal b :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal hmeanle)
      _ = ENNReal.ofReal (χ x + b) := (ENNReal.ofReal_add hχnn hb).symm
      _ ≤ ENNReal.ofReal (1 + ε) := ENNReal.ofReal_le_ofReal (by
        dsimp only [b]
        linarith only [hcorr])
      _ = _ := by rw [ENNReal.ofReal_add (by norm_num) hε]; norm_num
  apply Measure.le_iff.2
  intro E hE
  have hcutm := measurable_cubeCutoffEvaluation d m χ hinput.cutoff_measurable E hE
  have hdiff :
      (∫⁻ μ in G, (cubeRepairedDiffuse d m χ h μ : Measure (Rd d)) E ∂P) =
      ∫⁻ x in E, ∫⁻ μ in G, cubeRepairDensity d m χ h μ x ∂P ∂ρ := by
    calc
      _ = ∫⁻ μ in G, ∫⁻ x in E, cubeRepairDensity d m χ h μ x ∂ρ ∂P := by
        apply lintegral_congr
        intro μ
        change ρ.withDensity (cubeRepairDensity d m χ h μ) E = _
        exact withDensity_apply _ hE
      _ = _ := lintegral_lintegral_swap
        (μ := P.restrict G) (ν := ρ.restrict E)
        (f := fun μ x => cubeRepairDensity d m χ h μ x) hrawm.aemeasurable
  rw [cubeGoodRoundedMean_eq_repaired d m k hd R hR hsize χ h δ H hinput P hP E hE]
  simp only [Measure.add_apply]
  rw [lintegral_add_left (μ := P.restrict G)
    (f := fun μ : Measure (Rd d) =>
      (μ.restrict C).withDensity (fun x => ENNReal.ofReal (χ x)) E) hcutm
    (fun μ => (cubeRepairedDiffuse d m χ h μ : Measure (Rd d)) E), hdiff]
  calc
    _ ≤ ρ.withDensity (fun x => ENNReal.ofReal (χ x)) E +
        ∫⁻ x in E, ∫⁻ μ in G, cubeRepairDensity d m χ h μ x ∂P ∂ρ :=
      add_le_add (cubeGoodCutoffMean_le d m χ hinput.cutoff_measurable
        δ H P hP E hE) le_rfl
    _ = ∫⁻ x in E, ENNReal.ofReal (χ x) +
        (∫⁻ μ in G, cubeRepairDensity d m χ h μ x ∂P) ∂ρ := by
      rw [withDensity_apply _ hE]
      exact (lintegral_add_left (μ := ρ.restrict E)
        (f := fun x => ENNReal.ofReal (χ x))
        hinput.cutoff_measurable.ennreal_ofReal
        (fun x => ∫⁻ μ in G, cubeRepairDensity d m χ h μ x ∂P)).symm
    _ ≤ ∫⁻ _x in E, 1 + ENNReal.ofReal ε ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae
        (ae_restrict_mem (measurableSet_cube d (m : ℝ)))] with x hx
      exact hpoint x hx
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ,
        Measure.smul_apply, smul_eq_mul]
      rfl

theorem cubeGoodRoundedMean_scaled_le (d m k : ℕ) (hd : 2 ≤ d)
    (R : ℝ) (hR : 0 < R) (hsize : (m : ℝ) = (2 : ℝ)^k*R)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hinput : CubeRepairInputHypotheses d m χ h δ H)
    (P : ConfigurationLaw d) (hP : Admissible d P) :
    (1 + ENNReal.ofReal (H *
      |∫ μ in cubeRepairGoodEvent d m χ δ H,
        cubeCutoffDiscrepancy d m χ μ ∂P| / (m : ℝ)^d))⁻¹ •
      cubeGoodRoundedMean d m k R χ h δ H P ≤
        volume.restrict (cube d (m : ℝ)) := by
  apply scaled_good_intensity_le
  · exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1)
      le_self_add)
  · exact ENNReal.add_ne_top.mpr ⟨by norm_num, ENNReal.ofReal_ne_top⟩
  · exact cubeGoodRoundedMean_le d m k hd R hR hsize χ h δ H hinput P hP

private theorem cubeCutoffMass_integrable_and_mean (d m : ℕ)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hi : CubeRepairInputHypotheses d m χ h δ H)
    (P : ConfigurationLaw d) (hP : Admissible d P) :
    Integrable (cubeCutoffMass d m χ) P ∧
      (∫ μ, cubeCutoffMass d m χ μ ∂P) = ∫ x in cube d (m : ℝ), χ x ∂volume := by
  letI := hP.1
  let c : ℝ := ∫ x in cube d (m : ℝ), χ x ∂volume
  obtain ⟨hDi, hDz⟩ := cubeCutoffDiscrepancy_integrable_and_mean_zero d m χ h δ H hi P hP
  have heq : (fun μ => cubeCutoffDiscrepancy d m χ μ + c) = cubeCutoffMass d m χ := by
    funext μ
    dsimp only [cubeCutoffDiscrepancy, c]
    ring
  have hsum := hDi.add (integrable_const c)
  change Integrable (fun μ => cubeCutoffDiscrepancy d m χ μ + c) P at hsum
  rw [heq] at hsum
  refine ⟨hsum, ?_⟩
  rw [← heq, integral_add hDi (integrable_const c), hDz, integral_const]
  simp only [probReal_univ, one_smul, zero_add]
  rfl

private theorem cubeRepairInputHypotheses_sq (d m : ℕ)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hi : CubeRepairInputHypotheses d m χ h δ H) :
    CubeRepairInputHypotheses d m (fun x => (χ x)^2) h δ H := by
  refine ⟨hi.side_pos, hi.cutoff_measurable.pow_const 2, hi.correction_measurable,
    hi.slack_pos, hi.slack_lt_one, hi.correction_bound_pos, ?_,
    hi.correction_bounds, hi.correction_integral⟩
  intro x hx
  obtain ⟨h0, h1⟩ := hi.cutoff_bounds x hx
  refine ⟨sq_nonneg _, ?_⟩
  have hunit : χ x ≤ 1 := h1.trans (by linarith [hi.slack_pos])
  have hsquare : (χ x)^2 ≤ χ x := by nlinarith only [h0, hunit]
  exact hsquare.trans h1

private theorem cubeCutoffMass_eq_sum (d m a : ℕ) (χ : Rd d → ℝ)
    (μ : Measure (Rd d)) (x : Fin a → Rd d)
    (hlabels : tupleCounting d a x = μ.restrict (cube d (m : ℝ)))
    (hχ : ∀ i, 0 ≤ χ (x i)) :
    cubeCutoffMass d m χ μ = ∑ i, χ (x i) := by
  simp [cubeCutoffMass, ← hlabels, tupleCounting, lintegral_finsetSum_measure,
    ENNReal.toReal_sum, hχ]

theorem cubeCutoffSquareMass_le (d m : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hi : CubeRepairInputHypotheses d m χ h δ H)
    (μ : Measure (Rd d)) (hμ : IsSimpleConfiguration d μ) :
    cubeCutoffMass d m (fun x => (χ x)^2) μ ≤ cubeCutoffMass d m χ μ := by
  let C := cube d (m : ℝ)
  let a := windowInputCount d C μ
  let x := windowLabel d a (μ.restrict C)
  have hl := window_selected_bounded_label_spec d μ hμ C
    (measurableSet_cube d _) (cube_isBounded d _)
  have hx : ∀ i, x i ∈ C := hl.2.2
  have hχ0 : ∀ i, 0 ≤ χ (x i) := fun i => (hi.cutoff_bounds (x i) (hx i)).1
  rw [cubeCutoffMass_eq_sum d m a _ μ x hl.2.1 (fun i => sq_nonneg (χ (x i))),
    cubeCutoffMass_eq_sum d m a χ μ x hl.2.1 hχ0]
  apply Finset.sum_le_sum
  intro i _
  have hunit : χ (x i) ≤ 1 := (hi.cutoff_bounds (x i) (hx i)).2.trans
    (by linarith [hi.slack_pos])
  nlinarith only [hχ0 i, hunit]

theorem cubeRoundingBudget_eq_volume_sub_squareMass
    (d m a : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hi : CubeRepairInputHypotheses d m χ h δ H)
    (μ : Measure (Rd d)) (hg : μ ∈ cubeRepairGoodEvent d m χ δ H)
    (x : Fin a → Rd d)
    (hlabels : tupleCounting d a x = μ.restrict (cube d (m : ℝ))) :
    totalFractionalBudget (fun i => χ (x i)) +
        ((cubeRepairedDiffuse d m χ h μ).mass : ℝ) =
      (m : ℝ)^d - cubeCutoffMass d m (fun y => (χ y)^2) μ := by
  obtain ⟨hx, hχ, _, hmass⟩ :=
    cubeRepairedDiffuse_labeled_inputs d m a χ h δ H hi μ hg x hlabels
  have hsq := cubeCutoffMass_eq_sum d m a (fun y => (χ y)^2) μ x hlabels
    (fun i => sq_nonneg (χ (x i)))
  have hbudget : totalFractionalBudget (fun i => χ (x i)) =
      (∑ i, χ (x i)) - ∑ i, (χ (x i))^2 := by
    rw [totalFractionalBudget, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [fractionalBudget]
    ring
  rw [hbudget, hsq]
  rw [Nat.cast_pow] at hmass
  nlinarith only [hmass]

theorem cubeGoodRoundingBudget_bound (d m : ℕ) (χ h : Rd d → ℝ) (δ H : ℝ)
    (hi : CubeRepairInputHypotheses d m χ h δ H)
    (P : ConfigurationLaw d) (hP : Admissible d P)
    (hD2 : Integrable (fun μ => (cubeCutoffDiscrepancy d m χ μ)^2) P) :
    let G := cubeRepairGoodEvent d m χ δ H
    let M := ∫ μ, (cubeCutoffDiscrepancy d m χ μ)^2 ∂P
    let T := δ*(m : ℝ)^d/(2*H)
    Integrable (fun μ => (m : ℝ)^d - cubeCutoffMass d m (fun x => (χ x)^2) μ) P ∧
      (∫ μ in G, (m : ℝ)^d - cubeCutoffMass d m (fun x => (χ x)^2) μ ∂P) ≤
        (m : ℝ)^d - (∫ x in cube d (m : ℝ), (χ x)^2 ∂volume) + M/T := by
  dsimp only
  letI := hP.1
  let C := cube d (m : ℝ)
  let G := cubeRepairGoodEvent d m χ δ H
  let V : ℝ := (m : ℝ)^d
  let D := cubeCutoffDiscrepancy d m χ
  let M : ℝ := ∫ μ, (D μ)^2 ∂P
  let T : ℝ := δ*V/(2*H)
  let S := cubeCutoffMass d m (fun x => (χ x)^2)
  let B : Measure (Rd d) → ℝ := fun μ => V-S μ
  have hG : MeasurableSet G :=
    measurableSet_cubeRepairGoodEvent d m χ hi.cutoff_measurable δ H
  have hDi := cubeCutoffDiscrepancy_integrable_and_mean_zero d m χ h δ H hi P hP
  have hSq := cubeCutoffMass_integrable_and_mean d m (fun x => (χ x)^2) h δ H
    (cubeRepairInputHypotheses_sq d m χ h δ H hi) P hP
  have hBi : Integrable B P := (integrable_const V).sub hSq.1
  have hV : 0 < V := pow_pos (Nat.cast_pos.mpr hi.side_pos) d
  have hT : 0 < T := div_pos (mul_pos hi.slack_pos hV)
    (mul_pos (by norm_num) hi.correction_bound_pos)
  have hbad : {μ | T < |D μ|} = Gᶜ := by
    ext μ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, G, cubeRepairGoodEvent,
      not_le, T, V, D]
  have htail := square_tail_mass_and_mean_bounds P D
    (measurable_cubeCutoffDiscrepancy d m χ hi.cutoff_measurable)
    hDi.1 hD2 hDi.2 T hT
  dsimp only at htail
  rw [hbad] at htail
  let ρ : Measure (Rd d) := volume.restrict C
  letI : IsFiniteMeasure ρ := cube_background_isFiniteMeasure d m
  have hχi : Integrable χ ρ := by
    refine (integrable_const (1 : ℝ)).mono' hi.cutoff_measurable.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_cube d _)] with x hx
    rw [Real.norm_of_nonneg (hi.cutoff_bounds x hx).1]
    exact (hi.cutoff_bounds x hx).2.trans (by linarith [hi.slack_pos])
  have hc : (∫ x in C, χ x ∂volume) ≤ V := by
    have hle : χ ≤ᵐ[ρ] (fun _ => (1 : ℝ)) := by
      filter_upwards [ae_restrict_mem (measurableSet_cube d _)] with x hx
      exact (hi.cutoff_bounds x hx).2.trans (by linarith [hi.slack_pos])
    have hh := integral_mono_ae hχi (integrable_const (1 : ℝ)) hle
    simpa [ρ, integral_const, measureReal_def, volume_cube, V, C] using hh
  have hpoint : (fun μ => -(D μ)) ≤ᵐ[P.restrict Gᶜ] B := by
    filter_upwards [ae_restrict_of_ae hP.2.1] with μ hμ
    have hsq := cubeCutoffSquareMass_le d m χ h δ H hi μ hμ
    change -cubeCutoffDiscrepancy d m χ μ ≤ V - cubeCutoffMass d m (fun x => (χ x)^2) μ
    dsimp only [cubeCutoffDiscrepancy]
    linarith only [hsq, hc]
  have hbadlow := integral_mono_ae hDi.1.neg.integrableOn hBi.integrableOn hpoint
  change (∫ μ in Gᶜ, -(D μ) ∂P) ≤ ∫ μ in Gᶜ, B μ ∂P at hbadlow
  rw [integral_neg] at hbadlow
  have hfull : (∫ μ, B μ ∂P) = V-(∫ x in C, (χ x)^2 ∂volume) := by
    rw [integral_sub (integrable_const V) hSq.1, integral_const, hSq.2]
    simp only [probReal_univ, one_smul]
    rfl
  have hsplit := integral_add_compl hG hBi
  rw [hfull] at hsplit
  refine ⟨hBi, ?_⟩
  have hmeanTail := htail.2.1
  have habs := le_abs_self (∫ μ in Gᶜ, D μ ∂P)
  change (∫ μ in G, B μ ∂P) ≤ V-(∫ x in C, (χ x)^2 ∂volume)+M/T
  linarith only [hsplit, hbadlow, hmeanTail, habs]


private theorem cubeCutoffDiscrepancy_eq_compact
    (d m : ℕ) (φ : C_c(Rd d, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
    (hs : tsupport φ ⊆ cube d (m : ℝ)) (η : CountingConfiguration d) :
    cubeCutoffDiscrepancy d m φ η.val =
      (∫ x, φ x ∂η.val) - ∫ x, φ x ∂volume := by
  have hC := measurableSet_cube d (m : ℝ)
  have hsφ : Function.support (φ : Rd d → ℝ) ⊆ cube d (m : ℝ) :=
    (subset_tsupport φ).trans hs
  have hsNN : Function.support (fun x => ENNReal.ofReal (φ x)) ⊆ cube d (m : ℝ) := by
    intro x hx
    apply hsφ
    intro hzero
    exact hx (by simp only [hzero, ENNReal.ofReal_zero])
  rw [cubeCutoffDiscrepancy, cubeCutoffMass, ← lintegral_indicator hC,
    Set.indicator_eq_self.mpr hsNN,
    ← ofReal_integral_eq_lintegral_ofReal φ.integrable (Eventually.of_forall hφ),
    ENNReal.toReal_ofReal (integral_nonneg hφ), ← integral_indicator hC,
    Set.indicator_eq_self.mpr hsφ]

theorem cubeGoodRoundedLaw_expected_D_q_le
    (d m k : ℕ) (hd : 2 ≤ d) (hm : 0 < m)
    (R q τ : ℝ) (hR : 1 ≤ R) (hq : 0 < q) (hqTwo : q < 2) (hτ : 0 < τ)
    (hsize : (m : ℝ) = (2 : ℝ)^k*R)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (χ h : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (hh : ∀ x, 0 ≤ h x)
    (hχsm : ContDiff ℝ ∞ χ) (hhsm : ContDiff ℝ ∞ h)
    (hhmass : (∫ x : Rd d, h x) = 1) (δ H : ℝ)
    (hi : CubeRepairInputHypotheses d m
      (fun x => χ ((m : ℝ)⁻¹ • x))
      (fun x => ((m : ℝ)^d)⁻¹*h ((m : ℝ)⁻¹ • x)) δ H)
    (hφs : tsupport (fun x : Rd d => χ ((m : ℝ)⁻¹ • x)) ⊆ cube d (m : ℝ))
    (hHs : tsupport (fun x : Rd d => ((m : ℝ)^d)⁻¹*h ((m : ℝ)⁻¹ • x)) ⊆ cube d (m : ℝ))
    (L : ℝ) (hdiam : ∀ x ∈ cube d (m : ℝ), ∀ y ∈ cube d (m : ℝ), ‖x-y‖ ≤ L) :
    let hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    let φ := angularScaledCompactWindow d χ (m : ℝ) hmR
    let Hm : C_c(Rd d, ℝ) := ((m : ℝ)^d)⁻¹ • angularScaledCompactWindow d h (m : ℝ) hmR
    let A := cubeGoodRoundedLaw d m k R φ Hm δ H P
    let M := ∫ μ, (cubeCutoffDiscrepancy d m φ μ)^2 ∂P
    let T := δ*(m : ℝ)^d/(2*H)
    Integrable (D_q d q m) A ∧
      (∫ μ, D_q d q m μ ∂A) ≤
        (1+τ)*(∫ η : CountingConfiguration d,
          Riesz.Analysis.signedDiscrepancyEnergy q
            (negativeR1ScaledInput d χ h (m : ℝ) hmR η) ∂countingLawOfSimple d P) +
        (1+τ⁻¹)*(8*(Real.sqrt d*(1/2))^q/q+2*cubeRoundingConstant d q)*
          (R^q*((m : ℝ)^d-(∫ x in cube d (m : ℝ), (φ x)^2 ∂volume)+M/T) +
            (m : ℝ)^d*R^(q-(d : ℝ))) := by
  dsimp only
  letI := hP.1
  letI := cube_background_isFiniteMeasure d m
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  let φ := angularScaledCompactWindow d χ (m : ℝ) hmR
  let Hm : C_c(Rd d, ℝ) := ((m : ℝ)^d)⁻¹ • angularScaledCompactWindow d h (m : ℝ) hmR
  let A := cubeGoodRoundedLaw d m k R φ Hm δ H P
  let G := cubeRepairGoodEvent d m φ δ H
  let Z := randomRepairedInputMarks (halfUnitDiffuseCount d m)
  let F := countStratumRoundedOutput d m k R φ Hm
  let V : ℝ := (m : ℝ)^d
  let B : Measure (Rd d) → ℝ := fun μ => V-cubeCutoffMass d m (fun x => (φ x)^2) μ
  let M : ℝ := ∫ μ, (cubeCutoffDiscrepancy d m φ μ)^2 ∂P
  let T : ℝ := δ*V/(2*H)
  let c : ℝ := 8*(Real.sqrt d*(1/2))^q/q+2*cubeRoundingConstant d q
  let E : CountingConfiguration d → ℝ := fun η =>
    Riesz.Analysis.signedDiscrepancyEnergy q (negativeR1ScaledInput d χ h (m : ℝ) hmR η)
  let E0 : Measure (Rd d) → ℝ := fun μ => E (countingOfSimple d μ)
  have hs : -2 < -q := neg_lt_neg hqTwo
  have hφ : ∀ x, 0 ≤ φ x := angularScaledCompactWindow_nonneg d χ hχ _ hmR
  have hF : Measurable F := measurable_countStratumRoundedOutput d m k R φ Hm
    hi.cutoff_measurable hi.correction_measurable
  letI : IsFiniteMeasure A := cubeGoodRoundedLaw_isFiniteMeasure d m k R φ Hm
    hi.cutoff_measurable hi.correction_measurable δ H P
  have hclass := cubeGoodRoundedLaw_class d m k hd R (zero_lt_one.trans_le hR)
    hsize φ Hm δ H hi P hP
  have hAi := (cube_fixed_count_D_q_integrable_and_bounds d m q L hq hqTwo
    hdiam A (hclass.mono (fun _ h => h.2))).1
  have hmapF : MeasurePreserving F ((P.restrict G).prod Z) A := ⟨hF, rfl⟩
  have hJoint := hmapF.integrable_comp_of_integrable hAi
  have hcount : MeasurePreserving (countingOfSimple d) P (countingLawOfSimple d P) :=
    ⟨measurable_countingOfSimple d, rfl⟩
  have hEi : Integrable E (countingLawOfSimple d P) :=
    (negativeR1ScaledInput_energy_finite_and_real d hd q hq hs P hP hW
      χ h hχ hh hχsm hhsm hhmass (m : ℝ) hmR).2.1
  have hE0i : Integrable E0 P := hcount.integrable_comp_of_integrable hEi
  have hE0nonneg : 0 ≤ᵐ[P] E0 := Eventually.of_forall (fun μ =>
    negativeR1ScaledInput_energy_nonneg d q hq hqTwo χ h hχ hh hhmass
      (m : ℝ) hmR (countingOfSimple d μ))
  have hEmean : (∫ μ, E0 μ ∂P) = ∫ η, E η ∂countingLawOfSimple d P := by
    exact (integral_map hcount.measurable.aemeasurable hEi.aestronglyMeasurable).symm
  have hvar := negativeR1ScaledInput_mass_variance_real d hd q hq hs P hP hW χ (m : ℝ) hmR
  have hVarCount : Integrable (fun η : CountingConfiguration d =>
      ((∫ x, φ x ∂η.val)-(∫ x, φ x ∂volume))^2) (countingLawOfSimple d P) := hvar.1
  have hVarAmbient := hcount.integrable_comp_of_integrable hVarCount
  have hD2 : Integrable (fun μ => (cubeCutoffDiscrepancy d m φ μ)^2) P := by
    apply hVarAmbient.congr
    filter_upwards [hP.2.1] with μ hμ
    have he := cubeCutoffDiscrepancy_eq_compact d m φ hφ hφs (countingOfSimple d μ)
    rw [countingOfSimple_val d μ hμ] at he
    simpa only [Function.comp_def, countingOfSimple_val d μ hμ] using
      congrArg (fun r : ℝ => r^2) he.symm
  obtain ⟨hBi, hBudget⟩ := cubeGoodRoundingBudget_bound d m φ Hm δ H hi P hP hD2
  have hG : MeasurableSet G := measurableSet_cubeRepairGoodEvent d m φ hi.cutoff_measurable δ H
  have hg : P.real G ≤ 1 := by
    simpa only [probReal_univ] using measureReal_mono (μ := P) (Set.subset_univ G)
  have hqd : q < (d : ℝ) := hqTwo.trans_le (by exact_mod_cast hd)
  have hc : 0 ≤ c := add_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)) hq.le)
    (mul_nonneg (by norm_num) (cubeRoundingConstant_pos d q hq hqd).le)
  have hτi : 0 ≤ 1+τ⁻¹ := by positivity
  have hRpow : 0 ≤ R^q := Real.rpow_nonneg (zero_le_one.trans hR) _
  have hVR : 0 ≤ V*R^(q-(d : ℝ)) :=
    mul_nonneg (pow_nonneg hmR.le d) (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hpoint : (fun μ => ∫ z, D_q d q m (F (μ,z)) ∂Z) ≤ᵐ[P.restrict G]
      (fun μ => (1+τ)*E0 μ+(1+τ⁻¹)*c*(R^q*B μ+V*R^(q-(d : ℝ)))) := by
    filter_upwards [ae_restrict_of_ae hP.2.1, ae_restrict_mem hG] with μ hμ hgood
    let a := windowInputCount d (cube d (m : ℝ)) μ
    let x := windowLabel d a (μ.restrict (cube d (m : ℝ)))
    have hl := window_selected_bounded_label_spec d μ hμ (cube d (m : ℝ))
      (measurableSet_cube d _) (cube_isBounded d _)
    have hb := (randomRepairedHalfUnitBranch_expected_D_q_le d m a k hd R q τ hR
      hq hqTwo hτ hsize φ Hm δ H hi μ hgood x hl.1 hl.2.1).2
    have he : Riesz.Analysis.signedDiscrepancyEnergy q
        ((cubeLabeledRepairedInput d m a φ Hm μ x : Measure (Rd d)).toSignedMeasure -
          (volume.restrict (cube d (m : ℝ))).toSignedMeasure) = E0 μ := by
      have hη := countingOfSimple_val d μ hμ
      have hsid := cubeLabeledRepairedInput_compact_signed_identity d m a φ Hm δ H hi
        hφs hHs (countingOfSimple d μ) (by simpa only [hη] using hgood) x
        (by simpa only [hη] using hl.2.1)
      have hIn : cubeLabeledRepairedInput d m a φ Hm μ x =
          cubeLabeledRepairedInput d m a φ Hm (countingOfSimple d μ).val x :=
        congrArg (fun ν => cubeLabeledRepairedInput d m a φ Hm ν x) hη.symm
      rw [hIn, hsid]
      have hD := cubeCutoffDiscrepancy_eq_compact d m φ hφ hφs (countingOfSimple d μ)
      rw [hD]
      rfl
    have hB := cubeRoundingBudget_eq_volume_sub_squareMass d m a φ Hm δ H hi μ hgood x hl.2.1
    simpa only [he, hB, F, countStratumRoundedOutput, B, c, V, mul_assoc] using hb
  have hUpperI : Integrable (fun μ => (1+τ)*E0 μ+
      (1+τ⁻¹)*c*(R^q*B μ+V*R^(q-(d : ℝ)))) (P.restrict G) :=
    (hE0i.integrableOn.const_mul (1+τ)).add
      (((hBi.integrableOn.const_mul (R^q)).add (integrable_const _)).const_mul ((1+τ⁻¹)*c))
  have hAve := integral_mono_ae hJoint.integral_prod_left hUpperI hpoint
  have hCost : (∫ μ, D_q d q m μ ∂A) =
      ∫ μ in G, ∫ z, D_q d q m (F (μ,z)) ∂Z ∂P := by
    rw [show A = ((P.restrict G).prod Z).map F from rfl,
      integral_map hF.aemeasurable hAi.aestronglyMeasurable]
    exact integral_prod _ hJoint
  have hgoodE : (∫ μ in G, E0 μ ∂P) ≤ ∫ η, E η ∂countingLawOfSimple d P := by
    rw [← hEmean]
    exact setIntegral_le_integral hE0i hE0nonneg
  have hRounding : (∫ μ in G, R^q*B μ+V*R^(q-(d : ℝ)) ∂P) ≤
      R^q*(V-(∫ x in cube d (m : ℝ), (φ x)^2 ∂volume)+M/T)+V*R^(q-(d : ℝ)) := by
    rw [integral_add (hBi.integrableOn.const_mul (R^q)) (integrable_const _),
      integral_const_mul, integral_const]
    simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    change R^q*(∫ μ in G, B μ ∂P)+P.real G*(V*R^(q-(d : ℝ))) ≤ _
    exact add_le_add (mul_le_mul_of_nonneg_left hBudget hRpow)
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hg hVR)
  refine ⟨hAi, ?_⟩
  rw [hCost]
  calc
    _ ≤ ∫ μ in G, (1+τ)*E0 μ+(1+τ⁻¹)*c*(R^q*B μ+V*R^(q-(d : ℝ))) ∂P := hAve
    _ = (1+τ)*(∫ μ in G, E0 μ ∂P)+
        (1+τ⁻¹)*c*(∫ μ in G, R^q*B μ+V*R^(q-(d : ℝ)) ∂P) := by
      have hRBI : Integrable (fun μ => R^q*B μ+V*R^(q-(d : ℝ))) (P.restrict G) :=
        (hBi.integrableOn.const_mul (R^q)).add (integrable_const _)
      rw [integral_add (hE0i.integrableOn.const_mul (1+τ))
        (hRBI.const_mul ((1+τ⁻¹)*c)), integral_const_mul, integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hgoodE (by positivity))
      (mul_le_mul_of_nonneg_left hRounding (mul_nonneg hτi hc))

theorem cubeGoodResidualWeight_eq_and_bound
    (d m k : ℕ) (hd : 2 ≤ d)
    (R : ℝ) (hR : 0 < R) (hsize : (m : ℝ) = (2 : ℝ)^k*R)
    (χ h : Rd d → ℝ) (δ H : ℝ)
    (hi : CubeRepairInputHypotheses d m χ h δ H)
    (P : ConfigurationLaw d) (hP : Admissible d P)
    (hD2 : Integrable (fun μ => (cubeCutoffDiscrepancy d m χ μ)^2) P) :
    let G := cubeRepairGoodEvent d m χ δ H
    let V : ℝ := (m : ℝ)^d
    let M : ℝ := ∫ μ, (cubeCutoffDiscrepancy d m χ μ)^2 ∂P
    let ε : ℝ := H*|∫ μ in G, cubeCutoffDiscrepancy d m χ μ ∂P|/V
    let θ : ℝ≥0∞ := (1+ENNReal.ofReal ε)⁻¹
    let ν := cubeGoodRoundedMean d m k R χ h δ H P
    let η := volume.restrict (cube d (m : ℝ))-θ•ν
    let r : ℝ≥0∞ := η Set.univ*((m^d : ℕ) : ℝ≥0∞)⁻¹
    r.toReal = (ε+P.real Gᶜ)/(1+ε) ∧
      r.toReal ≤ (2*H^2/δ+4*H^2/δ^2)*M/V^2 := by
  dsimp only
  letI := hP.1
  let C := cube d (m : ℝ)
  let G := cubeRepairGoodEvent d m χ δ H
  let V : ℝ := (m : ℝ)^d
  let N : ℝ≥0∞ := (m^d : ℕ)
  let D := cubeCutoffDiscrepancy d m χ
  let M : ℝ := ∫ μ, (D μ)^2 ∂P
  let ε : ℝ := H*|∫ μ in G, D μ ∂P|/V
  let θ : ℝ≥0∞ := (1+ENNReal.ofReal ε)⁻¹
  let ν := cubeGoodRoundedMean d m k R χ h δ H P
  let ρ : Measure (Rd d) := volume.restrict C
  let η := ρ-θ•ν
  let r : ℝ≥0∞ := η Set.univ*N⁻¹
  let T : ℝ := δ*V/(2*H)
  letI : IsFiniteMeasure ρ := cube_background_isFiniteMeasure d m
  letI : IsFiniteMeasure ν := cubeGoodRoundedMean_isFiniteMeasure d m k hd R hR hsize
    χ h δ H hi P hP
  have hV : 0 < V := pow_pos (Nat.cast_pos.mpr hi.side_pos) d
  have hε : 0 ≤ ε := div_nonneg
    (mul_nonneg hi.correction_bound_pos.le (abs_nonneg _)) hV.le
  have hOne : 0 < 1+ε := by linarith only [hε]
  have hθreal : θ.toReal = (1+ε)⁻¹ := by
    simp only [θ, ENNReal.toReal_inv, ENNReal.toReal_add ENNReal.one_ne_top
      ENNReal.ofReal_ne_top, ENNReal.toReal_one, ENNReal.toReal_ofReal hε]
  have hνmass : ν Set.univ = N*P G :=
    cubeGoodRoundedMean_mass d m k hd R hR hsize χ h δ H hi P hP
  have hρmass : ρ Set.univ = N := cube_background_mass d m
  have hνle : θ•ν ≤ ρ := cubeGoodRoundedMean_scaled_le d m k hd R hR hsize χ h δ H hi P hP
  letI : IsFiniteMeasure (θ•ν) := isFiniteMeasure_of_le ρ hνle
  letI : IsFiniteMeasure η := isFiniteMeasure_of_le ρ Measure.sub_le
  have hηmass : η Set.univ = ρ Set.univ-(θ•ν) Set.univ :=
    Measure.sub_apply MeasurableSet.univ hνle
  have hηreal : (η Set.univ).toReal = V-(1+ε)⁻¹*V*P.real G := by
    rw [hηmass, ENNReal.toReal_sub_of_le (hνle Set.univ) (measure_ne_top ρ Set.univ),
      Measure.smul_apply, smul_eq_mul, hνmass, hρmass,
      ENNReal.toReal_mul, ENNReal.toReal_mul, hθreal]
    simp only [N, ENNReal.toReal_pow, ENNReal.toReal_natCast, Nat.cast_pow, measureReal_def, V]
    ring
  have hr : r.toReal = 1-P.real G/(1+ε) := by
    rw [show r = η Set.univ*N⁻¹ from rfl, ENNReal.toReal_mul, ENNReal.toReal_inv, hηreal]
    simp only [N, ENNReal.toReal_pow, ENNReal.toReal_natCast, Nat.cast_pow]
    change (V-(1+ε)⁻¹*V*P.real G)*V⁻¹ = 1-P.real G/(1+ε)
    field_simp [hV.ne', hOne.ne']
  have hG : MeasurableSet G := measurableSet_cubeRepairGoodEvent d m χ hi.cutoff_measurable δ H
  have hprob : P.real G+P.real Gᶜ = 1 := by
    simpa only [probReal_univ] using measureReal_add_measureReal_compl (μ := P) hG
  have hrformula : r.toReal = (ε+P.real Gᶜ)/(1+ε) := by
    rw [hr]
    field_simp [hOne.ne']
    linarith only [hprob]
  have hrle : r.toReal ≤ ε+P.real Gᶜ := by
    rw [hrformula]
    apply (div_le_iff₀ hOne).2
    have hnum : 0 ≤ ε+P.real Gᶜ := add_nonneg hε measureReal_nonneg
    nlinarith only [mul_nonneg hnum hε]
  have hT : 0 < T := div_pos (mul_pos hi.slack_pos hV)
    (mul_pos (by norm_num) hi.correction_bound_pos)
  have hDmean := cubeCutoffDiscrepancy_integrable_and_mean_zero d m χ h δ H hi P hP
  have htail := square_tail_mass_and_mean_bounds P D
    (measurable_cubeCutoffDiscrepancy d m χ hi.cutoff_measurable)
    hDmean.1 hD2 hDmean.2 T hT
  have hbad : {μ | T < |D μ|} = Gᶜ := by
    ext μ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, G, cubeRepairGoodEvent,
      not_le, T, V, D]
  dsimp only at htail
  rw [hbad, compl_compl] at htail
  have hεbound : ε ≤ 2*H^2*M/(δ*V^2) := by
    calc
      _ ≤ H*(M/T)/V := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htail.2.2 hi.correction_bound_pos.le) hV.le
      _ = _ := by
        dsimp only [T]
        field_simp [hV.ne', hi.slack_pos.ne', hi.correction_bound_pos.ne']
  have hpbound : P.real Gᶜ ≤ 4*H^2*M/(δ^2*V^2) := by
    calc
      _ ≤ M/T^2 := htail.1
      _ = _ := by
        dsimp only [T]
        field_simp [hV.ne', hi.slack_pos.ne', hi.correction_bound_pos.ne']
        ring
  refine ⟨hrformula, hrle.trans ?_⟩
  change ε+P.real Gᶜ ≤ (2*H^2/δ+4*H^2/δ^2)*M/V^2
  calc
    _ ≤ 2*H^2*M/(δ*V^2)+4*H^2*M/(δ^2*V^2) := add_le_add hεbound hpbound
    _ = _ := by
      field_simp [hV.ne', hi.slack_pos.ne']


theorem exists_cubeRepair_smooth_base (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (χ h : C_c(Rd d, ℝ)) (δ H : ℝ),
      ContDiff ℝ ∞ χ ∧ ContDiff ℝ ∞ h ∧ 0 < δ ∧ δ < 1 ∧ 0 < H ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1-δ) ∧ (∀ x, 0 ≤ h x ∧ h x ≤ H) ∧
      (∫ x : Rd d, h x) = 1 ∧ tsupport χ ⊆ cube d 1 ∧ tsupport h ⊆ cube d 1 ∧
      1-ε < (∫ x : Rd d, (χ x)^2) ∧ (∫ x : Rd d, (χ x)^2) ≤ 1 := by
  obtain ⟨ψ, hψsm, hψ, hψsupp, hψpos, hψnear, hψone⟩ :=
    exists_nearIndicator_smooth_cube_window d (ε/4) (by positivity)
  let δ : ℝ := min (ε/8) (1/4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδquarter : δ ≤ 1/4 := min_le_right _ _
  have hδε : δ ≤ ε/8 := min_le_left _ _
  have hδone : δ < 1 := lt_of_le_of_lt hδquarter (by norm_num)
  let I : ℝ := ∫ x : Rd d, ψ x
  have hψsqI : Integrable (fun x : Rd d => (ψ x)^2) volume :=
    Continuous.integrable_of_hasCompactSupport (ψ.continuous.pow 2)
      (ψ.hasCompactSupport.comp_left (g := fun t : ℝ => t^2) (by norm_num))
  have hI : 0 < I := hψpos.trans_le
    (integral_mono hψsqI ψ.integrable (fun x => by
      obtain ⟨h0,h1⟩ := hψ x
      nlinarith only [h0,h1]))
  let χ : C_c(Rd d, ℝ) := (1-δ) • ψ
  let h : C_c(Rd d, ℝ) := I⁻¹ • ψ
  let H : ℝ := I⁻¹
  have hχ (x : Rd d) : 0 ≤ χ x ∧ χ x ≤ 1-δ := by
    change 0 ≤ (1-δ)*ψ x ∧ (1-δ)*ψ x ≤ 1-δ
    exact ⟨mul_nonneg (sub_nonneg.mpr hδone.le) (hψ x).1,
      by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hψ x).2 (sub_nonneg.mpr hδone.le)⟩
  have hh (x : Rd d) : 0 ≤ h x ∧ h x ≤ H := by
    change 0 ≤ I⁻¹*ψ x ∧ I⁻¹*ψ x ≤ I⁻¹
    exact ⟨mul_nonneg (inv_nonneg.mpr hI.le) (hψ x).1,
      by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hψ x).2 (inv_nonneg.mpr hI.le)⟩
  have hmass : (∫ x : Rd d, h x) = 1 := by
    change (∫ x : Rd d, I⁻¹*ψ x) = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hI.ne'
  have hχsupp : tsupport χ ⊆ cube d 1 :=
    (tsupport_smul_subset_right (fun _ : Rd d => (1-δ)) (ψ : Rd d → ℝ)).trans hψsupp
  have hhsupp : tsupport h ⊆ cube d 1 :=
    (tsupport_smul_subset_right (fun _ : Rd d => I⁻¹) (ψ : Rd d → ℝ)).trans hψsupp
  have hχmass : (∫ x : Rd d, (χ x)^2) =
      (1-δ)^2*(∫ x : Rd d, (ψ x)^2) := by
    change (∫ x : Rd d, ((1-δ)*ψ x)^2) = _
    simp only [mul_pow]
    exact integral_const_mul _ _
  have hsqlo : (∫ x : Rd d, (ψ x)^2)-2*δ ≤ (∫ x : Rd d, (χ x)^2) := by
    rw [hχmass]
    have h1 := mul_nonneg (sub_nonneg.mpr hψone) hδ.le
    have h2 : 0 ≤ δ^2*(∫ x : Rd d, (ψ x)^2 ∂volume) :=
      mul_nonneg (sq_nonneg δ) (integral_nonneg (fun x : Rd d => sq_nonneg (ψ x)))
    nlinarith only [h1,h2]
  have hnear : 1-ε < (∫ x : Rd d, (χ x)^2) := by
    linarith only [hψnear, hδε, hsqlo, hε]
  have hmassone : (∫ x : Rd d, (χ x)^2) ≤ 1 := by
    rw [hχmass]
    have hfactor : 0 ≤ (1-δ)^2 ∧ (1-δ)^2 ≤ 1 := by
      exact ⟨sq_nonneg _, by nlinarith only [hδ.le,hδone.le]⟩
    exact (mul_le_mul_of_nonneg_left hψone hfactor.1).trans
      (by simpa only [mul_one] using hfactor.2)
  have hχsm : ContDiff ℝ ∞ (χ : Rd d → ℝ) := by
    change ContDiff ℝ ∞ (fun x : Rd d => (1-δ) • ψ x)
    exact hψsm.const_smul (1-δ)
  have hhsm : ContDiff ℝ ∞ (h : Rd d → ℝ) := by
    change ContDiff ℝ ∞ (fun x : Rd d => I⁻¹ • ψ x)
    exact hψsm.const_smul I⁻¹
  exact ⟨χ,h,δ,H,hχsm,hhsm,hδ,hδone,
    inv_pos.mpr hI,hχ,hh,hmass,hχsupp,hhsupp,hnear,hmassone⟩

private theorem scaledCompactWindow_tsupport_subset_cube
    (d : ℕ) (ψ : C_c(Rd d, ℝ)) (hs : tsupport ψ ⊆ cube d 1)
    (L : ℝ) (hL : 0 < L) :
    tsupport (angularScaledCompactWindow d ψ L hL) ⊆ cube d L := by
  let K : Set (Rd d) := (fun x : Rd d => L • x) '' tsupport ψ
  have hK : IsCompact K := ψ.hasCompactSupport.image (continuous_const_smul L)
  have hsK : Function.support (angularScaledCompactWindow d ψ L hL : Rd d → ℝ) ⊆ K := by
    intro x hx
    refine ⟨L⁻¹ • x, subset_tsupport ψ (show ψ (L⁻¹ • x) ≠ 0 from hx), ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hts : tsupport (angularScaledCompactWindow d ψ L hL) ⊆ K :=
    closure_minimal hsK hK.isClosed
  apply hts.trans
  rintro x ⟨y,hy,rfl⟩
  intro i
  obtain ⟨hy0,hy1⟩ := hs hy i
  change 0 ≤ L*y i ∧ L*y i < L
  refine ⟨mul_nonneg hL.le hy0, ?_⟩
  simpa only [mul_one] using mul_lt_mul_of_pos_left hy1 hL

theorem cubeRepairInputHypotheses_scaled
    (d m : ℕ) (hm : 0 < m) (χ h : C_c(Rd d, ℝ)) (δ H : ℝ)
    (hδ : 0 < δ) (hδone : δ < 1) (hH : 0 < H)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1-δ)
    (hh : ∀ x, 0 ≤ h x ∧ h x ≤ H) (hmass : (∫ x : Rd d, h x) = 1)
    (hhsupp : tsupport h ⊆ cube d 1) :
    CubeRepairInputHypotheses d m
      (fun x => χ ((m : ℝ)⁻¹ • x))
      (fun x => ((m : ℝ)^d)⁻¹*h ((m : ℝ)⁻¹ • x)) δ H := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hV : 0 < (m : ℝ)^d := pow_pos hmR d
  refine ⟨hm, χ.continuous.measurable.comp (measurable_const_smul _),
    measurable_const.mul (h.continuous.measurable.comp (measurable_const_smul _)),
    hδ,hδone,hH,fun x _ => hχ _,?_,?_⟩
  · intro x _
    refine ⟨mul_nonneg (inv_nonneg.mpr hV.le) (hh _).1, ?_⟩
    calc
      _ ≤ ((m : ℝ)^d)⁻¹*H := mul_le_mul_of_nonneg_left (hh _).2 (inv_nonneg.mpr hV.le)
      _ = H/(m : ℝ)^d := by ring
  · have hscale : (∫ x : Rd d, h ((m : ℝ)⁻¹ • x)) =
        (m : ℝ)^d*(∫ x : Rd d, h x) := by
      simpa only [Rd,finrank_euclideanSpace_fin,smul_eq_mul] using
        Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Rd d)) h hmR.le
    have hts : tsupport (fun x : Rd d => ((m : ℝ)^d)⁻¹*h ((m : ℝ)⁻¹ • x)) ⊆
        cube d (m : ℝ) :=
      (tsupport_smul_subset_right (fun _ : Rd d => ((m : ℝ)^d)⁻¹)
        (fun x : Rd d => h ((m : ℝ)⁻¹ • x))).trans
        (scaledCompactWindow_tsupport_subset_cube d h hhsupp (m : ℝ) hmR)
    have hsupport := (subset_tsupport (fun x : Rd d =>
      ((m : ℝ)^d)⁻¹*h ((m : ℝ)⁻¹ • x))).trans hts
    rw [← integral_indicator (measurableSet_cube d _),
      Set.indicator_eq_self.mpr hsupport, integral_const_mul, hscale, hmass, mul_one]
    exact inv_mul_cancel₀ hV.ne'

theorem cubeScaledCutoff_square_mass
    (d m : ℕ) (hm : 0 < m) (χ : C_c(Rd d, ℝ))
    (hχsupp : tsupport χ ⊆ cube d 1) :
    ((m : ℝ)^d)⁻¹*(∫ x in cube d (m : ℝ), (χ ((m : ℝ)⁻¹ • x))^2 ∂volume) =
      ∫ x : Rd d, (χ x)^2 := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hts := scaledCompactWindow_tsupport_subset_cube d χ hχsupp (m : ℝ) hmR
  have hs : Function.support (fun x : Rd d => (χ ((m : ℝ)⁻¹ • x))^2) ⊆
      cube d (m : ℝ) := by
    intro x hx
    apply hts
    apply subset_tsupport (angularScaledCompactWindow d χ (m : ℝ) hmR)
    intro hzero
    change χ ((m : ℝ)⁻¹ • x) = 0 at hzero
    exact hx (by simp only [hzero, zero_pow two_ne_zero])
  have hscale : (∫ x : Rd d, (χ ((m : ℝ)⁻¹ • x))^2) =
      (m : ℝ)^d*(∫ x : Rd d, (χ x)^2) := by
    simpa only [Rd,finrank_euclideanSpace_fin,smul_eq_mul] using
      Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Rd d))
        (fun x : Rd d => (χ x)^2) hmR.le
  rw [← integral_indicator (measurableSet_cube d _), Set.indicator_eq_self.mpr hs, hscale]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hmR.ne'), one_mul]

theorem cubeDyadicSide_tendsto (R : ℕ) (hR : 1 ≤ R) :
    Tendsto (fun k : ℕ => 2^k*R) atTop atTop := by
  have hp : Tendsto (fun k : ℕ => (2 : ℕ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  apply tendsto_atTop_mono _ hp
  intro k
  exact le_mul_of_one_le_right (Nat.zero_le _) hR

theorem cubeDyadicSide_real_geometry (R k : ℕ) :
    ((2^k*R : ℕ) : ℝ) = (2 : ℝ)^k*(R : ℝ) := by
  push_cast
  rfl


private theorem cubeScaledCutoff_variance_transfer
    (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (χ : C_c(Rd d, ℝ)) (hχ : ∀ x, 0 ≤ χ x) (hχs : tsupport χ ⊆ cube d 1) :
    let hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    let φ := angularScaledCompactWindow d χ (m : ℝ) hmR
    Integrable (fun μ => (cubeCutoffDiscrepancy d m φ μ)^2) P ∧
      (∫ μ, (cubeCutoffDiscrepancy d m φ μ)^2 ∂P) =
        ∫ η : CountingConfiguration d,
          ((∫ x, φ x ∂η.val)-(∫ x, φ x ∂volume))^2 ∂countingLawOfSimple d P := by
  dsimp only
  let φ := angularScaledCompactWindow d χ (m : ℝ) (Nat.cast_pos.mpr hm)
  let f : CountingConfiguration d → ℝ := fun η =>
    ((∫ x, φ x ∂η.val)-(∫ x, φ x ∂volume))^2
  have hi : Integrable f (countingLawOfSimple d P) :=
    (negativeR1ScaledInput_mass_variance_real d hd q hq (neg_lt_neg hqTwo)
      P hP hW χ (m : ℝ) (Nat.cast_pos.mpr hm)).1
  have hmap : MeasurePreserving (countingOfSimple d) P (countingLawOfSimple d P) :=
    ⟨measurable_countingOfSimple d,rfl⟩
  have heq : (fun μ => f (countingOfSimple d μ)) =ᵐ[P]
      (fun μ => (cubeCutoffDiscrepancy d m φ μ)^2) := by
    filter_upwards [hP.2.1] with μ hμ
    have he := cubeCutoffDiscrepancy_eq_compact d m φ
      (angularScaledCompactWindow_nonneg d χ hχ _ _)
      (scaledCompactWindow_tsupport_subset_cube d χ hχs _ _) (countingOfSimple d μ)
    rw [countingOfSimple_val d μ hμ] at he
    simpa only [f, countingOfSimple_val d μ hμ] using
      congrArg (fun r : ℝ => r^2) he.symm
  exact ⟨(hmap.integrable_comp_of_integrable hi).congr heq,
    (integral_congr_ae heq).symm.trans
      (integral_map hmap.measurable.aemeasurable hi.aestronglyMeasurable).symm⟩

private theorem reverseCube_diameter (d m : ℕ) (hm : 0 < m)
    (x : Rd d) (hx : x ∈ cube d (m : ℝ))
    (y : Rd d) (hy : y ∈ cube d (m : ℝ)) :
    ‖x-y‖ ≤ Real.sqrt d*(m : ℝ) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hc (i : Fin d) : |x i-y i| ≤ (m : ℝ) :=
    abs_le.mpr ⟨by linarith [(hx i).1,(hy i).2], by linarith [(hy i).1,(hx i).2]⟩
  have hsquare : ‖x-y‖^2 ≤ (d : ℝ)*(m : ℝ)^2 := by
    calc
      _ = ∑ i : Fin d, (x i-y i)^2 := EuclideanSpace.real_norm_sq_eq (x-y)
      _ ≤ ∑ _i : Fin d, (m : ℝ)^2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hmR.le).2 (hc i))
      _ = _ := by simp
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hmR.le)).mp
    (by simpa only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg d)] using hsquare)

private theorem original_finite_negative_W_nonneg
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤) :
    0 ≤ (W d (-q) P).toReal := by
  have hc := negative_constant_finiteness_and_sign d hd (-q)
    (neg_lt_neg hqTwo) (neg_lt_zero.mpr hq)
  have hbot : W d (-q) P ≠ ⊥ :=
    ne_of_gt ((EReal.bot_lt_coe (c0 d (-q))).trans_le (c0_le_W d (-q) P))
  have hlow : (e d (-q) : EReal) ≤ W d (-q) P := by
    rw [← hc.1]
    exact sInf_le ⟨P,hP,rfl⟩
  have he : e d (-q) ≤ (W d (-q) P).toReal := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [EReal.coe_toReal hW hbot] using hlow
  exact hc.2.1.le.trans he

/-- This is a bound by an actual constructed balanced law, not a balanced-law
or energy premise. The only cutoff hypotheses are structural base data. -/
private theorem balanced_density_inf_le_actual_dyadic_budget
    (d m k : ℕ) (hd : 2 ≤ d) (hm : 0 < m)
    (R q τ : ℝ) (hR : 1 ≤ R) (hq : 0 < q) (hqTwo : q < 2) (hτ : 0 < τ)
    (hsize : (m : ℝ) = (2 : ℝ)^k*R)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (χ h : C_c(Rd d, ℝ)) (δ H : ℝ)
    (hχsm : ContDiff ℝ ∞ χ) (hhsm : ContDiff ℝ ∞ h)
    (hδ : 0 < δ) (hδone : δ < 1) (hH : 0 < H)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1-δ)
    (hh : ∀ x, 0 ≤ h x ∧ h x ≤ H) (hmass : (∫ x : Rd d, h x) = 1)
    (hχs : tsupport χ ⊆ cube d 1) (hhs : tsupport h ⊆ cube d 1) :
    let hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    let φ := angularScaledCompactWindow d χ (m : ℝ) hmR
    let V : ℝ := (m : ℝ)^d
    let M : ℝ := ∫ μ, (cubeCutoffDiscrepancy d m φ μ)^2 ∂P
    let T : ℝ := δ*V/(2*H)
    let a : ℝ := ∫ x : Rd d, (χ x)^2
    let c : ℝ := 8*(Real.sqrt d*(1/2))^q/q+2*cubeRoundingConstant d q
    let K : ℝ := 2*H^2/δ+4*H^2/δ^2
    sInf (balancedDensityValues d q) ≤
      (1+τ)*(V⁻¹*∫ η : CountingConfiguration d,
        Riesz.Analysis.signedDiscrepancyEnergy q
          (negativeR1ScaledInput d χ h (m : ℝ) hmR η) ∂countingLawOfSimple d P) +
      (1+τ⁻¹)*c*(R^q*(1-a+M/(T*V))+R^(q-(d : ℝ))) +
      (2*(Real.sqrt d)^q/q)*K*(M/(m : ℝ)^((d : ℝ)-q)) := by
  dsimp only
  letI := hP.1
  have hdpos : 0 < d := Nat.lt_of_lt_of_le (by decide) hd
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  let φ := angularScaledCompactWindow d χ (m : ℝ) hmR
  let Hm : C_c(Rd d, ℝ) := ((m : ℝ)^d)⁻¹ • angularScaledCompactWindow d h (m : ℝ) hmR
  let V : ℝ := (m : ℝ)^d
  let M : ℝ := ∫ μ, (cubeCutoffDiscrepancy d m φ μ)^2 ∂P
  let T : ℝ := δ*V/(2*H)
  let a : ℝ := ∫ x : Rd d, (χ x)^2
  let c : ℝ := 8*(Real.sqrt d*(1/2))^q/q+2*cubeRoundingConstant d q
  let K : ℝ := 2*H^2/δ+4*H^2/δ^2
  let Cfall : ℝ := 2*(Real.sqrt d)^q/q
  let G := cubeRepairGoodEvent d m φ δ H
  let ε : ℝ := H*|∫ μ in G, cubeCutoffDiscrepancy d m φ μ ∂P|/V
  let θ : ℝ≥0∞ := (1+ENNReal.ofReal ε)⁻¹
  let A := cubeGoodRoundedLaw d m k R φ Hm δ H P
  let ν := cubeGoodRoundedMean d m k R φ Hm δ H P
  let η : Measure (Rd d) := volume.restrict (cube d (m : ℝ))-θ•ν
  let r : ℝ≥0∞ := η Set.univ*((m^d : ℕ) : ℝ≥0∞)⁻¹
  let Pimix := cubeResidualIIDMixture d m A θ ν
  have hi := cubeRepairInputHypotheses_scaled d m hm χ h δ H
    hδ hδone hH hχ hh hmass hhs
  have hφs : tsupport φ ⊆ cube d (m : ℝ) :=
    scaledCompactWindow_tsupport_subset_cube d χ hχs _ hmR
  have hHms : tsupport (Hm : Rd d → ℝ) ⊆ cube d (m : ℝ) :=
    (tsupport_smul_subset_right (fun _ : Rd d => ((m : ℝ)^d)⁻¹)
      (angularScaledCompactWindow d h (m : ℝ) hmR : Rd d → ℝ)).trans
      (scaledCompactWindow_tsupport_subset_cube d h hhs _ hmR)
  letI : IsFiniteMeasure A := cubeGoodRoundedLaw_isFiniteMeasure d m k R φ Hm
    hi.cutoff_measurable hi.correction_measurable δ H P
  have hclass := cubeGoodRoundedLaw_class d m k hd R (zero_lt_one.trans_le hR)
    hsize φ Hm δ H hi P hP
  have hdom : θ•ν ≤ volume.restrict (cube d (m : ℝ)) :=
    cubeGoodRoundedMean_scaled_le d m k hd R (zero_lt_one.trans_le hR)
      hsize φ Hm δ H hi P hP
  have hPimix : BalancedAdmissible d m Pimix := cubeResidualIIDMixture_balanced
    d m hdpos hm A hclass ν
    (fun E hE => (cubeGoodRoundedMean_apply d m k R φ Hm δ H P E hE).symm)
    θ hdom
  have hθ : θ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by
    exact ne_of_gt (zero_lt_one.trans_le (le_self_add : (1 : ℝ≥0∞) ≤ 1+ENNReal.ofReal ε)))
  have hθone : θ.toReal ≤ 1 := by
    have ht : θ ≤ 1 := ENNReal.inv_le_one.mpr (by exact le_self_add)
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top ht
  have hdiam := reverseCube_diameter d m hm
  have hmix := cubeResidualIIDMixture_expected_energy_le d m hdpos hm q
    (Real.sqrt d*(m : ℝ)) hq hqTwo hdiam A hclass ν θ hθ
  have hAi := cube_fixed_count_D_q_integrable_and_bounds d m q
    (Real.sqrt d*(m : ℝ)) hq hqTwo hdiam A (hclass.mono (fun _ t => t.2))
  have hEA : 0 ≤ ∫ μ, D_q d q m μ ∂A :=
    integral_nonneg_of_ae (hAi.2.mono (fun _ t => t.1))
  have hgood := (cubeGoodRoundedLaw_expected_D_q_le d m k hd hm R q τ hR hq
    hqTwo hτ hsize P hP hW χ h (fun x => (hχ x).1) (fun x => (hh x).1)
    hχsm hhsm hmass δ H hi hφs hHms (Real.sqrt d*(m : ℝ)) hdiam).2
  have hD2 := (cubeScaledCutoff_variance_transfer d m hd hm q hq hqTwo P hP hW
    χ (fun x => (hχ x).1) hχs).1
  have hr := (cubeGoodResidualWeight_eq_and_bound d m k hd R
    (zero_lt_one.trans_le hR) hsize φ Hm δ H hi P hP hD2).2
  have hV : 0 < V := pow_pos hmR d
  have hQ : 0 < (m : ℝ)^((d : ℝ)-q) := Real.rpow_pos_of_pos hmR _
  have hT : 0 < T := div_pos (mul_pos hδ hV) (mul_pos (by norm_num) hH)
  have hFall0 : 0 ≤ 2*(Real.sqrt d*(m : ℝ))^q*((m^d : ℕ) : ℝ)^2/q := by positivity
  have hpow : (m : ℝ)^q*(m : ℝ)^((d : ℝ)-q) = V := by
    rw [← Real.rpow_add hmR]
    have he : q+((d : ℝ)-q) = (d : ℝ) := by ring
    rw [he,Real.rpow_natCast]
  have hpowq : (m : ℝ)^q = V/(m : ℝ)^((d : ℝ)-q) :=
    (eq_div_iff hQ.ne').2 hpow
  have hfallback : V⁻¹*(r.toReal*(2*(Real.sqrt d*(m : ℝ))^q*
      ((m^d : ℕ) : ℝ)^2/q)) ≤ Cfall*K*(M/(m : ℝ)^((d : ℝ)-q)) := by
    calc
      _ ≤ V⁻¹*((K*M/V^2)*(2*(Real.sqrt d*(m : ℝ))^q*
          ((m^d : ℕ) : ℝ)^2/q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr hFall0)
          (inv_nonneg.mpr hV.le)
      _ = _ := by
        rw [Real.mul_rpow (Real.sqrt_nonneg _) hmR.le, hpowq]
        simp only [Nat.cast_pow]
        change V⁻¹*((K*M/V^2)*(2*((Real.sqrt d)^q*(V/(m : ℝ)^((d : ℝ)-q)))*V^2/q)) = _
        dsimp only [Cfall]
        field_simp [hV.ne',hQ.ne',hq.ne']
  have hS : (∫ x in cube d (m : ℝ), (φ x)^2 ∂volume) = V*a := by
    have hs := cubeScaledCutoff_square_mass d m hm χ hχs
    change V⁻¹*(∫ x in cube d (m : ℝ), (φ x)^2 ∂volume) = a at hs
    have ht := congrArg (fun z : ℝ => V*z) hs
    simpa only [← mul_assoc,mul_inv_cancel₀ hV.ne',one_mul] using ht
  have hnormalize : V⁻¹*(R^q*(V-(∫ x in cube d (m : ℝ), (φ x)^2 ∂volume)+M/T)+
      V*R^(q-(d : ℝ))) = R^q*(1-a+M/(T*V))+R^(q-(d : ℝ)) := by
    rw [hS]
    field_simp [hV.ne',hT.ne']
  have hstar : sInf (balancedDensityValues d q) ≤ b d q m/V :=
    csInf_le (balancedDensityValues_bddBelow d q hq hqTwo) ⟨m,Nat.succ_le_iff.mpr hm,rfl⟩
  calc
    _ ≤ b d q m/V := hstar
    _ ≤ V⁻¹*(∫ μ, D_q d q m μ ∂Pimix) := by
      simpa only [div_eq_mul_inv,mul_comm] using
        div_le_div_of_nonneg_right (b_le_expectedEnergy d m q hq hqTwo Pimix hPimix) hV.le
    _ ≤ V⁻¹*((∫ μ, D_q d q m μ ∂A)+
        r.toReal*(2*(Real.sqrt d*(m : ℝ))^q*((m^d : ℕ) : ℝ)^2/q)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hV.le)
      exact hmix.trans (add_le_add
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hθone hEA) le_rfl)
    _ = V⁻¹*(∫ μ, D_q d q m μ ∂A)+
        V⁻¹*(r.toReal*(2*(Real.sqrt d*(m : ℝ))^q*((m^d : ℕ) : ℝ)^2/q)) := mul_add _ _ _
    _ ≤ V⁻¹*((1+τ)*(∫ ξ : CountingConfiguration d,
          Riesz.Analysis.signedDiscrepancyEnergy q
            (negativeR1ScaledInput d χ h (m : ℝ) hmR ξ) ∂countingLawOfSimple d P)+
        (1+τ⁻¹)*c*(R^q*(V-(∫ x in cube d (m : ℝ),(φ x)^2 ∂volume)+M/T)+
          V*R^(q-(d : ℝ))))+Cfall*K*(M/(m : ℝ)^((d : ℝ)-q)) :=
      add_le_add (mul_le_mul_of_nonneg_left hgood (inv_nonneg.mpr hV.le)) hfallback
    _ = _ := by
      calc
        _ = (1+τ)*(V⁻¹*∫ ξ : CountingConfiguration d,
            Riesz.Analysis.signedDiscrepancyEnergy q
              (negativeR1ScaledInput d χ h (m : ℝ) hmR ξ) ∂countingLawOfSimple d P)+
          ((1+τ⁻¹)*c)*(V⁻¹*(R^q*(V-(∫ x in cube d (m : ℝ),(φ x)^2 ∂volume)+M/T)+
            V*R^(q-(d : ℝ))))+Cfall*K*(M/(m : ℝ)^((d : ℝ)-q)) := by ring
        _ = _ := by rw [hnormalize]

/-- The dyadic subsequence is used only for constructing competitors. The
already checked full cube-limit theorem is not reproved. -/
theorem balanced_density_inf_le_smooth_window_budget
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤)
    (τ : ℝ) (hτ : 0 < τ) (R : ℕ) (hR : 1 ≤ R)
    (χ h : C_c(Rd d, ℝ)) (δ H : ℝ)
    (hχsm : ContDiff ℝ ∞ χ) (hhsm : ContDiff ℝ ∞ h)
    (hδ : 0 < δ) (hδone : δ < 1) (hH : 0 < H)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1-δ)
    (hh : ∀ x, 0 ≤ h x ∧ h x ≤ H) (hmass : (∫ x : Rd d, h x) = 1)
    (hχs : tsupport χ ⊆ cube d 1) (hhs : tsupport h ⊆ cube d 1) :
    sInf (balancedDensityValues d q) ≤
      (1+τ)*(∫ x : Rd d, (χ x)^2)*(W d (-q) P).toReal +
      (1+τ⁻¹)*(8*(Real.sqrt d*(1/2))^q/q+2*cubeRoundingConstant d q)*
        ((R : ℝ)^q*(1-(∫ x : Rd d, (χ x)^2))+(R : ℝ)^(q-(d : ℝ))) := by
  let m : ℕ → ℕ := fun k => 2^k*R
  have hm (k : ℕ) : 0 < m k := Nat.mul_pos (pow_pos (by decide) k)
    (Nat.zero_lt_of_lt hR)
  let L : ℕ → ℝ := fun k => (m k : ℝ)
  have hL (k : ℕ) : 0 < L k := Nat.cast_pos.mpr (hm k)
  have hLone (k : ℕ) : 1 ≤ L k := by
    change (1 : ℝ) ≤ (m k : ℝ)
    exact_mod_cast Nat.succ_le_iff.mpr (hm k)
  have hLinf : Tendsto L atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (cubeDyadicSide_tendsto R hR)
  let V : ℕ → ℝ := fun k => L k^d
  let φ (k : ℕ) := angularScaledCompactWindow d χ (L k) (hL k)
  let M : ℕ → ℝ := fun k => ∫ μ, (cubeCutoffDiscrepancy d (m k) (φ k) μ)^2 ∂P
  let T : ℕ → ℝ := fun k => δ*V k/(2*H)
  let a : ℝ := ∫ x : Rd d, (χ x)^2
  let c : ℝ := 8*(Real.sqrt d*(1/2))^q/q+2*cubeRoundingConstant d q
  let K : ℝ := 2*H^2/δ+4*H^2/δ^2
  let Cfall : ℝ := 2*(Real.sqrt d)^q/q
  let E : ℕ → ℝ := fun k => (V k)⁻¹*∫ η : CountingConfiguration d,
    Riesz.Analysis.signedDiscrepancyEnergy q
      (negativeR1ScaledInput d χ h (L k) (hL k) η) ∂countingLawOfSimple d P
  have hR1 := negativeR1ScaledInput_energy_and_variance_tendsto d hd q hq
    (neg_lt_neg hqTwo) P hP hW χ h (fun x => (hχ x).1) (fun x => (hh x).1)
    hχsm hhsm hmass L hL hLinf
  have hE : Tendsto E atTop (𝓝 (a*(W d (-q) P).toReal)) := hR1.2.1
  have hMcount (k : ℕ) : M k = ∫ η : CountingConfiguration d,
      ((∫ x, φ k x ∂η.val)-(∫ x, φ k x ∂volume))^2 ∂countingLawOfSimple d P :=
    (cubeScaledCutoff_variance_transfer d (m k) hd (hm k) q hq hqTwo P hP hW
      χ (fun x => (hχ x).1) hχs).2
  have hMQ : Tendsto (fun k => M k/(L k)^((d : ℝ)-q)) atTop (𝓝 0) := by
    have ht := hR1.2.2.2
    change Tendsto (fun k => (L k^((d : ℝ)-q))⁻¹ *
      ∫ η : CountingConfiguration d,
        ((∫ x, φ k x ∂η.val)-(∫ x, φ k x ∂volume))^2 ∂countingLawOfSimple d P)
      atTop (𝓝 0) at ht
    apply Filter.Tendsto.congr' (h := ht)
    apply Eventually.of_forall
    intro k
    dsimp only
    rw [← hMcount k]
    ring
  have hM0 (k : ℕ) : 0 ≤ M k := integral_nonneg (fun μ => sq_nonneg _)
  have hV (k : ℕ) : 0 < V k := pow_pos (hL k) d
  have hMQ0 (k : ℕ) : 0 < (L k)^((d : ℝ)-q) := Real.rpow_pos_of_pos (hL k) _
  have hQle (k : ℕ) : (L k)^((d : ℝ)-q) ≤ (V k)^2 := by
    calc
      _ ≤ (L k)^((d : ℝ)+(d : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (hLone k) (by
          have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
          linarith only [hd0,hq.le])
      _ = (L k)^d*(L k)^d := by rw [Real.rpow_add (hL k)]; simp only [Real.rpow_natCast]
      _ = (V k)^2 := by dsimp only [V]; ring
  have hMV2 : Tendsto (fun k => M k/(V k)^2) atTop (𝓝 0) :=
    squeeze_zero (fun k => div_nonneg (hM0 k) (sq_nonneg _))
      (fun k => div_le_div_of_nonneg_left (hM0 k) (hMQ0 k) (hQle k)) hMQ
  have hMTV : Tendsto (fun k => M k/(T k*V k)) atTop (𝓝 0) := by
    have ht := hMV2.const_mul (2*H/δ)
    simp only [mul_zero] at ht
    apply Filter.Tendsto.congr' (h := ht)
    apply Eventually.of_forall
    intro k
    dsimp only [T]
    field_simp [(hV k).ne',hδ.ne',hH.ne']
  let U : ℕ → ℝ := fun k => (1+τ)*E k+
    (1+τ⁻¹)*c*((R : ℝ)^q*(1-a+M k/(T k*V k))+(R : ℝ)^(q-(d : ℝ)))+
    Cfall*K*(M k/(L k)^((d : ℝ)-q))
  have hU : Tendsto U atTop (𝓝 ((1+τ)*a*(W d (-q) P).toReal+
      (1+τ⁻¹)*c*((R : ℝ)^q*(1-a)+(R : ℝ)^(q-(d : ℝ))))) := by
    have hconstA : Tendsto (fun _ : ℕ => 1-a) atTop (𝓝 (1-a)) := tendsto_const_nhds
    have hconstB : Tendsto (fun _ : ℕ => (R : ℝ)^(q-(d : ℝ))) atTop
        (𝓝 ((R : ℝ)^(q-(d : ℝ)))) := tendsto_const_nhds
    have ht := ((hE.const_mul (1+τ)).add
      ((((hconstA.add hMTV).const_mul ((R : ℝ)^q)).add hconstB).const_mul ((1+τ⁻¹)*c))).add (hMQ.const_mul (Cfall*K))
    simpa only [U,mul_zero,add_zero,mul_assoc] using ht
  apply ge_of_tendsto hU
  apply Eventually.of_forall
  intro k
  exact balanced_density_inf_le_actual_dyadic_budget d (m k) k hd (hm k)
    (R : ℝ) q τ (by exact_mod_cast hR) hq hqTwo hτ
    (cubeDyadicSide_real_geometry R k) P hP hW χ h δ H hχsm hhsm hδ hδone hH
    hχ hh hmass hχs hhs

/-- Actual reverse inequality for each original finite-energy law. The
parameter order is tau, microcell integer R, then the smooth near-indicator
cutoff and correction. R1 then tends along the dyadic side sequence. -/
theorem balanced_density_inf_le_original_W
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2)
    (P : ConfigurationLaw d) (hP : Admissible d P) (hW : W d (-q) P ≠ ⊤) :
    sInf (balancedDensityValues d q) ≤ (W d (-q) P).toReal := by
  let w : ℝ := (W d (-q) P).toReal
  have hw : 0 ≤ w := original_finite_negative_W_nonneg d hd q hq hqTwo P hP hW
  have hqd : q < (d : ℝ) := hqTwo.trans_le (by exact_mod_cast hd)
  let c : ℝ := 8*(Real.sqrt d*(1/2))^q/q+2*cubeRoundingConstant d q
  have hc : 0 < c := add_pos_of_nonneg_of_pos
    (div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)) hq.le)
    (mul_pos (by norm_num) (cubeRoundingConstant_pos d q hq hqd))
  apply le_of_forall_pos_le_add
  intro ε hε
  let τ : ℝ := ε/(3*(w+1))
  have hwp : 0 < w+1 := by linarith only [hw]
  have hτ : 0 < τ := div_pos hε (mul_pos (by norm_num) hwp)
  let C : ℝ := (1+τ⁻¹)*c
  have hC : 0 < C := mul_pos (by positivity) hc
  have hτw : τ*w < ε/3 := by
    calc
      _ < τ*(w+1) := mul_lt_mul_of_pos_left (by linarith) hτ
      _ = _ := by dsimp only [τ]; field_simp [hwp.ne'];
  have htail : Tendsto (fun n : ℕ => C*(n : ℝ)^(q-(d : ℝ))) atTop (𝓝 0) := by
    have ht := ((tendsto_rpow_neg_atTop (sub_pos.mpr hqd)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_mul C
    simpa only [Function.comp_def,neg_sub,mul_zero] using ht
  obtain ⟨R,hRtail,hR⟩ :=
    ((htail.eventually (gt_mem_nhds (show (0 : ℝ) < ε/3 by positivity))).and
      (eventually_ge_atTop (1 : ℕ))).exists
  have hRp : 0 < (R : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hR)
  have hRq : 0 < (R : ℝ)^q := Real.rpow_pos_of_pos hRp q
  let γ : ℝ := ε/(3*C*(R : ℝ)^q)
  have hγ : 0 < γ := div_pos hε (mul_pos (mul_pos (by norm_num) hC) hRq)
  obtain ⟨χ,h,δ,H,hχsm,hhsm,hδ,hδone,hH,hχ,hh,hmass,hχs,hhs,hnear,haone⟩ :=
    exists_cubeRepair_smooth_base d γ hγ
  let a : ℝ := ∫ x : Rd d, (χ x)^2
  have hgap : C*(R : ℝ)^q*(1-a) < ε/3 := by
    calc
      _ < C*(R : ℝ)^q*γ :=
        mul_lt_mul_of_pos_left (by linarith only [hnear]) (mul_pos hC hRq)
      _ = _ := by dsimp only [γ]; field_simp [hC.ne',hRq.ne'];
  have hfixed := balanced_density_inf_le_smooth_window_budget d hd q hq hqTwo
    P hP hW τ hτ R hR χ h δ H hχsm hhsm hδ hδone hH hχ hh hmass hχs hhs
  have hmain : (1+τ)*a*w ≤ (1+τ)*w := by
    calc
      _ = (1+τ)*(a*w) := by ring
      _ ≤ (1+τ)*(1*w) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right haone hw) (by positivity)
      _ = _ := by rw [one_mul]
  have hfinal : sInf (balancedDensityValues d q) < w+ε := by
    change sInf (balancedDensityValues d q) ≤ (1+τ)*a*w+
      C*((R : ℝ)^q*(1-a)+(R : ℝ)^(q-(d : ℝ))) at hfixed
    nlinarith only [hfixed,hmain,hτw,hgap,hRtail]
  exact hfinal.le

/-- The genuine reverse comparison, combined with the already checked grid
comparison. This is the intended equality endpoint consumed by the negative
spherical upper/attainment path, with no equality or reverse-bound premise. -/
theorem balanced_density_inf_eq_e
    (d : ℕ) (hd : 2 ≤ d) (q : ℝ) (hq : 0 < q) (hqTwo : q < 2) :
    sInf (balancedDensityValues d q) = e d (-q) := by
  have hc := negative_constant_finiteness_and_sign d hd (-q)
    (neg_lt_neg hqTwo) (neg_lt_zero.mpr hq)
  have hreverse : ((sInf (balancedDensityValues d q) : ℝ) : EReal) ≤ eExtended d (-q) := by
    apply le_sInf
    rintro w ⟨P,hP,rfl⟩
    by_cases hW : W d (-q) P = ⊤
    · rw [hW]
      exact le_top
    · have hbot : W d (-q) P ≠ ⊥ :=
        ne_of_gt ((EReal.bot_lt_coe (c0 d (-q))).trans_le (c0_le_W d (-q) P))
      rw [← EReal.coe_toReal hW hbot]
      exact EReal.coe_le_coe_iff.mpr
        (balanced_density_inf_le_original_W d hd q hq hqTwo P hP hW)
  have hreverseReal : sInf (balancedDensityValues d q) ≤ e d (-q) := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [hc.1] using hreverse
  have hforward : e d (-q) ≤ sInf (balancedDensityValues d q) := by
    simpa only [balancedDensityValues] using
      (balanced_cube_density_limit_and_stationary_bound d hd q hq hqTwo).2
  exact le_antisymm hreverseReal hforward

end Riesz.Negative
