import Riesz.Asymptotics.PositiveSphericalUpper
import Riesz.Geometry.SphericalAreaCover
import Riesz.Geometry.InteriorGrid
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Actual chart transport of a positive finite-cell trial law. -/

noncomputable section
open MeasureTheory RieszShowcase Riesz.Negative Riesz.Stationary Riesz.Geometry
open scoped ENNReal Classical

namespace Riesz.Configuration

def sphericalCellChartExtension (d : ℕ) (D : Set (Rd d)) (F : Rd d → Sphere d) :
    Rd d → Sphere d := D.piecewise F (fun _ => F 0)

theorem measurable_sphericalCellChartExtension (d : ℕ) (D : Set (Rd d))
    (F : Rd d → Sphere d) (hD : MeasurableSet D) (hF : ContinuousOn F D) :
    Measurable (sphericalCellChartExtension d D F) := by
  exact hF.measurable_piecewise continuous_const.continuousOn hD

theorem inv_smul_preimage_cube (d : ℕ) (L R : ℝ) (hR : 0 < R) :
    (fun x : Rd d => R⁻¹ • x) ⁻¹' cube d (L / R) = cube d L := by
  ext x
  change (∀ i, 0 ≤ R⁻¹ * x i ∧ R⁻¹ * x i < L / R) ↔ ∀ i, 0 ≤ x i ∧ x i < L
  simp only [← div_eq_inv_mul, le_div_iff₀ hR, zero_mul, div_lt_div_iff_of_pos_right hR]

theorem map_cube_volume_inv_smul (d : ℕ) (L R : ℝ) (hR : 0 < R) :
    (volume.restrict (cube d L)).map (fun x : Rd d => R⁻¹ • x) =
      ENNReal.ofReal (R^d) • volume.restrict (cube d (L / R)) := by
  have hscale : (volume : Measure (Rd d)).map (fun x => R⁻¹ • x) =
      ENNReal.ofReal (R^d) • volume := by
    simpa only [finrank_euclideanSpace_fin, inv_pow, inv_inv,
      abs_of_pos (pow_pos hR d)] using
        Measure.map_addHaar_smul (volume : Measure (Rd d)) (inv_ne_zero hR.ne')
  have h := Measure.restrict_map (μ := (volume : Measure (Rd d)))
    (measurable_const_smul R⁻¹) (measurableSet_cube d (L / R))
  simpa only [hscale, Measure.restrict_smul, inv_smul_preimage_cube d L R hR] using h.symm

def sphericalCellAffine (d : ℕ) (L R : ℝ) (z : GridIndex d) (x : Rd d) : Rd d :=
  latticeOrigin d (L / R) z + R⁻¹ • x

theorem map_cube_volume_sphericalCellAffine (d : ℕ) (L R : ℝ)
    (hR : 0 < R) (z : GridIndex d) :
    (volume.restrict (cube d L)).map (sphericalCellAffine d L R z) =
      ENNReal.ofReal (R^d) • volume.restrict (latticeCell d (L / R) 0 z) := by
  change (volume.restrict (cube d L)).map
    ((fun x => latticeOrigin d (L / R) z + x) ∘ (fun x => R⁻¹ • x)) = _
  rw [← Measure.map_map (measurable_const_add _) (measurable_const_smul _),
    map_cube_volume_inv_smul d L R hR, Measure.map_smul, map_cube_volume_translation]
  simp only [latticeCell, zero_add]

theorem inv_smul_image_cube (d : ℕ) (L R : ℝ) (hR : 0 < R) :
    (fun x : Rd d => R⁻¹ • x) '' cube d L = cube d (L / R) := by
  have hsurj : Function.Surjective (fun x : Rd d => R⁻¹ • x) :=
    fun y => ⟨R • y, by simp only [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]⟩
  simpa only [inv_smul_preimage_cube d L R hR] using
    Set.image_preimage_eq (cube d (L / R)) hsurj

theorem sphericalCellAffine_image_cube (d : ℕ) (L R : ℝ) (hR : 0 < R) (z : GridIndex d) :
    sphericalCellAffine d L R z '' cube d L = latticeCell d (L / R) 0 z := by
  change ((fun x => latticeOrigin d (L / R) z + x) ∘ (fun x => R⁻¹ • x)) '' cube d L = _
  simp only [Set.image_comp, inv_smul_image_cube d L R hR, latticeCell, zero_add, translatedCube]

theorem continuous_sphericalCellAffine (d : ℕ) (L R : ℝ) (z : GridIndex d) :
    Continuous (sphericalCellAffine d L R z) := by
  exact continuous_const.add (continuous_const_smul R⁻¹)

theorem injective_sphericalCellAffine (d : ℕ) (L R : ℝ) (hR : 0 < R) (z : GridIndex d) :
    Function.Injective (sphericalCellAffine d L R z) := by
  intro x y h
  have hh := congrArg (fun v : Rd d => R • v) (show R⁻¹ • x = R⁻¹ • y from add_left_cancel h)
  simpa only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul] using hh

def sphericalCellMap (d : ℕ) (L R : ℝ) (D : Set (Rd d))
    (F : Rd d → Sphere d) (z : GridIndex d) (x : Rd d) : Rd (d + 1) :=
  (sphericalCellChartExtension d D F (sphericalCellAffine d L R z x)).val

theorem measurable_sphericalCellMap (d : ℕ) (L R : ℝ) (D : Set (Rd d))
    (F : Rd d → Sphere d) (hD : MeasurableSet D) (hF : ContinuousOn F D) (z : GridIndex d) :
    Measurable (sphericalCellMap d L R D F z) := by
  exact continuous_subtype_val.measurable.comp
    ((measurable_sphericalCellChartExtension d D F hD hF).comp
      (continuous_sphericalCellAffine d L R z).measurable)

theorem sphericalCellAffine_mapsTo (d : ℕ) (L R : ℝ) (hR : 0 < R)
    (z : GridIndex d) (D : Set (Rd d))
    (hcell : latticeCell d (L / R) 0 z ⊆ D) :
    Set.MapsTo (sphericalCellAffine d L R z) (cube d L) D := by
  exact fun x hx => hcell ((sphericalCellAffine_image_cube d L R hR z) ▸
    Set.mem_image_of_mem (sphericalCellAffine d L R z) hx)

theorem sphericalCellMap_eqOn (d : ℕ) (L R : ℝ) (hR : 0 < R)
    (z : GridIndex d) (D : Set (Rd d)) (F : Rd d → Sphere d)
    (hcell : latticeCell d (L / R) 0 z ⊆ D) :
    Set.EqOn (sphericalCellMap d L R D F z)
      (fun x => (F (sphericalCellAffine d L R z x)).val) (cube d L) := by
  exact fun x hx => congrArg Subtype.val
    (Set.piecewise_eq_of_mem D F (fun _ => F 0)
      (sphericalCellAffine_mapsTo d L R hR z D hcell hx))

theorem continuousOn_sphericalCellMap (d : ℕ) (L R : ℝ) (hR : 0 < R)
    (z : GridIndex d) (D : Set (Rd d)) (F : Rd d → Sphere d)
    (hF : ContinuousOn F D) (hcell : latticeCell d (L / R) 0 z ⊆ D) :
    ContinuousOn (sphericalCellMap d L R D F z) (cube d L) := by
  exact (continuous_subtype_val.comp_continuousOn
    (hF.comp (continuous_sphericalCellAffine d L R z).continuousOn
      (sphericalCellAffine_mapsTo d L R hR z D hcell))).congr
        (sphericalCellMap_eqOn d L R hR z D F hcell)

theorem injOn_sphericalCellMap (d : ℕ) (L R : ℝ) (hR : 0 < R)
    (z : GridIndex d) (D : Set (Rd d)) (F : Rd d → Sphere d)
    (hFi : Set.InjOn F D) (hcell : latticeCell d (L / R) 0 z ⊆ D) :
    Set.InjOn (sphericalCellMap d L R D F z) (cube d L) := by
  intro x hx y hy hxy
  rw [sphericalCellMap_eqOn d L R hR z D F hcell hx,
    sphericalCellMap_eqOn d L R hR z D F hcell hy] at hxy
  exact injective_sphericalCellAffine d L R hR z
    (hFi (sphericalCellAffine_mapsTo d L R hR z D hcell hx)
      (sphericalCellAffine_mapsTo d L R hR z D hcell hy) (Subtype.val_injective hxy))

theorem measurableSet_sphericalCellMap_image (d : ℕ) (L R : ℝ) (hR : 0 < R)
    (z : GridIndex d) (D : Set (Rd d)) (F : Rd d → Sphere d)
    (hF : ContinuousOn F D) (hFi : Set.InjOn F D)
    (hcell : latticeCell d (L / R) 0 z ⊆ D) :
    MeasurableSet (sphericalCellMap d L R D F z '' cube d L) := by
  exact (measurableSet_cube d L).image_of_continuousOn_injOn
    (continuousOn_sphericalCellMap d L R hR z D F hF hcell)
    (injOn_sphericalCellMap d L R hR z D F hFi hcell)

theorem map_volume_sphericalCellChartExtension (d : ℕ) (D : Set (Rd d))
    (F : Rd d → Sphere d) (hF : ContinuousOn F D) (hFi : Set.InjOn F D)
    (harea : ∀ E : Set (Rd d), MeasurableSet E → E ⊆ D →
      sphericalMeasure d (F '' E) =
        (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E)
    (E : Set (Rd d)) (hE : MeasurableSet E) (hED : E ⊆ D) :
    (volume.restrict E).map (sphericalCellChartExtension d D F) =
      ENNReal.ofReal (omega d) • (sphericalMeasure d).restrict (F '' E) := by
  apply Eq.trans (Measure.map_congr ?_)
    (Riesz.Geometry.equalAreaChart_map_volume_restrict d D F hF hFi harea hE hED)
  exact (ae_restrict_mem hE).mono (fun x hx =>
    Set.piecewise_eq_of_mem D F (fun _ => F 0) (hED hx))

theorem map_cube_volume_sphericalCellMap (d : ℕ) (L R : ℝ) (hR : 0 < R)
    (z : GridIndex d) (D : Set (Rd d)) (F : Rd d → Sphere d)
    (hD : MeasurableSet D) (hF : ContinuousOn F D) (hFi : Set.InjOn F D)
    (harea : ∀ E : Set (Rd d), MeasurableSet E → E ⊆ D →
      sphericalMeasure d (F '' E) =
        (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E)
    (hcell : latticeCell d (L / R) 0 z ⊆ D) :
    (volume.restrict (cube d L)).map (sphericalCellMap d L R D F z) =
      (ENNReal.ofReal (R^d * omega d) •
        (sphericalMeasure d).restrict (F '' latticeCell d (L / R) 0 z)).map Subtype.val := by
  change (volume.restrict (cube d L)).map
    ((Subtype.val ∘ sphericalCellChartExtension d D F) ∘ sphericalCellAffine d L R z) = _
  rw [← Measure.map_map
    (continuous_subtype_val.measurable.comp (measurable_sphericalCellChartExtension d D F hD hF))
    (continuous_sphericalCellAffine d L R z).measurable,
    map_cube_volume_sphericalCellAffine d L R hR z, Measure.map_smul,
    ← Measure.map_map continuous_subtype_val.measurable
      (measurable_sphericalCellChartExtension d D F hD hF),
    map_volume_sphericalCellChartExtension d D F hF hFi harea
      (latticeCell d (L / R) 0 z) (latticeCell_measurable d (L / R) 0 z) hcell]
  rw [Measure.map_smul, Measure.map_smul, smul_smul, ENNReal.ofReal_mul (pow_nonneg hR.le d)]

theorem sphericalCellTransportLaw_mean (d N : ℕ) (L R : ℝ) (hR : 0 < R)
    (hRN : R^d * omega d = N) (z : GridIndex d) (D : Set (Rd d))
    (F : Rd d → Sphere d) (hD : MeasurableSet D)
    (hF : ContinuousOn F D) (hFi : Set.InjOn F D)
    (harea : ∀ E : Set (Rd d), MeasurableSet E → E ⊆ D →
      sphericalMeasure d (F '' E) =
        (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E)
    (hcell : latticeCell d (L / R) 0 z ⊆ D)
    (Q : ConfigurationLaw d)
    (hmean : ∀ E, MeasurableSet E → (∫⁻ μ, μ E ∂Q) = (volume.restrict (cube d L)) E)
    (E : Set (Rd (d + 1))) (hE : MeasurableSet E) :
    (∫⁻ η, η E ∂finiteCellTransportLaw d (d + 1) Q (sphericalCellMap d L R D F z)) =
      ((ENNReal.ofReal (N : ℝ) •
        (sphericalMeasure d).restrict (F '' latticeCell d (L / R) 0 z)).map Subtype.val) E := by
  rw [finiteCellTransportLaw_mean d (d + 1) Q (volume.restrict (cube d L))
    (sphericalCellMap d L R D F z) (measurable_sphericalCellMap d L R D F hD hF z) hmean E hE,
    map_cube_volume_sphericalCellMap d L R hR z D F hD hF hFi harea hcell, hRN]

theorem sphericalRadius_area_normalization (d N : ℕ) (hd : 0 < d) :
    (sphericalRadius d N)^d * omega d = N := by
  rw [sphericalRadius_pow_dimension d N hd, div_mul_cancel₀ _ (sphericalArea_pos d).ne']

theorem norm_sphericalCellAffine_sub (d : ℕ) (L R : ℝ) (hR : 0 < R)
    (z : GridIndex d) (x y : Rd d) :
    ‖sphericalCellAffine d L R z y - sphericalCellAffine d L R z x‖ = R⁻¹ * ‖y - x‖ := by
  simp only [sphericalCellAffine, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]

def sphericalCellKernel (d : ℕ) (s R : ℝ) (p : Rd (d + 1) × Rd (d + 1)) : ℝ≥0∞ :=
  ENNReal.ofReal (K_s s (R * ‖p.2 - p.1‖))

theorem measurable_sphericalCellKernel (d : ℕ) (s R : ℝ) :
    Measurable (sphericalCellKernel d s R) := by
  exact ((((measurable_const.mul (measurable_snd.sub measurable_fst).norm).pow_const (-s)).div_const s).ennreal_ofReal)

theorem sphericalCellMap_relative_distance (d : ℕ) (L R δ : ℝ) (hR : 0 < R)
    (z : GridIndex d) (D : Set (Rd d)) (F : Rd d → Sphere d)
    (hcell : latticeCell d (L / R) 0 z ⊆ D)
    (hmetric : ∀ x ∈ D, ∀ y ∈ D,
      (1 - δ) * ‖x - y‖ ≤ chord d (F x) (F y) ∧
        chord d (F x) (F y) ≤ (1 + δ) * ‖x - y‖)
    (x : Rd d) (hx : x ∈ cube d L) (y : Rd d) (hy : y ∈ cube d L) :
    (1 - δ) * ‖y - x‖ ≤ R * ‖sphericalCellMap d L R D F z y - sphericalCellMap d L R D F z x‖ ∧
      R * ‖sphericalCellMap d L R D F z y - sphericalCellMap d L R D F z x‖ ≤ (1 + δ) * ‖y - x‖ := by
  have h := hmetric (sphericalCellAffine d L R z y)
    (sphericalCellAffine_mapsTo d L R hR z D hcell hy)
    (sphericalCellAffine d L R z x)
    (sphericalCellAffine_mapsTo d L R hR z D hcell hx)
  rw [sphericalCellMap_eqOn d L R hR z D F hcell hy,
    sphericalCellMap_eqOn d L R hR z D F hcell hx]
  simpa only [chord, norm_sphericalCellAffine_sub d L R hR z x y,
    mul_left_comm R (1 - δ), mul_left_comm R (1 + δ), ← mul_assoc,
    mul_inv_cancel₀ hR.ne', one_mul, mul_one] using
      (And.intro (mul_le_mul_of_nonneg_left h.1 hR.le) (mul_le_mul_of_nonneg_left h.2 hR.le))

theorem sphericalCellKernel_relative_distortion (d : ℕ) (s L R δ : ℝ)
    (hs : 0 < s) (hR : 0 < R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (z : GridIndex d) (D : Set (Rd d)) (F : Rd d → Sphere d)
    (hcell : latticeCell d (L / R) 0 z ⊆ D)
    (hmetric : ∀ x ∈ D, ∀ y ∈ D,
      (1 - δ) * ‖x - y‖ ≤ chord d (F x) (F y) ∧
        chord d (F x) (F y) ≤ (1 + δ) * ‖x - y‖)
    (x : Rd d) (hx : x ∈ cube d L) (y : Rd d) (hy : y ∈ cube d L) :
    ENNReal.ofReal ((1 + δ)^(-s)) * positiveCellKernel d s (x, y) ≤
        sphericalCellKernel d s R (sphericalCellMap d L R D F z x, sphericalCellMap d L R D F z y) ∧
      sphericalCellKernel d s R (sphericalCellMap d L R D F z x, sphericalCellMap d L R D F z y) ≤
        ENNReal.ofReal ((1 - δ)^(-s)) * positiveCellKernel d s (x, y) := by
  have hdist := sphericalCellMap_relative_distance d L R δ hR z D F hcell hmetric x hx y hy
  have h := positive_kernel_relative_distortion s δ ‖y - x‖
    (R * ‖sphericalCellMap d L R D F z y - sphericalCellMap d L R D F z x‖)
    hs hδ0 hδ1 (norm_nonneg _) (mul_nonneg hR.le (norm_nonneg _)) hdist.1 hdist.2
  simpa only [sphericalCellKernel, positiveCellKernel,
    ENNReal.ofReal_mul (Real.rpow_nonneg (show 0 ≤ 1 + δ by linarith only [hδ0]) (-s)),
    ENNReal.ofReal_mul (Real.rpow_nonneg (sub_nonneg.mpr hδ1.le) (-s))] using
      (And.intro (ENNReal.ofReal_le_ofReal h.1) (ENNReal.ofReal_le_ofReal h.2))

theorem sphericalCellTransportLaw_centered_energy (d N : ℕ) (s L R δ : ℝ)
    (hs : 0 < s) (hR : 0 < R) (hRN : R^d * omega d = N)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (z : GridIndex d) (D : Set (Rd d)) (F : Rd d → Sphere d)
    (hD : MeasurableSet D) (hF : ContinuousOn F D) (hFi : Set.InjOn F D)
    (harea : ∀ E : Set (Rd d), MeasurableSet E → E ⊆ D →
      sphericalMeasure d (F '' E) =
        (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E)
    (hcell : latticeCell d (L / R) 0 z ⊆ D)
    (hmetric : ∀ x ∈ D, ∀ y ∈ D,
      (1 - δ) * ‖x - y‖ ≤ chord d (F x) (F y) ∧
        chord d (F x) (F y) ≤ (1 + δ) * ‖x - y‖)
    (Q : ConfigurationLaw d)
    (hQ : ∀ᵐ μ ∂Q, IsSimpleConfiguration d μ ∧ μ (cube d L)ᶜ = 0 ∧ μ Set.univ < ⊤)
    (hpair : (∫⁻ μ, windowPairIntegral d (positiveCellKernel d s) μ ∂Q) ≠ ⊤)
    (hbackground : positiveCellBackground d s L ≠ ⊤) :
    let T := sphericalCellMap d L R D F z
    let Λ := finiteCellTransportLaw d (d + 1) Q T
    let ν := (ENNReal.ofReal (N : ℝ) •
      (sphericalMeasure d).restrict (F '' latticeCell d (L / R) 0 z)).map Subtype.val
    (∫⁻ η, windowPairIntegral (d + 1) (sphericalCellKernel d s R) η ∂Λ) ≠ ⊤ ∧
      (∫⁻ p, sphericalCellKernel d s R p ∂ν.prod ν) ≠ ⊤ ∧
      Integrable (cellRealEnergy (d + 1) (sphericalCellKernel d s R)) Λ ∧
      (∫ η, cellRealEnergy (d + 1) (sphericalCellKernel d s R) η ∂Λ) -
          (∫⁻ p, sphericalCellKernel d s R p ∂ν.prod ν).toReal ≤
        (1 - δ)^(-s) * (∫ μ, cellRealEnergy d (positiveCellKernel d s) μ ∂Q) -
          (1 + δ)^(-s) * (positiveCellBackground d s L).toReal := by
  simpa only [map_cube_volume_sphericalCellMap d L R hR z D F hD hF hFi harea hcell,
    hRN, positiveCellBackground] using
      finiteCellTransportLaw_centered_energy d (d + 1) volume Q (cube d L) (measurableSet_cube d L)
        (sphericalCellMap d L R D F z) (measurable_sphericalCellMap d L R D F hD hF z)
        (injOn_sphericalCellMap d L R hR z D F hFi hcell)
        (measurableSet_sphericalCellMap_image d L R hR z D F hF hFi hcell) hQ
        (positiveCellKernel d s) (measurable_positiveCellKernel d s)
        (sphericalCellKernel d s R) (measurable_sphericalCellKernel d s R)
        ((1 - δ)^(-s)) ((1 + δ)^(-s))
        (Real.rpow_nonneg (sub_nonneg.mpr hδ1.le) (-s))
        (Real.rpow_nonneg (show 0 ≤ 1 + δ by linarith only [hδ0]) (-s))
        (fun x hx y hy => (sphericalCellKernel_relative_distortion d s L R δ hs hR hδ0 hδ1
          z D F hcell hmetric x hx y hy).1)
        (fun x hx y hy => (sphericalCellKernel_relative_distortion d s L R δ hs hR hδ0 hδ1
          z D F hcell hmetric x hx y hy).2) hpair hbackground

end Riesz.Configuration
