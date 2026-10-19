import Riesz.Geometry.SphericalArea
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Order.Disjointed
import Mathlib.Order.Interval.Finset.Fin

/-!
# Finite coverage by the explicit equal-area chart

An explicit polar inverse gives a sphere neighborhood inside every positive
parameter ball. Compactness and the original orthogonal action then give a
finite open cover carried by rotations of the audited chart.
-/

noncomputable section

open MeasureTheory RieszShowcase
open scoped ENNReal Topology

namespace Riesz.Geometry

/-- Recover the cylinder angle and transverse coordinates. -/
def equalAreaCapInverse (k : ℕ) (y : Rd (k + 2)) : Rd (k + 1) :=
  euclideanCons k (polarCoord (y 0, (euclideanTail (k + 1) y) 0)).2
    (euclideanTail k (euclideanTail (k + 1) y))

/-- The polar branch recovers every sphere point with positive north coordinate. -/
theorem equalAreaCapPoint_inverse (k : ℕ) (y : Sphere (k + 1))
    (hy : 0 < y.val 0) :
    equalAreaCapPoint k (equalAreaCapInverse k y.val) = y := by
  let q : ℝ × ℝ := (y.val 0, (euclideanTail (k + 1) y.val) 0)
  let u : Rd k := euclideanTail k (euclideanTail (k + 1) y.val)
  have hnorm := euclideanCons_norm_sq (k + 1) (y.val 0)
    (euclideanTail (k + 1) y.val)
  rw [euclideanCons_head_tail, y.property] at hnorm
  have htail := euclideanCons_norm_sq k ((euclideanTail (k + 1) y.val) 0) u
  rw [euclideanCons_head_tail] at htail
  have hsq : q.1 ^ 2 + q.2 ^ 2 + ‖u‖ ^ 2 = 1 := by
    dsimp only [q]
    nlinarith
  have hu : ‖u‖ < 1 := by
    have hq : 0 < q.1 := hy
    nlinarith [sq_pos_of_pos hq, sq_nonneg q.2, norm_nonneg u]
  have hsource : q ∈ polarCoord.source := by
    exact Or.inl hy
  have hpair := polarCoord.left_inv hsource
  change ((polarCoord q).1 * Real.cos (polarCoord q).2,
    (polarCoord q).1 * Real.sin (polarCoord q).2) = q at hpair
  have ha : equalAreaCapAmplitude k (equalAreaCapInverse k y.val) =
      (polarCoord q).1 := by
    change Real.sqrt (1 - ‖u‖ ^ 2) = Real.sqrt (q.1 ^ 2 + q.2 ^ 2)
    congr 1
    linarith
  apply Subtype.ext
  rw [equalAreaCapPoint_val k (show
    ‖euclideanTail k (equalAreaCapInverse k y.val)‖ < 1 from hu)]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change equalAreaCapAmplitude k (equalAreaCapInverse k y.val) *
      Real.cos (polarCoord q).2 = q.1
    simpa only [ha] using congrArg Prod.fst hpair
  · refine Fin.cases ?_ (fun j => ?_) j
    · change equalAreaCapAmplitude k (equalAreaCapInverse k y.val) *
        Real.sin (polarCoord q).2 = q.2
      simpa only [ha] using congrArg Prod.snd hpair
    · rfl

theorem equalAreaCapInverse_north (k : ℕ) :
    equalAreaCapInverse k (normalNorth (k + 1)) = 0 := by
  simp [equalAreaCapInverse, normalNorth, euclideanCons, euclideanTail,
    polarCoord, Complex.equivRealProd_symm_apply]
  exact funext fun i => Fin.cases rfl (fun _ => rfl) i

theorem equalAreaCapInverse_continuousAt_north (k : ℕ) :
    ContinuousAt (equalAreaCapInverse k) (normalNorth (k + 1)) := by
  have hp : Continuous (fun y : Rd (k + 2) =>
      (y 0, (euclideanTail (k + 1) y) 0)) :=
    (PiLp.continuous_apply 2 (fun _ : Fin (k + 2) => ℝ) 0).prodMk
      ((PiLp.continuous_apply 2 (fun _ : Fin (k + 1) => ℝ) 0).comp
        (euclideanTail_continuous (k + 1)))
  have hsource :
      ((normalNorth (k + 1)) 0,
        (euclideanTail (k + 1) (normalNorth (k + 1))) 0) ∈
        polarCoord.source := by
    exact Or.inl (by simp [normalNorth, euclideanCons])
  have hangle : ContinuousAt (fun y : Rd (k + 2) =>
      (polarCoord (y 0, (euclideanTail (k + 1) y) 0)).2)
      (normalNorth (k + 1)) :=
    ((polarCoord.continuousAt hsource).comp
      (f := fun y : Rd (k + 2) => (y 0, (euclideanTail (k + 1) y) 0))
      hp.continuousAt).snd
  fun_prop [equalAreaCapInverse, euclideanCons, euclideanTail]

/-- Every positive parameter ball carries an actual sphere neighborhood of north. -/
theorem equalAreaCapPoint_image_ball_contains_ball (k : ℕ) {rho : ℝ}
    (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧
      Metric.ball (normalPoint (k + 1) 1 0) delta ⊆
        equalAreaCapPoint k '' Metric.ball (0 : Rd (k + 1)) rho := by
  let n : Sphere (k + 1) := normalPoint (k + 1) 1 0
  have hn : n.val = normalNorth (k + 1) := normalPoint_zero (k + 1) 1
  have hi : ContinuousAt (fun y : Sphere (k + 1) => equalAreaCapInverse k y.val) n := by
    have hc : ContinuousAt (equalAreaCapInverse k) n.val := by
      simpa only [hn] using equalAreaCapInverse_continuousAt_north k
    exact hc.comp continuous_subtype_val.continuousAt
  have hizero : equalAreaCapInverse k n.val = 0 := by
    rw [hn, equalAreaCapInverse_north]
  have hball : ∀ᶠ y : Sphere (k + 1) in 𝓝 n,
      equalAreaCapInverse k y.val ∈ Metric.ball (0 : Rd (k + 1)) rho := by
    apply hi.eventually
    simpa only [hizero] using! Metric.ball_mem_nhds (0 : Rd (k + 1)) hrho
  have hhead : ∀ᶠ y : Sphere (k + 1) in 𝓝 n, 0 < y.val 0 := by
    exact (northHemisphere_isOpen (k + 1)).mem_nhds
      (by simp [northHemisphere, hn, normalNorth, euclideanCons])
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hhead.and hball)
  refine ⟨delta, hdelta, fun y hy => ?_⟩
  exact ⟨equalAreaCapInverse k y.val, (hcontrol y hy).2,
    equalAreaCapPoint_inverse k y (hcontrol y hy).1⟩

/-- The existing orthogonal action is transitive on the exact Showcase sphere. -/
theorem rotateSphere_transitive (d : ℕ) (x y : Sphere d) :
    ∃ U : Problem1.Orthogonal d, rotateSphere d U x = y := by
  obtain ⟨U, hU⟩ := Problem1.sphere_transitive (d + 1) (Nat.succ_pos d)
    (problem1SphereIsometryEquiv d x) (problem1SphereIsometryEquiv d y)
  refine ⟨U, ?_⟩
  simpa only [rotateSphere, Problem1.sphereAction, IsometryEquiv.symm_apply_apply] using
    congrArg (problem1SphereIsometryEquiv d).symm hU

/-- Finitely many open rotated sphere balls are carried by equal-area charts. -/
theorem exists_finite_equalAreaCapPoint_open_cover (k : ℕ) {rho : ℝ}
    (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ t : Finset (Problem1.Orthogonal (k + 1)),
        let V : Problem1.Orthogonal (k + 1) → Set (Sphere (k + 1)) :=
          fun U => rotateSphere (k + 1) U⁻¹ ⁻¹'
            Metric.ball (normalPoint (k + 1) 1 0) delta
        (∀ U, IsOpen (V U)) ∧
        ((Set.univ : Set (Sphere (k + 1))) ⊆ ⋃ U ∈ t, V U) ∧
        (∀ U, V U ⊆ (rotateSphere (k + 1) U ∘ equalAreaCapPoint k) ''
          Metric.ball (0 : Rd (k + 1)) rho) := by
  classical
  obtain ⟨delta, hdelta, himage⟩ := equalAreaCapPoint_image_ball_contains_ball k hrho
  let n : Sphere (k + 1) := normalPoint (k + 1) 1 0
  let V : Problem1.Orthogonal (k + 1) → Set (Sphere (k + 1)) :=
    fun U => rotateSphere (k + 1) U⁻¹ ⁻¹' Metric.ball n delta
  have hopen : ∀ U, IsOpen (V U) := fun U =>
    Metric.isOpen_ball.preimage (rotateSphere_isometry (k + 1) U⁻¹).continuous
  have hcover : (Set.univ : Set (Sphere (k + 1))) ⊆ ⋃ U, V U := by
    intro y _
    obtain ⟨U, hU⟩ := rotateSphere_transitive (k + 1) n y
    refine Set.mem_iUnion.mpr ⟨U, ?_⟩
    change rotateSphere (k + 1) U⁻¹ y ∈ Metric.ball n delta
    rw [← hU, ← rotateSphere_mul, inv_mul_cancel, rotateSphere_one]
    exact Metric.mem_ball_self hdelta
  have hcompact : IsCompact (Set.univ : Set (Sphere (k + 1))) := by
    have hc := (isCompact_univ : IsCompact
      (Set.univ : Set (Problem1.Sphere (k + 1)))).image
        (problem1SphereIsometryEquiv (k + 1)).symm.continuous
    simpa only [Set.image_univ,
      (problem1SphereIsometryEquiv (k + 1)).symm.surjective.range_eq] using hc
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover V hopen hcover
  refine ⟨delta, hdelta, t, hopen, ht, fun U y hy => ?_⟩
  obtain ⟨x, hx, heq⟩ := himage hy
  refine ⟨x, hx, ?_⟩
  simp only [Function.comp_apply, heq, ← rotateSphere_mul, mul_inv_cancel, rotateSphere_one]

/-- A finite open cover admits disjoint open patches losing arbitrarily little area. -/
theorem exists_disjoint_open_subordinate_almost_cover
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [NormalSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] [Measure.InnerRegularCompactLTTop mu]
    (n : ℕ) (U : Fin n → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ O : Fin n → Set X,
      (∀ i, IsOpen (O i) ∧ O i ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (O i) (O j)) ∧
      mu (⋃ i, O i)ᶜ < ENNReal.ofReal eta := by
  classical
  let A : Fin n → Set X := disjointed U
  let delta : ℝ := eta / ((n : ℝ) + 1)
  have hdelta : 0 < delta := div_pos heta (by positivity)
  have hAnon : ∀ i, MeasurableSet (A i) := by
    intro i
    rw [show A i = U i ∩ ⋂ j < i, (U j)ᶜ from disjointed_eq_inter_compl U i]
    exact (hopen i).measurableSet.inter
      (MeasurableSet.iInter fun j : Fin n => MeasurableSet.iInter fun (_hj : j < i) =>
        (hopen j).measurableSet.compl)
  have hAsub : ∀ i, A i ⊆ U i := fun i => disjointed_subset U i
  have hAdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)) := disjoint_disjointed U
  have hAcover : (⋃ i, A i) = Set.univ := by
    simpa only [A, iUnion_disjointed] using hcover
  choose K hKsub hKcompact hKloss using fun i =>
    (hAnon i).exists_isCompact_sdiff_lt (measure_ne_top mu (A i))
      (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
  have hKdisjoint : Pairwise (fun i j => Disjoint (K i) (K j)) :=
    fun i j hij => (hAdisjoint hij).mono (hKsub i) (hKsub j)
  have hfilters : Pairwise (fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))) :=
    fun i j hij => disjoint_nhdsSet_nhdsSet (hKcompact i).isClosed
      (hKcompact j).isClosed (hKdisjoint hij)
  obtain ⟨V, hV, hVdisjoint⟩ :=
    hfilters.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (K i))
  let O : Fin n → Set X := fun i => V i ∩ U i
  have hKO : ∀ i, K i ⊆ O i :=
    fun i _ hx => ⟨(hV i).2 hx, hAsub i (hKsub i hx)⟩
  have hOopen : ∀ i, IsOpen (O i) := fun i => (hV i).1.inter (hopen i)
  have hremaining : (⋃ i, O i)ᶜ ⊆ ⋃ i, A i \ K i := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp
      (show x ∈ ⋃ i, A i from hAcover.symm ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨i, hxi,
      fun hxK => hx (Set.mem_iUnion.mpr ⟨i, hKO i hxK⟩)⟩
  have hbudget : (n : ℝ) * delta < eta := by
    have hdelta_eq : delta * ((n : ℝ) + 1) = eta :=
      div_mul_cancel₀ eta (by positivity)
    nlinarith
  refine ⟨O, (fun i => ⟨hOopen i, Set.inter_subset_right⟩),
    (fun i j hij => (hVdisjoint hij).mono Set.inter_subset_left Set.inter_subset_left), ?_⟩
  calc
    mu (⋃ i, O i)ᶜ ≤ mu (⋃ i, A i \ K i) := measure_mono hremaining
    _ ≤ ∑ i : Fin n, mu (A i \ K i) := measure_iUnion_fintype_le mu _
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal delta :=
      Finset.sum_le_sum (fun i _ => (hKloss i).le)
    _ = (n : ℝ≥0∞) * ENNReal.ofReal delta := by simp
    _ = ENNReal.ofReal ((n : ℝ) * delta) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    _ < ENNReal.ofReal eta := (ENNReal.ofReal_lt_ofReal_iff heta).mpr hbudget

/-- Exact area on measurable pieces determines the transported parameter measure. -/
theorem equalAreaChart_map_volume_restrict
    (d : ℕ) (B : Set (Rd d)) (F : Rd d → Sphere d)
    (hcont : ContinuousOn F B) (hinj : Set.InjOn F B)
    (harea : ∀ E : Set (Rd d), MeasurableSet E → E ⊆ B →
      sphericalMeasure d (F '' E) =
        (ENNReal.ofReal (omega d))⁻¹ * (volume : Measure (Rd d)) E)
    {D : Set (Rd d)} (hD : MeasurableSet D) (hDsub : D ⊆ B) :
    (volume.restrict D).map F =
      ENNReal.ofReal (omega d) • (sphericalMeasure d).restrict (F '' D) := by
  have hcD : ContinuousOn F D := hcont.mono hDsub
  have hEmb : MeasurableEmbedding (D.restrict F) :=
    ContinuousOn.measurableEmbedding hD hcD (hinj.mono hDsub)
  have hFae : AEMeasurable F ((volume : Measure (Rd d)).restrict D) :=
    hcD.aemeasurable hD
  ext S hS
  let E : Set (Rd d) := F ⁻¹' S ∩ D
  have hEeq : ((↑) : D → Rd d) '' ((D.restrict F) ⁻¹' S) = E := by
    ext x
    simp [E, Set.mem_image, and_comm]
  have hE : MeasurableSet E := by
    rw [← hEeq]
    exact (MeasurableEmbedding.subtype_coe hD).measurableSet_image.mpr (hEmb.measurable hS)
  have himageE : F '' E = S ∩ (F '' D) := Set.image_preimage_inter F D S
  rw [Measure.map_apply_of_aemeasurable hFae hS,
    Measure.restrict_apply' hD, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS]
  rw [← himageE, harea E hE (fun _ hx => hDsub hx.2)]
  exact (ENNReal.mul_inv_cancel_left
    (ENNReal.ofReal_pos.mpr (Riesz.Asymptotics.omega_pos d)).ne'
    ENNReal.ofReal_ne_top).symm

/-- The audited cap chart transports Lebesgue measure with the exact sphere factor. -/
theorem equalAreaCapPoint_map_volume_restrict
    (k : ℕ) (D : Set (Rd (k + 1))) (hD : MeasurableSet D)
    (hcyl : ∀ x ∈ D, ‖euclideanTail k x‖ < 1)
    (hinj : Set.InjOn (equalAreaCapVector k) D) :
    (volume.restrict D).map (equalAreaCapPoint k) =
      ENNReal.ofReal (omega (k + 1)) •
        (sphericalMeasure (k + 1)).restrict (equalAreaCapPoint k '' D) := by
  apply equalAreaChart_map_volume_restrict (k + 1) D (equalAreaCapPoint k)
    (equalAreaCapPoint_continuousOn k D hcyl)
    (equalAreaCapPoint_injOn k D hcyl hinj) ?_ hD (fun _ hx => hx)
  exact fun E hE hsub => equalAreaCapPoint_sphericalMeasure k E hE
    (fun x hx => hcyl x (hsub hx)) (hinj.mono hsub)

theorem rotateSphere_map_sphericalMeasure (d : ℕ) (U : Problem1.Orthogonal d) :
    (sphericalMeasure d).map (rotateSphere d U) = sphericalMeasure d := by
  have hconj : rotateSphere d U ∘ (problem1SphereIsometryEquiv d).symm =
      (problem1SphereIsometryEquiv d).symm ∘ Problem1.sphereAction U := by
    funext x
    simp only [Function.comp_apply, rotateSphere, IsometryEquiv.apply_symm_apply]
  rw [sphericalMeasure,
    Measure.map_map (rotateSphere_isometry d U).continuous.measurable
      (problem1SphereIsometryEquiv d).symm.continuous.measurable,
    hconj, ← Measure.map_map (problem1SphereIsometryEquiv d).symm.continuous.measurable
      (Problem1.sphereActionN_continuous U).measurable, Problem1.sigma_map_sphereAction]

theorem rotateSphere_measurePreserving (d : ℕ) (U : Problem1.Orthogonal d) :
    MeasurePreserving (rotateSphere d U) (sphericalMeasure d) (sphericalMeasure d) :=
  ⟨(rotateSphere_isometry d U).continuous.measurable, rotateSphere_map_sphericalMeasure d U⟩

/-- The original rotation with its explicit inverse, as an isometry equivalence. -/
def rotateSphereIsometryEquiv (d : ℕ) (U : Problem1.Orthogonal d) : Sphere d ≃ᵢ Sphere d := by
  refine { toFun := rotateSphere d U
           invFun := rotateSphere d U⁻¹
           left_inv := ?_
           right_inv := ?_
           isometry_toFun := rotateSphere_isometry d U }
  all_goals intro x
  all_goals simp only [← rotateSphere_mul, inv_mul_cancel, mul_inv_cancel, rotateSphere_one]

theorem sphericalMeasure_rotateSphere_image (d : ℕ) (U : Problem1.Orthogonal d)
    (A : Set (Sphere d)) :
    sphericalMeasure d (rotateSphere d U '' A) = sphericalMeasure d A := by
  simpa only [Set.preimage_image_eq _ (rotateSphere_isometry d U).injective] using!
    ((rotateSphere_measurePreserving d U).measure_preimage_emb
      (rotateSphereIsometryEquiv d U).toHomeomorph.measurableEmbedding
      (rotateSphere d U '' A)).symm

/-- Pull disjoint open patches back to open subsets of their parameter charts. -/
theorem exists_disjoint_open_chart_domains
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [NormalSpace X] [TopologicalSpace Y]
    (mu : Measure X) [IsFiniteMeasure mu] [Measure.InnerRegularCompactLTTop mu]
    (B : Set Y) (hB : IsOpen B) (n : ℕ) (F : Fin n → Y → X)
    (hF : ∀ i, ContinuousOn (F i) B) (U : Fin n → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ)
    (himage : ∀ i, U i ⊆ F i '' B) {eta : ℝ} (heta : 0 < eta) :
    ∃ D : Fin n → Set Y,
      (∀ i, IsOpen (D i) ∧ D i ⊆ B ∧ F i '' D i ⊆ U i ∧ IsOpen (F i '' D i)) ∧
      Pairwise (fun i j => Disjoint (F i '' D i) (F j '' D j)) ∧
      mu (⋃ i, F i '' D i)ᶜ < ENNReal.ofReal eta := by
  obtain ⟨O, hO, hdisjoint, hloss⟩ :=
    exists_disjoint_open_subordinate_almost_cover mu n U hU hcover heta
  let D : Fin n → Set Y := fun i => B ∩ (F i) ⁻¹' O i
  have hDO : ∀ i, F i '' D i = O i := by
    intro i
    exact (Set.image_inter_preimage (F i) B (O i)).trans
      (Set.inter_eq_right.mpr ((hO i).2.trans (himage i)))
  refine ⟨D, (fun i => ⟨(hF i).isOpen_inter_preimage hB (hO i).1,
    Set.inter_subset_left, (hDO i) ▸ (hO i).2, (hDO i) ▸ (hO i).1⟩), ?_, ?_⟩
  · simpa only [hDO] using hdisjoint
  · simpa only [hDO] using hloss

/-- Finitely many disjoint equal-area patches cover all but any prescribed area.
Their open bounded parameter domains retain the local relative chord estimate. -/
theorem exists_finite_disjoint_equalAreaCapPoint_patches (k : ℕ)
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon) (hepsilon' : epsilon < 1)
    (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 / 2 ∧
      ∃ n : ℕ, ∃ U : Fin n → Problem1.Orthogonal (k + 1),
        ∃ D : Fin n → Set (Rd (k + 1)),
          let F : Fin n → Rd (k + 1) → Sphere (k + 1) :=
            fun i => rotateSphere (k + 1) (U i) ∘ equalAreaCapPoint k
          (∀ i, IsOpen (D i) ∧ D i ⊆ Metric.ball 0 rho ∧
            Bornology.IsBounded (D i) ∧ ContinuousOn (F i) (D i) ∧
            Set.InjOn (F i) (D i) ∧ IsOpen (F i '' D i)) ∧
          Pairwise (fun i j => Disjoint (F i '' D i) (F j '' D j)) ∧
          sphericalMeasure (k + 1) (⋃ i, F i '' D i)ᶜ < ENNReal.ofReal eta ∧
          (∀ i E, MeasurableSet E → E ⊆ D i →
            sphericalMeasure (k + 1) (F i '' E) =
              (ENNReal.ofReal (omega (k + 1)))⁻¹ *
                (volume : Measure (Rd (k + 1))) E) ∧
          (∀ i, ∀ x ∈ D i, ∀ y ∈ D i,
            (1 - epsilon) * ‖x - y‖ ≤ chord (k + 1) (F i x) (F i y) ∧
            chord (k + 1) (F i x) (F i y) ≤ (1 + epsilon) * ‖x - y‖) := by
  classical
  obtain ⟨rho, hrho, hsmall, hc, hi, ha, hd⟩ :=
    exists_equalAreaCapPoint_chart k hepsilon hepsilon'
  obtain ⟨delta, hdelta, t, hWopen, hWcover, hWinside⟩ :=
    exists_finite_equalAreaCapPoint_open_cover k hrho
  let W : Problem1.Orthogonal (k + 1) → Set (Sphere (k + 1)) :=
    fun R => rotateSphere (k + 1) R⁻¹ ⁻¹'
      Metric.ball (normalPoint (k + 1) 1 0) delta
  let n := Fintype.card ↥t
  let e : ↥t ≃ Fin n := Fintype.equivFin ↥t
  let U : Fin n → Problem1.Orthogonal (k + 1) := fun i => (e.symm i).val
  let C : Fin n → Set (Sphere (k + 1)) := fun i => W (U i)
  let F : Fin n → Rd (k + 1) → Sphere (k + 1) :=
    fun i => rotateSphere (k + 1) (U i) ∘ equalAreaCapPoint k
  have hCopen : ∀ i, IsOpen (C i) := fun i => hWopen (U i)
  have hCcover : (⋃ i, C i) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    obtain ⟨R, hRt, hyR⟩ := Set.mem_iUnion₂.mp
      (show y ∈ ⋃ R ∈ t, W R from hWcover (Set.mem_univ y))
    refine Set.mem_iUnion.mpr ⟨e ⟨R, hRt⟩, ?_⟩
    simpa only [C, U, Equiv.symm_apply_apply] using hyR
  have hCinside : ∀ i, C i ⊆ F i '' Metric.ball (0 : Rd (k + 1)) rho :=
    fun i => hWinside (U i)
  have hFcont : ∀ i, ContinuousOn (F i) (Metric.ball 0 rho) :=
    fun i => (rotateSphere_isometry (k + 1) (U i)).continuous.comp_continuousOn hc
  have hFinj : ∀ i, Set.InjOn (F i) (Metric.ball 0 rho) :=
    fun i x hx y hy hxy =>
      hi hx hy ((rotateSphere_isometry (k + 1) (U i)).injective hxy)
  letI : CompactSpace (Sphere (k + 1)) :=
    (problem1SphereIsometryEquiv (k + 1)).symm.toHomeomorph.compactSpace
  obtain ⟨D, hD, hdisjoint, hloss⟩ :=
    exists_disjoint_open_chart_domains (sphericalMeasure (k + 1))
      (Metric.ball (0 : Rd (k + 1)) rho) Metric.isOpen_ball n F hFcont
      C hCopen hCcover hCinside heta
  refine ⟨rho, hrho, hsmall, n, U, D, (fun i => ⟨(hD i).1, (hD i).2.1,
    Metric.isBounded_ball.subset (hD i).2.1, (hFcont i).mono (hD i).2.1,
    (hFinj i).mono (hD i).2.1, (hD i).2.2.2⟩), hdisjoint, hloss, ?_, ?_⟩
  · intro i E hE hsub
    rw [Set.image_comp, sphericalMeasure_rotateSphere_image]
    exact ha E hE (hsub.trans (hD i).2.1)
  · intro i x hx y hy
    simpa only [Function.comp_apply, rotateSphere_chord] using
      hd x ((hD i).2.1 hx) y ((hD i).2.1 hy)

end Riesz.Geometry
