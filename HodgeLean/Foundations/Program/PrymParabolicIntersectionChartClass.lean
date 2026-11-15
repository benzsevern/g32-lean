import HodgeLean.Foundations.Program.PrymParabolicIntersectionPlaneClass

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The inverse chart on its open coordinate target, with the marked point removed.
Source: `OpenPartialHomeomorph.right_inv`, maps of point-complement pairs. -/
def hga_chartInversePointPairMap {T : Type} [TopologicalSpace T] (d : ℕ)
    (e : OpenPartialHomeomorph T (Fin d → ℂ)) (y : T) :
    neighborhoodPointComplementPair e.target (e y) ⟶ pointComplementPair y :=
  have hne (w : {w : e.target | w.1 ≠ e y}) : e.symm w.1.1 ≠ y := by
    intro h
    apply w.2
    exact (e.right_inv w.1.2).symm.trans (congrArg e h)
  TopPair.ofHom
    (TopCat.ofHom ⟨fun w ↦ e.symm w.1, e.symm.continuousOn.domRestrict⟩)
    (TopCat.ofHom ⟨fun w ↦ ⟨e.symm w.1.1, hne w⟩,
      (e.symm.continuousOn.domRestrict.comp continuous_subtype_val).subtype_mk hne⟩)
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem hga_chartInverse_radial_comp {T : Type} [TopologicalSpace T] (d : ℕ)
    (e : OpenPartialHomeomorph T (Fin d → ℂ)) (y : T) (hy : y ∈ e.source) :
    radialTargetPointPairMap d e.target (e y) (chartRadius d e y hy)
      (chartRadius_pos d e y hy) (ball_chartRadius_subset d e y hy) 0 (e y)
      (OpenPartialHomeomorph.univBall_apply_zero _ _) ≫
      hga_chartInversePointPairMap d e y = chartModelEmbeddingPair d e y hy := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    apply Subtype.ext
    change e.symm (OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy)
      (z.1 + 0)) = _
    rw [add_zero]
    rfl
  · ext z
    change e.symm (OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy)
      ((show Fin d → ℂ from z) + 0)) = _
    rw [add_zero]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem hga_chartLocalClass_of_coordinate_normalization (R : Type) [CommRing R]
    {T : Type} [TopologicalSpace T] (d : ℕ)
    (e : OpenPartialHomeomorph T (Fin d → ℂ)) (y : T) (hy : y ∈ e.source)
    (D : puncturedPair ℂ d ⟶ neighborhoodPointComplementPair e.target (e y))
    (hD : relativeHomologyMap R (2 * d)
      (neighborhoodPointComplementPairMap e.target (e y))
      (relativeHomologyMap R (2 * d) D (standardComplexLocalClass R d)) =
      relativeHomologyMap R (2 * d)
        (translationPointComplementPairMap (Fin d → ℂ) (e y))
        (standardComplexLocalClass R d)) :
    relativeHomologyMap R (2 * d) (D ≫ hga_chartInversePointPairMap d e y)
      (standardComplexLocalClass R d) = b6m_localClassOfChart R d e y hy := by
  let A := radialTargetPointPairMap d e.target (e y) (chartRadius d e y hy)
    (chartRadius_pos d e y hy) (ball_chartRadius_subset d e y hy) 0 (e y)
    (OpenPartialHomeomorph.univBall_apply_zero _ _)
  have he : relativeHomologyMap R (2 * d) D (standardComplexLocalClass R d) =
      relativeHomologyMap R (2 * d) A (standardComplexLocalClass R d) := by
    apply (b6m_point_excision_bijective R e.target (e y) e.open_target
      (e.map_source hy) (2 * d)).1
    rw [hD]
    exact (b6m_radialTargetPointPairMap_normalization R d e.target (e y)
      (chartRadius d e y hy) (chartRadius_pos d e y hy)
      (ball_chartRadius_subset d e y hy) 0 (e y)
      (OpenPartialHomeomorph.univBall_apply_zero _ _)).symm
  rw [relativeHomologyMap_comp, LinearMap.comp_apply, he,
    ← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  change relativeHomologyMap R (2 * d)
    (_ ≫ hga_chartInversePointPairMap d e y) (standardComplexLocalClass R d) = _
  rw [hga_chartInverse_radial_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem hga_complexScalar_hasFDerivAt (f : ℂ → ℂ) (ρ : ℂ)
    (hf : HasDerivAt f ρ 0) :
    HasFDerivAt (fun z : Fin 1 → ℂ ↦ fun i ↦ f (z i))
      ((Matrix.mulVecLin (fun _ _ : Fin 1 ↦ ρ)).toContinuousLinearMap)
      0 := by
  apply (piHasFDerivAt_iff_normed 1 _ _ _).mpr
  have hd : HasFDerivAt (fun z : Fin 1 → ℂ ↦ fun i ↦ f (z i))
      (ContinuousLinearMap.pi (fun i : Fin 1 ↦
        ρ • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) i)) 0 := by
    apply hasFDerivAt_pi.mpr
    intro i
    have hi := hasFDerivAt_apply (𝕜 := ℂ) i (0 : Fin 1 → ℂ)
    have hs := hf.hasFDerivAt.comp (0 : Fin 1 → ℂ) hi
    convert hs using 1 <;> ext z <;>
      simp [ContinuousLinearMap.comp_apply, smul_eq_mul, mul_comm]
  convert hd using 1
  ext z i
  simp [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  exact Or.inl (congrArg z (Subsingleton.elim _ _))

/-- A scalar map acting on the one-coordinate punctured complex plane.
Source: `complexPuncturedPairMapOf`. -/
def hga_complexScalarPairMap (f : C(ℂ, ℂ))
    (hne : ∀ z, z ≠ 0 → f z ≠ 0) : puncturedPair ℂ 1 ⟶ puncturedPair ℂ 1 :=
  complexPuncturedPairMapOf 1 (fun z i ↦ f (z i))
    (by apply continuous_pi; intro i; exact f.continuous.comp (continuous_apply i))
    (by
      intro z hz h
      apply hz
      funext i
      by_contra hi
      exact hne (z i) hi (congrFun h i))

set_option backward.isDefEq.respectTransparency false in
theorem hga_complexScalar_preservesLocalClass (R : Type) [CommRing R]
    (f : C(ℂ, ℂ)) (hne : ∀ z, z ≠ 0 → f z ≠ 0) (hf0 : f 0 = 0)
    (ρ : ℂ) (hρ : ρ ≠ 0) (hf : HasDerivAt f ρ 0) :
    relativeHomologyMap R 2 (hga_complexScalarPairMap f hne)
      (standardComplexLocalClass R 1) = standardComplexLocalClass R 1 := by
  exact b6m_complexDifferentiable_preserves_localClass R 1 (fun _ _ ↦ ρ)
    (by simpa only [Matrix.det_fin_one] using hρ)
    (fun z i ↦ f (z i))
    (by apply continuous_pi; intro i; exact f.continuous.comp (continuous_apply i))
    (by funext i; exact hf0)
    (by
      intro z hz h
      apply hz
      funext i
      by_contra hi
      exact hne (z i) hi (congrFun h i))
    (hga_complexScalar_hasFDerivAt f ρ hf)

theorem hga_continuous_triangleChartCoordinate {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T))
    (e : OpenPartialHomeomorph T (Fin 1 → ℂ)) (hs : ∀ a, σ a ∈ e.source) :
    Continuous (fun w : ℂ ↦ e (hga_triangleExtension σ w)) := by
  exact e.continuousOn.comp_continuous (hga_triangleExtension σ).continuous
    (fun w ↦ hs (hga_triangleRetraction w))

theorem hga_triangleChartCoordinate_center_iff {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3)
    (e : OpenPartialHomeomorph T (Fin 1 → ℂ)) (hs : ∀ a, σ a ∈ e.source)
    (w : ℂ) : e (hga_triangleExtension σ w) = e (σ b) ↔ w = 0 := by
  constructor
  · intro h
    have hx : hga_triangleExtension σ w ∈ e.source := hs (hga_triangleRetraction w)
    exact (hga_triangleExtension_barycentre_iff σ hσ b hb w).mp (e.injOn hx (hs b) h)
  · intro h
    exact congrArg e ((hga_triangleExtension_barycentre_iff σ hσ b hb w).mpr h)

/-- The extended triangle as a map into the punctured open chart target.
Source: `hga_continuous_triangleChartCoordinate`, `hga_triangleChartCoordinate_center_iff`. -/
def hga_triangleChartPairMap {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3)
    (e : OpenPartialHomeomorph T (Fin 1 → ℂ)) (hs : ∀ a, σ a ∈ e.source) :
    puncturedPair ℂ 1 ⟶ neighborhoodPointComplementPair e.target (e (σ b)) := by
  have hc := hga_continuous_triangleChartCoordinate σ e hs
  have hm (z : Fin 1 → ℂ) : e (hga_triangleExtension σ (z 0)) ∈ e.target :=
    e.map_source (hs (hga_triangleRetraction (z 0)))
  have hn (z : ({0}ᶜ : Set (Fin 1 → ℂ))) :
      e (hga_triangleExtension σ (z.1 0)) ≠ e (σ b) := by
    intro h
    have hz := (hga_triangleChartCoordinate_center_iff σ hσ b hb e hs (z.1 0)).mp h
    apply z.2
    funext i
    exact (congrArg z.1 (Subsingleton.elim i 0)).trans hz
  refine TopPair.ofHom (X := puncturedPair ℂ 1)
    (Y := neighborhoodPointComplementPair e.target (e (σ b)))
    (TopCat.ofHom ⟨fun z ↦ ⟨e (hga_triangleExtension σ (z 0)), hm z⟩, ?_⟩)
    (TopCat.ofHom ⟨fun z ↦ ⟨⟨e (hga_triangleExtension σ (z.1 0)), hm z.1⟩, hn z⟩, ?_⟩)
    rfl
  · apply Continuous.subtype_mk
    exact hc.comp (continuous_apply 0)
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact hc.comp ((continuous_apply 0).comp continuous_subtype_val)

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangleChart_normalization (R : Type) [CommRing R]
    {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3)
    (e : OpenPartialHomeomorph T (Fin 1 → ℂ)) (hs : ∀ a, σ a ∈ e.source)
    (ρ : ℂ) (hρ : ρ ≠ 0)
    (hd : HasDerivAt (fun w : ℂ ↦ e (hga_triangleExtension σ w) 0) ρ 0) :
    relativeHomologyMap R 2 (neighborhoodPointComplementPairMap e.target (e (σ b)))
      (relativeHomologyMap R 2 (hga_triangleChartPairMap σ hσ b hb e hs)
        (standardComplexLocalClass R 1)) =
      relativeHomologyMap R 2 (translationPointComplementPairMap (Fin 1 → ℂ) (e (σ b)))
        (standardComplexLocalClass R 1) := by
  let f : C(ℂ, ℂ) := ⟨fun w ↦ e (hga_triangleExtension σ w) 0 - e (σ b) 0,
    (((continuous_apply 0).comp (hga_continuous_triangleChartCoordinate σ e hs)).sub
      continuous_const)⟩
  have hne : ∀ w, w ≠ 0 → f w ≠ 0 := by
    intro w hw hf
    have he : e (hga_triangleExtension σ w) = e (σ b) := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact sub_eq_zero.mp hf
    exact hw ((hga_triangleChartCoordinate_center_iff σ hσ b hb e hs w).mp he)
  have hf0 : f 0 = 0 := by
    have h0 := (hga_triangleChartCoordinate_center_iff σ hσ b hb e hs 0).mpr rfl
    change e (hga_triangleExtension σ 0) 0 - e (σ b) 0 = 0
    rw [h0, sub_self]
  have hmaps : relativeHomologyMap R 2
      (hga_triangleChartPairMap σ hσ b hb e hs ≫
        neighborhoodPointComplementPairMap e.target (e (σ b))) =
      relativeHomologyMap R 2 (hga_complexScalarPairMap f hne ≫
        translationPointComplementPairMap (Fin 1 → ℂ) (e (σ b))) := by
    apply hga_local_maps_eq_of_eventuallyEq R (e (σ b)) 1 2
    apply Filter.Eventually.of_forall
    intro z
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change e (hga_triangleExtension σ (z 0)) 0 =
      (e (hga_triangleExtension σ (z 0)) 0 - e (σ b) 0) + e (σ b) 0
    ring
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hmaps,
    relativeHomologyMap_comp, LinearMap.comp_apply,
    hga_complexScalar_preservesLocalClass R f hne hf0 ρ hρ (hd.sub_const _)]

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangleExtension_chartLocalClass (R : Type) [CommRing R]
    {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3)
    (e : OpenPartialHomeomorph T (Fin 1 → ℂ)) (hs : ∀ a, σ a ∈ e.source)
    (ρ : ℂ) (hρ : ρ ≠ 0)
    (hd : HasDerivAt (fun w : ℂ ↦ e (hga_triangleExtension σ w) 0) ρ 0) :
    relativeHomologyMap R 2
      (hga_complexLinePairIso.hom ≫ hga_triangleExtension_pairMap σ hσ b hb)
      (standardComplexLocalClass R 1) = b6m_localClassOfChart R 1 e (σ b) (hs b) := by
  have hm : relativeHomologyMap R 2
      (hga_triangleChartPairMap σ hσ b hb e hs ≫ hga_chartInversePointPairMap 1 e (σ b)) =
      relativeHomologyMap R 2
        (hga_complexLinePairIso.hom ≫ hga_triangleExtension_pairMap σ hσ b hb) := by
    apply hga_local_maps_eq_of_eventuallyEq R (σ b) 1 2
    apply Filter.Eventually.of_forall
    intro z
    change e.symm (e (hga_triangleExtension σ (z 0))) = hga_triangleExtension σ (z 0)
    exact e.left_inv (hs (hga_triangleRetraction (z 0)))
  have hclass := hga_chartLocalClass_of_coordinate_normalization R 1 e (σ b) (hs b)
    (hga_triangleChartPairMap σ hσ b hb e hs)
    (hga_triangleChart_normalization R σ hσ b hb e hs ρ hρ hd)
  rw [hm] at hclass
  exact hclass

set_option backward.isDefEq.respectTransparency false in
theorem hga_affineTriangle_localClass {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3)
    (e : OpenPartialHomeomorph T (Fin 1 → ℂ)) (hs : ∀ a, σ a ∈ e.source)
    (v : ℂ) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hform : ∀ a, e (σ a) 0 = v + (ρ : ℂ) *
      (((a.weights 1 : ℝ) : ℂ) + ((a.weights 2 : ℝ) : ℂ) * Complex.I)) :
    let P := pointComplementPair (σ b)
    let z : LinearMap.ker (((relativeChainFunctor ℤ).obj P).sc 2).g.hom :=
      ⟨((relativeChainProjection ℤ P).f 2).hom
        (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ)),
        hga_triangle_relative_cycle σ (σ b)
          (hga_triangle_face_ne_interior σ hσ b (by intro i; rw [hb]; norm_num))⟩
    (((relativeChainFunctor ℤ).obj P).sc 2).moduleCatHomologyClass z =
      b6m_localClassOfChart ℤ 1 e (σ b) (hs b) := by
  exact (hga_triangle_localClass σ hσ b hb).trans
    (hga_triangleExtension_chartLocalClass ℤ σ hσ b hb e hs (ρ : ℂ)
      (by exact_mod_cast hρ)
      (hga_triangleExtension_hasDerivAt σ (fun x ↦ e x 0) v ρ hform))

theorem hga_complexChart_deriv_ne_zero (e : OpenPartialHomeomorph ℂ ℂ)
    (x : ℂ) (hx : x ∈ e.source)
    (hf : DifferentiableAt ℂ e x) (hg : DifferentiableAt ℂ e.symm (e x)) :
    deriv e x ≠ 0 := by
  have hc := hg.hasDerivAt.comp x hf.hasDerivAt
  have hi : HasDerivAt (fun z : ℂ ↦ e.symm (e z)) 1 x :=
    (hasDerivAt_id x).congr_of_eventuallyEq (e.eventually_left_inverse hx)
  have hp := hc.unique hi
  intro h
  rw [h, mul_zero] at hp
  exact zero_ne_one hp

theorem hga_atlas_transition_hasDerivAt {T : Type} [TopologicalSpace T]
    [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) 1 T]
    (e e' : OpenPartialHomeomorph T ℂ) (he : e ∈ atlas ℂ T) (he' : e' ∈ atlas ℂ T)
    (x : T) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧ HasDerivAt (fun z : ℂ ↦ e' (e.symm z)) ρ (e x) := by
  let A := e.symm.trans e'
  have hA : A ∈ contDiffGroupoid 1 𝓘(ℂ, ℂ) :=
    IsManifold.compatible_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he')
  have hAx : e x ∈ A.source := by
    change e x ∈ e.target ∧ e.symm (e x) ∈ e'.source
    exact ⟨e.map_source hx, by simpa only [e.left_inv hx] using hx'⟩
  have hf : DifferentiableAt ℂ A (e x) :=
    (((contMDiffOn_of_mem_contDiffGroupoid hA).contDiffOn).contDiffAt
      (A.open_source.mem_nhds hAx)).differentiableAt (by norm_num)
  have hg : DifferentiableAt ℂ A.symm (A (e x)) :=
    (((contMDiffOn_of_mem_contDiffGroupoid
      ((contDiffGroupoid 1 𝓘(ℂ, ℂ)).symm hA)).contDiffOn).contDiffAt
      (A.open_target.mem_nhds (A.map_source hAx))).differentiableAt (by norm_num)
  exact ⟨deriv A (e x), hga_complexChart_deriv_ne_zero A (e x) hAx hf hg,
    hf.hasDerivAt⟩

/-- A scalar complex chart written in the finite-coordinate model of local homology.
Source: `b6m_surfaceCoordinateEquiv`. -/
def hga_complexCoordinateChart {T : Type} [TopologicalSpace T]
    (e : OpenPartialHomeomorph T ℂ) : OpenPartialHomeomorph T (Fin 1 → ℂ) :=
  e.trans b6m_surfaceCoordinateEquiv.toHomeomorph.toOpenPartialHomeomorph

theorem hga_complexCoordinateChart_source {T : Type} [TopologicalSpace T]
    (e : OpenPartialHomeomorph T ℂ) : (hga_complexCoordinateChart e).source = e.source := by
  simp [hga_complexCoordinateChart, OpenPartialHomeomorph.trans_source]

set_option backward.isDefEq.respectTransparency false in
theorem hga_atlas_localClass_eq (R : Type) [CommRing R]
    {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) 1 T]
    (e e' : OpenPartialHomeomorph T ℂ) (he : e ∈ atlas ℂ T) (he' : e' ∈ atlas ℂ T)
    (x : T) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    b6m_localClassOfChart R 1 (hga_complexCoordinateChart e) x
      (by simpa only [hga_complexCoordinateChart_source] using hx) =
    b6m_localClassOfChart R 1 (hga_complexCoordinateChart e') x
      (by simpa only [hga_complexCoordinateChart_source] using hx') := by
  obtain ⟨ρ, hρ, hraw⟩ := hga_atlas_transition_hasDerivAt e e' he he' x hx hx'
  let E := b6m_surfaceCoordinateEquiv
  let A : ℂ →L[ℂ] ℂ := ContinuousLinearMap.toSpanSingleton ℂ ρ
  let L := E.toContinuousLinearMap.comp (A.comp E.symm.toContinuousLinearMap)
  have hA : Function.Injective A := by
    intro a b hab
    change a * ρ = b * ρ at hab
    exact mul_right_cancel₀ hρ hab
  have hL : Function.Injective L := E.injective.comp (hA.comp E.symm.injective)
  have hraw' : HasFDerivAt (fun z : ℂ ↦ e' (e.symm z)) A (E.symm (E (e x))) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hraw.hasFDerivAt
  have hderiv := E.hasFDerivAt.comp (E (e x))
    (hraw'.comp (E (e x)) E.symm.hasFDerivAt)
  apply b6m_localClassOfChart_eq_of_hasFDerivAt_transition R 1
    (hga_complexCoordinateChart e) (hga_complexCoordinateChart e') x _ _ L hL
  apply (piHasFDerivAt_iff_normed 1 _ L _).mpr
  exact hderiv

theorem hga_atlas_localClass_surface (R : Type) [CommRing R]
    {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) 1 T]
    (e : OpenPartialHomeomorph T ℂ) (he : e ∈ atlas ℂ T)
    (x : T) (hx : x ∈ e.source) :
    b6m_localClassOfChart R 1 (hga_complexCoordinateChart e) x
      (by simpa only [hga_complexCoordinateChart_source] using hx) =
      b6m_surfaceLocalClass R x := by
  exact hga_atlas_localClass_eq R e (chartAt ℂ x) he (chart_mem_atlas ℂ x)
    x hx (mem_chart_source ℂ x)

set_option backward.isDefEq.respectTransparency false in
theorem hga_affineTriangle_surfaceLocalClass
    {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) 1 T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3)
    (e : OpenPartialHomeomorph T ℂ) (he : e ∈ atlas ℂ T) (hs : ∀ a, σ a ∈ e.source)
    (v : ℂ) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hform : ∀ a, e (σ a) = v + (ρ : ℂ) *
      (((a.weights 1 : ℝ) : ℂ) + ((a.weights 2 : ℝ) : ℂ) * Complex.I)) :
    let P := pointComplementPair (σ b)
    let z : LinearMap.ker (((relativeChainFunctor ℤ).obj P).sc 2).g.hom :=
      ⟨((relativeChainProjection ℤ P).f 2).hom
        (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ)),
        hga_triangle_relative_cycle σ (σ b)
          (hga_triangle_face_ne_interior σ hσ b (by intro i; rw [hb]; norm_num))⟩
    (((relativeChainFunctor ℤ).obj P).sc 2).moduleCatHomologyClass z =
      b6m_surfaceLocalClass ℤ (σ b) := by
  have hs' : ∀ a, σ a ∈ (hga_complexCoordinateChart e).source := by
    intro a
    simpa only [hga_complexCoordinateChart_source] using hs a
  exact (hga_affineTriangle_localClass σ hσ b hb (hga_complexCoordinateChart e)
    hs' v ρ hρ hform).trans (hga_atlas_localClass_surface ℤ e he (σ b) (hs b))

set_option backward.isDefEq.respectTransparency false in
theorem hga_fundChain_relative_cycle {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap b4b_root T) (y : T) :
    let P := pointComplementPair y
    (((relativeChainFunctor ℤ).obj P).sc 2).g.hom
      (((relativeChainProjection ℤ P).f 2).hom (hga_fundChain F)) = 0 := by
  intro P
  let K := (relativeChainFunctor ℤ).obj P
  change (K.d 2 ((ComplexShape.down ℕ).next 2)).hom _ = 0
  rw [ChainComplex.next_nat_succ 1]
  have hd := ConcreteCategory.congr_hom ((relativeChainProjection ℤ P).comm 2 1)
    (hga_fundChain F)
  change (K.d 2 1).hom (((relativeChainProjection ℤ P).f 2).hom (hga_fundChain F)) =
    ((relativeChainProjection ℤ P).f 1).hom
      (((SingularChainComplex ℤ (TopCat.of T)).d 2 1).hom (hga_fundChain F)) at hd
  rw [hd, hga_d_fundChain F 1, map_zero]

set_option backward.isDefEq.respectTransparency false in
theorem hga_fundClass_pointProjection {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap b4b_root T) (y : T) :
    let P := pointComplementPair y
    (relativeHomologyProjection ℤ P 2).hom (hga_fundClass F) =
      (((relativeChainFunctor ℤ).obj P).sc 2).moduleCatHomologyClass
        ⟨((relativeChainProjection ℤ P).f 2).hom (hga_fundChain F),
          hga_fundChain_relative_cycle F y⟩ := by
  intro P
  exact ShortComplex.moduleCatHomologyClass_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
      (relativeChainProjection ℤ P))
    ⟨hga_fundChain F, hga_d_fundChain F _⟩

set_option backward.isDefEq.respectTransparency false in
theorem hga_orientation_boundary_of_local_projection
    {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) 1 T]
    (F : hg8_DeltaMap b4b_root T)
    (σ : C(StdSimplex ℝ (Fin 3), T)) (b : StdSimplex ℝ (Fin 3))
    (hb : ∀ i, b.weights i = 1 / 3)
    (e : OpenPartialHomeomorph T ℂ) (he : e ∈ atlas ℂ T) (hs : ∀ a, σ a ∈ e.source)
    (v : ℂ) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hform : ∀ a, e (σ a) = v + (ρ : ℂ) *
      (((a.weights 1 : ℝ) : ℂ) + ((a.weights 2 : ℝ) : ℂ) * Complex.I))
    (hy : (relativeHomologyProjection ℤ (pointComplementPair (σ b)) 2).hom
      (hga_fundClass F) = -b6m_surfaceLocalClass ℤ (σ b)) :
    ∃ (w : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 3)
      (u : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of ({σ b}ᶜ : Set T))) 2),
      hga_fundChain F + Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ) =
        Simplicial.boundary ℤ 2 w + hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 2 u := by
  let P := pointComplementPair (σ b)
  let K := (relativeChainFunctor ℤ).obj P
  have hσ := hga_affine_triangle_injective σ e v ρ hρ hform
  have hcF := hga_fundChain_relative_cycle F (σ b)
  have hcS := hga_triangle_relative_cycle σ (σ b)
    (hga_triangle_face_ne_interior σ hσ b (by intro i; rw [hb]; norm_num))
  let zF : LinearMap.ker (K.sc 2).g.hom :=
    ⟨((relativeChainProjection ℤ P).f 2).hom (hga_fundChain F), hcF⟩
  let zS : LinearMap.ker (K.sc 2).g.hom :=
    ⟨((relativeChainProjection ℤ P).f 2).hom
      (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ)), hcS⟩
  have hF : (K.sc 2).moduleCatHomologyClass zF = -b6m_surfaceLocalClass ℤ (σ b) :=
    (hga_fundClass_pointProjection F (σ b)).symm.trans hy
  have hS : (K.sc 2).moduleCatHomologyClass zS = b6m_surfaceLocalClass ℤ (σ b) :=
    hga_affineTriangle_surfaceLocalClass σ hσ b hb e he hs v ρ hρ hform
  have hc : (K.sc 2).g.hom (((relativeChainProjection ℤ P).f 2).hom
      (hga_fundChain F + Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ))) = 0 := by
    rw [map_add, map_add, hcF, hcS, add_zero]
  apply hga_point_boundary_of_relative_class_zero (σ b) _ hc
  have hz : (⟨((relativeChainProjection ℤ P).f 2).hom
      (hga_fundChain F + Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ)), hc⟩ :
      LinearMap.ker (K.sc 2).g.hom) = zF + zS := by
    apply Subtype.ext
    exact map_add _ _ _
  rw [hz, map_add, hF, hS, neg_add_cancel]

#print axioms hga_chartInversePointPairMap

#print axioms hga_chartInverse_radial_comp

#print axioms hga_chartLocalClass_of_coordinate_normalization

#print axioms hga_complexScalar_hasFDerivAt

#print axioms hga_complexScalarPairMap
#print axioms hga_complexScalar_preservesLocalClass

#print axioms hga_continuous_triangleChartCoordinate

#print axioms hga_triangleChartCoordinate_center_iff

#print axioms hga_triangleChartPairMap

#print axioms hga_triangleChart_normalization

#print axioms hga_triangleExtension_chartLocalClass

#print axioms hga_affineTriangle_localClass

#print axioms hga_complexChart_deriv_ne_zero

#print axioms hga_atlas_transition_hasDerivAt

#print axioms hga_complexCoordinateChart
#print axioms hga_complexCoordinateChart_source

#print axioms hga_atlas_localClass_eq

#print axioms hga_atlas_localClass_surface

#print axioms hga_affineTriangle_surfaceLocalClass

#print axioms hga_fundChain_relative_cycle

#print axioms hga_fundClass_pointProjection

#print axioms hga_orientation_boundary_of_local_projection

end HodgeLean.Foundations.Program
