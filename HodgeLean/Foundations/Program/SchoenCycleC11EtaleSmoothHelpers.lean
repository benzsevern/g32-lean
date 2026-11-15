import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeLean.Foundations.Program.SchoenCycleC11CoverAssemblyHelpers
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension
import Mathlib.Topology.Maps.Proper.Basic

/-! # Etale coordinates over smooth complex bases
Explicit section-algebra transport for analytic local inverses.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback on affine sections preserves the actual complex algebra structures.
Source: Mathlib, Scheme.Hom.appLE_comp_appLE; upstream overSpecAlgebra. -/
def s2e_c11_section_algHom
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (U : Y.left.Opens) (V : X.left.Opens) (e : V ≤ f.left ⁻¹ᵁ U) :
    Γ(Y.left, U) →ₐ[ℂ] Γ(X.left, V) where
  toRingHom := (f.left.appLE U V e).hom
  commutes' z := by
    change (f.left.appLE U V e)
      ((Y.hom.appLE ⊤ U (by simp)) ((Scheme.ΓSpecIso ↧ℂ).inv z)) =
      (X.hom.appLE ⊤ V (by simp)) ((Scheme.ΓSpecIso ↧ℂ).inv z)
    have hmap : Y.hom.appLE ⊤ U (by simp) ≫ f.left.appLE U V e =
        X.hom.appLE ⊤ V (by simp) := by
      rw [Scheme.Hom.appLE_comp_appLE, Over.w f]
    exact congrArg (fun g : Γ(Spec ↧ℂ, ⊤) ⟶ Γ(X.left, V) ↦
      g ((Scheme.ΓSpecIso ↧ℂ).inv z)) hmap

/-- Etale pullback preserves the specified smooth relative dimension.
Source: Mathlib, smoothOfRelativeDimension_comp and Etale.iff_smoothOfRelativeDimension_zero. -/
theorem s2e_c11_etale_smooth_relative_dimension
    (d : ℕ) (X Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension d Y.hom]
    (f : X ⟶ Y) [Etale f.left] : SmoothOfRelativeDimension d X.hom := by
  rw [← Over.w f]
  simpa only [Nat.zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + d) (f.left ≫ Y.hom))

/-- Pull back an affine etale coordinate neighbourhood through the actual finite etale map.
Source: Mathlib, Etale.etale_appLE and stability of etale ring maps under composition. -/
def s2e_c11_pullback_local_etale_coordinates
    (d : ℕ) (X Y : Over (Spec ↧ℂ))
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] (x : X.left)
    (D : LocalEtaleCoordinates Y d (f.left x)) : LocalEtaleCoordinates X d x where
  neighborhood := f.left ⁻¹ᵁ D.neighborhood
  isAffine := D.isAffine.preimage f.left
  mem := D.mem
  coordinateAlgHom := (s2e_c11_section_algHom X Y f D.neighborhood
    (f.left ⁻¹ᵁ D.neighborhood) le_rfl).comp D.coordinateAlgHom
  etale := RingHom.Etale.stableUnderComposition _ _ D.etale
    (f.left.etale_appLE D.isAffine (D.isAffine.preimage f.left) le_rfl)

/-- An etale coordinate morphism factors through the sections on its actual neighbourhood.
Source: Mathlib, Scheme.Opens.toSpecΓ and Spec.map_comp. -/
theorem s2e_c11_etale_coordinate_toAffineSpace
    (d : ℕ) (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension d X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X d x) :
    D.toAffineSpace = D.neighborhood.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom D.coordinateAlgHom.toRingHom) ≫
      (AffineSpace.SpecIso (Fin d) ↧ℂ).inv := by
  unfold LocalEtaleCoordinates.toAffineSpace Scheme.Opens.toSpecΓ
  rw [Category.assoc, ← Spec.map_comp_assoc]
  rfl

/-- Pullback coordinate morphisms commute with the actual restricted scheme map.
Source: Mathlib, Scheme.Opens.toSpecΓ_naturality; construction of etale pullback coordinates. -/
theorem s2e_c11_pullback_coordinate_toAffineSpace
    (d : ℕ) (X Y : Over (Spec ↧ℂ))
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] (x : X.left)
    (D : LocalEtaleCoordinates Y d (f.left x)) :
    (s2e_c11_pullback_local_etale_coordinates d X Y f x D).toAffineSpace =
      (f.left ∣_ D.neighborhood) ≫ D.toAffineSpace := by
  rw [s2e_c11_etale_coordinate_toAffineSpace, s2e_c11_etale_coordinate_toAffineSpace]
  change (f.left ⁻¹ᵁ D.neighborhood).toSpecΓ ≫ Spec.map
      (CommRingCat.ofHom (((s2e_c11_section_algHom X Y f D.neighborhood
        (f.left ⁻¹ᵁ D.neighborhood) le_rfl).comp D.coordinateAlgHom).toRingHom)) ≫ _ = _
  rw [← Scheme.Opens.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc]
  congr 2
  apply congrArg Spec.map
  apply ConcreteCategory.hom_ext
  intro a
  change (f.left.appLE D.neighborhood (f.left ⁻¹ᵁ D.neighborhood) le_rfl)
    (D.coordinateAlgHom a) = (f.left.app D.neighborhood) (D.coordinateAlgHom a)
  rw [← Scheme.Hom.app_eq_appLE]

/-- The actual analytic coordinates of an etale neighbourhood are local homeomorphisms.
Source: Upstream LocalEtaleCoordinates.ambientProjectionChart and its coordinate equation. -/
theorem s2e_c11_etale_analytic_coordinates_local_homeomorph
    (d : ℕ) (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension d X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X d x) :
    IsLocalHomeomorph D.analyticCoordinates := by
  have hamb : IsLocalHomeomorph D.ambientAnalyticCoordinates := by
    apply IsLocalHomeomorph.mk
    intro z
    exact ⟨D.ambientProjectionChart z, D.mem_ambientProjectionChart_source z,
      fun y hy ↦ (D.ambientProjectionChart_apply_of_mem z y hy).symm⟩
  have hh := hamb.comp (openHomeomorph X D.neighborhood).isLocalHomeomorph
  convert hh using 1
  funext z
  change D.analyticCoordinates z =
    D.analyticCoordinates ((openEquiv X D.neighborhood).symm ((openEquiv X D.neighborhood) z))
  exact congrArg D.analyticCoordinates ((openEquiv X D.neighborhood).symm_apply_apply z).symm

/-- Restriction to a base open, bundled over the complex base. -/
def s2e_c11_restricted_over_morphism
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (U : Y.left.Opens) :
    openScheme X (f.left ⁻¹ᵁ U) ⟶ openScheme Y U :=
  Over.homMk (f.left ∣_ U) (by
    change (f.left ∣_ U) ≫ (U.ι ≫ Y.hom) = (f.left ⁻¹ᵁ U).ι ≫ X.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w f])

/-- The restricted over-morphism has the original inclusion square.
Source: Mathlib, morphismRestrict_ι. -/
theorem s2e_c11_restricted_over_morphism_inclusion
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (U : Y.left.Opens) :
    s2e_c11_restricted_over_morphism X Y f U ≫ openInclusion Y U =
      openInclusion X (f.left ⁻¹ᵁ U) ≫ f := by
  apply Over.OverMorphism.ext
  exact morphismRestrict_ι f.left U

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The analytic coordinate tuples commute with the actual restricted point map.
Source: Upstream LocalEtaleCoordinates.analyticCoordinates and scheme-coordinate naturality. -/
theorem s2e_c11_pullback_analytic_coordinates
    (d : ℕ) (X Y : Over (Spec ↧ℂ))
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] (x : X.left)
    (D : LocalEtaleCoordinates Y d (f.left x)) :
    (s2e_c11_pullback_local_etale_coordinates d X Y f x D).analyticCoordinates =
      D.analyticCoordinates ∘ Point.map (s2e_c11_restricted_over_morphism X Y f D.neighborhood) := by
  let E := s2e_c11_pullback_local_etale_coordinates d X Y f x D
  have heq : s2e_c11_restricted_over_morphism X Y f D.neighborhood ≫
      D.toAffineSpaceOver = E.toAffineSpaceOver := by
    apply Over.OverMorphism.ext
    exact (s2e_c11_pullback_coordinate_toAffineSpace d X Y f x D).symm
  funext z
  change affineSpaceEquiv (Fin d) (Point.map E.toAffineSpaceOver z) =
    affineSpaceEquiv (Fin d) (Point.map D.toAffineSpaceOver
      (Point.map (s2e_c11_restricted_over_morphism X Y f D.neighborhood) z))
  rw [← Point.map_comp_apply, heq]

/-- On a pulled-back coordinate neighbourhood the actual point map is a local homeomorphism.
Source: Mathlib, IsLocalHomeomorph.of_comp; upstream etale analytic coordinate charts. -/
theorem s2e_c11_restricted_etale_local_homeomorph
    (d : ℕ) (X Y : Over (Spec ↧ℂ))
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] (x : X.left)
    (D : LocalEtaleCoordinates Y d (f.left x)) :
    IsLocalHomeomorph (Point.map (s2e_c11_restricted_over_morphism X Y f D.neighborhood)) := by
  have hcomp : IsLocalHomeomorph (D.analyticCoordinates ∘
      Point.map (s2e_c11_restricted_over_morphism X Y f D.neighborhood)) := by
    rw [← s2e_c11_pullback_analytic_coordinates d X Y f x D]
    exact s2e_c11_etale_analytic_coordinates_local_homeomorph d X x _
  exact hcomp.of_comp (s2e_c11_etale_analytic_coordinates_local_homeomorph d Y (f.left x) D)
    (Point.continuous_map _)

/-- Local inverses on a scheme restriction transport to the exact analytic preimage restriction.
Source: Upstream ComplexPoint.openHomeomorph; Mathlib, composition of local homeomorphisms. -/
theorem s2e_c11_restricted_point_local_homeomorph
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (U : Y.left.Opens)
    (hf : IsLocalHomeomorph (Point.map (s2e_c11_restricted_over_morphism X Y f U))) :
    IsLocalHomeomorph ((Point.overOpen U).restrictPreimage (Point.map f)) := by
  have heq : (Point.map f) ⁻¹' Point.overOpen U = Point.overOpen (f.left ⁻¹ᵁ U) := by
    ext z
    exact Point.mem_overOpen_map_iff f z U
  let eX : Point ℂ (openScheme X (f.left ⁻¹ᵁ U)) ≃ₜ
      (Point.map f) ⁻¹' Point.overOpen U :=
    (openHomeomorph X (f.left ⁻¹ᵁ U)).trans (Homeomorph.setCongr heq.symm)
  let eY := openHomeomorph Y U
  have hsquare (z : Point ℂ (openScheme X (f.left ⁻¹ᵁ U))) :
      (eY (Point.map (s2e_c11_restricted_over_morphism X Y f U) z)).1 =
        Point.map f (eX z).1 := by
    change Point.map (openInclusion Y U)
      (Point.map (s2e_c11_restricted_over_morphism X Y f U) z) =
      Point.map f (Point.map (openInclusion X (f.left ⁻¹ᵁ U)) z)
    rw [← Point.map_comp_apply, ← Point.map_comp_apply,
      s2e_c11_restricted_over_morphism_inclusion]
  have hh := eY.isLocalHomeomorph.comp (hf.comp eX.symm.isLocalHomeomorph)
  convert hh using 1
  funext z
  apply Subtype.ext
  have h := hsquare (eX.symm z)
  rw [eX.apply_symm_apply] at h
  exact h.symm

/-- Source open neighbourhoods suffice to test the local homeomorphism property.
Source: Mathlib, OpenPartialHomeomorph.lift_openEmbedding. -/
theorem s2e_c11_local_homeomorph_of_source_opens
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] (f : E → B)
    (h : ∀ x, ∃ s : Set E, x ∈ s ∧ IsOpen s ∧ IsLocalHomeomorph (s.domRestrict f)) :
    IsLocalHomeomorph f := by
  apply IsLocalHomeomorph.mk
  intro x
  have : Nonempty B := ⟨f x⟩
  obtain ⟨s, hx, hs, hf⟩ := h x
  obtain ⟨e, he, heq⟩ := hf ⟨x, hx⟩
  refine ⟨e.lift_openEmbedding hs.isOpenEmbedding_subtypeVal, ⟨⟨x, hx⟩, he, rfl⟩, ?_⟩
  rintro z ⟨w, hw, rfl⟩
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  exact congrFun heq w

/-- Finite etale maps over smooth pure-dimensional complex bases induce analytic local homeomorphisms.
Source: Hartshorne, Algebraic Geometry, Appendix B; upstream etale polynomial-coordinate charts. -/
theorem s2e_c11_finite_etale_local_homeomorph_over_smooth
    (d : ℕ) (X Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension d Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] :
    IsLocalHomeomorph (Point.map f) := by
  have : SmoothOfRelativeDimension d X.hom := s2e_c11_etale_smooth_relative_dimension d X Y f
  apply s2e_c11_local_homeomorph_of_source_opens
  intro z
  let D := AlgebraicGeometry.localEtaleCoordinates Y d (f.left z.underlying)
  let U : Set (Point ℂ Y) := Point.overOpen D.neighborhood
  have hU : IsOpen U := Point.isOpen_overOpen D.neighborhood
  have hz : z ∈ (Point.map f) ⁻¹' U := by
    change f.left z.underlying ∈ D.neighborhood
    exact D.mem
  have hrest : IsLocalHomeomorph (U.restrictPreimage (Point.map f)) :=
    s2e_c11_restricted_point_local_homeomorph X Y f D.neighborhood
      (s2e_c11_restricted_etale_local_homeomorph d X Y f z.underlying D)
  refine ⟨(Point.map f) ⁻¹' U, hz, hU.preimage (Point.continuous_map f), ?_⟩
  exact hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp hrest

/-- Finite etale maps to the actual projective scheme have analytic local inverses.
Source: Hartshorne, Algebraic Geometry, Appendix B; projective smooth relative dimension. -/
theorem s2e_c11_projective_finite_etale_local_homeomorph
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (f : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite f.left] [Etale f.left] : IsLocalHomeomorph (Point.map f) := by
  have : SmoothOfRelativeDimension k
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
    s0_complex_projective_relative_dimension k
  exact s2e_c11_finite_etale_local_homeomorph_over_smooth k W _ f

/-- Properness on a scheme restriction transports to the exact analytic preimage restriction.
Source: Upstream ComplexPoint.openHomeomorph; Mathlib, properness under composition with homeomorphisms. -/
theorem s2e_c11_restricted_point_proper
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (U : Y.left.Opens)
    (hf : IsProperMap (Point.map (s2e_c11_restricted_over_morphism X Y f U))) :
    IsProperMap ((Point.overOpen U).restrictPreimage (Point.map f)) := by
  have heq : (Point.map f) ⁻¹' Point.overOpen U = Point.overOpen (f.left ⁻¹ᵁ U) := by
    ext z
    exact Point.mem_overOpen_map_iff f z U
  let eX : Point ℂ (openScheme X (f.left ⁻¹ᵁ U)) ≃ₜ
      (Point.map f) ⁻¹' Point.overOpen U :=
    (openHomeomorph X (f.left ⁻¹ᵁ U)).trans (Homeomorph.setCongr heq.symm)
  let eY := openHomeomorph Y U
  have hsquare (z : Point ℂ (openScheme X (f.left ⁻¹ᵁ U))) :
      (eY (Point.map (s2e_c11_restricted_over_morphism X Y f U) z)).1 =
        Point.map f (eX z).1 := by
    change Point.map (openInclusion Y U)
      (Point.map (s2e_c11_restricted_over_morphism X Y f U) z) =
      Point.map f (Point.map (openInclusion X (f.left ⁻¹ᵁ U)) z)
    rw [← Point.map_comp_apply, ← Point.map_comp_apply,
      s2e_c11_restricted_over_morphism_inclusion]
  have hh := eY.isProperMap.comp (hf.comp eX.symm.isProperMap)
  convert hh using 1
  funext z
  apply Subtype.ext
  have h := hsquare (eX.symm z)
  rw [eX.apply_symm_apply] at h
  exact h.symm

end HodgeLean.Foundations.Program
