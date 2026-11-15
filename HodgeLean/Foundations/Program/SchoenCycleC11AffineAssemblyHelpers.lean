import HodgeLean.Foundations.Program.SchoenCycleC11AffineHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11EtaleSmoothHelpers
import HodgeLean.Foundations.Analytic.Analytification

/-! # Affine analytic properness transport
Implication from finite algebra coordinate bounds to the actual affine point maps.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology
namespace HodgeLean.Foundations.Program

/-- A finite algebra induces a proper restriction map on complex algebra points.
Source: Checked finite-element bounds and properness from closed coordinate embeddings. -/
theorem s2e_c11_finite_algebra_point_restriction_proper
    (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [Module.Finite A B] :
    IsProperMap (fun φ : B →ₐ[ℂ] ℂ ↦ φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
  have : T2Space (A →ₐ[ℂ] ℂ) := (s2e_c11_algebraHom_isClosedEmbedding A).isEmbedding.t2Space
  have hc : Continuous (fun φ : B →ₐ[ℂ] ℂ ↦ φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
    rw [continuous_induced_rng]
    exact continuous_pi fun a ↦ continuous_affineAlgebraHom_apply B (algebraMap A B a)
  exact s2e_c11_proper_of_coordinate_bounds
    (fun φ : B →ₐ[ℂ] ℂ ↦ (φ : B → ℂ)) (s2e_c11_algebraHom_isClosedEmbedding B)
    _ hc (fun b ↦ s2e_c11_finite_element_continuous_bound b)


/-- The coordinate algebra homomorphism of a finite affine morphism is finite.
Source: Mathlib, IsFinite.SpecMap_iff and invariance under scheme isomorphisms. -/
theorem s2e_c11_affine_coordinate_algHom_finite
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [IsFinite f.left] :
    letI := s2e_c11_affineSectionAlgebra X
    letI := s2e_c11_affineSectionAlgebra Y
    (s2e_c11_affineCoordinateAlgHom X Y f).toRingHom.Finite := by
  letI := s2e_c11_affineSectionAlgebra X
  letI := s2e_c11_affineSectionAlgebra Y
  have hmap : IsFinite (Spec.map (CommRingCat.ofHom
      (s2e_c11_affineCoordinateAlgHom X Y f).toRingHom)) := by
    rw [s2e_c11_affineCoordinateAlgHom_spec]
    infer_instance
  exact (IsFinite.SpecMap_iff _).mp hmap

/-- Finite analytic properness holds on the exact affine-base restriction.
Source: Checked f4_isProperMap_of_isProper; Hartshorne, Algebraic Geometry, Appendix B. -/
theorem s2e_c11_finite_affine_restriction_point_proper
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    IsProperMap ((Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f)) := by
  have : IsAffine (openScheme X (f.left ⁻¹ᵁ U)).left := hU.preimage f.left
  have : IsAffine (openScheme Y U).left := hU
  have : LocallyOfFiniteType (openScheme X (f.left ⁻¹ᵁ U)).hom :=
    inferInstanceAs (LocallyOfFiniteType ((f.left ⁻¹ᵁ U).ι ≫ X.hom))
  have : LocallyOfFiniteType (openScheme Y U).hom :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ Y.hom))
  have : IsAffineHom (openScheme X (f.left ⁻¹ᵁ U)).hom := inferInstance
  have : IsAffineHom (openScheme Y U).hom := inferInstance
  have : IsFinite (s2e_c11_restricted_over_morphism X Y f U).left :=
    inferInstanceAs (IsFinite (f.left ∣_ U))
  exact s2e_c11_restricted_point_proper X Y f U
    (HodgeLean.Foundations.Analytic.f4_isProperMap_of_isProper
      (s2e_c11_restricted_over_morphism X Y f U))

/-- Finite etale maps to projective space give finite analytic coverings.
Source: Hartshorne, Algebraic Geometry, Appendix B; checked affine properness and smooth-base local inverses. -/
theorem s2e_c11_projective_finite_etale_analytic_cover
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (f : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite f.left] [Etale f.left] :
    IsCoveringMap (Point.map f) ∧
      (∀ y, Set.Finite ((Point.map f) ⁻¹' {y})) := by
  have : LocallyOfFiniteType
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
    inferInstanceAs (LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
  have : LocallyOfFiniteType W.hom := by
    rw [← Over.w f]
    change LocallyOfFiniteType (f.left ≫ ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    infer_instance
  apply s2e_c11_analytic_cover_of_affine_restrictions W _ f
  · exact s2e_c11_projective_finite_etale_local_homeomorph k W f
  · intro U hU
    exact (s2e_c11_finite_affine_restriction_point_proper W _ f U hU).isClosedMap

end HodgeLean.Foundations.Program
