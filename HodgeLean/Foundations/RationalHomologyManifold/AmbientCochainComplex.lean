import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainPresheaf

/-! Actual ambient cochains, their local restriction, and its kernel as presheaf complexes.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Regard the actual singular cochain complex as a constant presheaf complex.
Source: Bredon, Sheaf Theory, second edition, VI.12; constant ambient singular cochains.
HC no distance; AV milestone no distance.
-/
def ambientCochainPresheafComplex (X : TopCat.{0}) :
    CochainComplex (TopCat.Presheaf AddCommGrpCat.{0} X) ℕ :=
  ((Functor.const (Opens X)ᵒᵖ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (SingularCochainComplex ℚ X))

#print axioms ambientCochainPresheafComplex
/-- Restriction from actual ambient to local singular cochains is a morphism of the existing presheaf complexes.
Source: Bredon, Sheaf Theory, second edition, VI.12; the ambient to local cochain complex map.
HC no distance; AV milestone no distance.
-/
def ambientCochainPresheafComplexRestriction (X : TopCat.{0}) :
    ambientCochainPresheafComplex X ⟶ singularCochainPresheafComplex ℚ X :=
  CochainComplex.ofHom (fun p => ambientCochainPresheafRestriction X p) (fun p => by
    rw [singularCochainPresheafComplex_d]
    exact (ambientCochainPresheafRestriction_coboundary X p).symm)

#print axioms ambientCochainPresheafComplexRestriction
end HodgeLean.Foundations.RationalHomologyManifold
