import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainSheafComplex
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionGlobalSections

/-! Actual global ambient cochains as constant sheaf sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Regard each actual global singular cochain as its constant ambient sheaf section on the whole space.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; the actual ambient cochain sheafification unit.
HC no distance; AV milestone no distance.
-/
def ambientCochainGlobalUnit (X : TopCat.{0}) :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
      (SingularCochainComplex ℚ X) ⟶
    ((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
      (ambientCochainSheafComplex X) :=
  CochainComplex.ofHom (fun p =>
    (toSheafify (Opens.grothendieckTopology X) ((ambientCochainPresheafComplex X).X p)).app (op ⊤))
    (fun p => by
      have h := congrArg (fun f => f.app (op ⊤))
        (toSheafify_naturality (Opens.grothendieckTopology X)
          ((ambientCochainPresheafComplex X).d p (p + 1)))
      exact h.symm)

#print axioms ambientCochainGlobalUnit
end HodgeLean.Foundations.RationalHomologyManifold
