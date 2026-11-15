import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainGlobalRestriction
import HodgeLean.Foundations.RationalHomologyManifold.AmbientFixedCycleCapComplex

/-! The actual global fixed-cycle cap morphism into the bounded supported-chain model.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Apply literal fixed-cycle cap to actual ordinary global cochains through their constant ambient sheaf sections.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
def globalFixedCycleCapComplexHom (X : TopCat.{0}) (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0) :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
      (SingularCochainComplex ℚ X) ⟶
    ((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
      (capTargetComplex X N) :=
  ambientCochainGlobalUnit X ≫
    ((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map
      (ambientFixedCycleCapComplexHom X N z hz)

#print axioms globalFixedCycleCapComplexHom
end HodgeLean.Foundations.RationalHomologyManifold
