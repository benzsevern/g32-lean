import HodgeLean.Foundations.RationalHomologyManifold.FixedCapPresheafDifferential

/-! Sheafification of literal fixed-chain cap from actual ambient cochains.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Sheafify the actual fixed-chain cap morphism from constant ambient singular cochains.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
def ambientFixedCapSheafMap (X : TopCat.{0}) (p q : ℕ)
    (z : (SingularChainComplex ℚ X).X (p + q)) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      ((ambientCochainPresheafComplex X).X p) ⟶ (subdivisionLimitSheafComplex X).X q :=
  ⟨sheafifyLift (Opens.grothendieckTopology X) (ambientFixedCapPresheafMap X p q z)
    ((subdivisionLimitSheafComplex X).X q).property⟩

#print axioms ambientFixedCapSheafMap
end HodgeLean.Foundations.RationalHomologyManifold
