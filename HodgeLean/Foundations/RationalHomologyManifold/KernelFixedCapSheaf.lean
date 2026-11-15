import HodgeLean.Foundations.RationalHomologyManifold.KernelPrismIdentity

/-! Actual sheafification of fixed-chain cap restricted to the ambient cochain kernel.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Sheafify the literal fixed-chain cap morphism on the actual cochain-restriction kernel.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; sheafification of the local kernel cap map.
HC no distance; AV milestone no distance.
-/
def kernelFixedCapSheafMap (X : TopCat.{0}) (p q : ℕ)
    (z : (SingularChainComplex ℚ X).X (p + q)) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ((ambientLocalZeroPresheafComplex X).X p) ⟶ (subdivisionLimitSheafComplex X).X q :=
  ⟨sheafifyLift (Opens.grothendieckTopology X)
    ((kernel.ι (ambientCochainPresheafComplexRestriction X)).f p ≫ ambientFixedCapPresheafMap X p q z)
    ((subdivisionLimitSheafComplex X).X q).property⟩

#print axioms kernelFixedCapSheafMap
end HodgeLean.Foundations.RationalHomologyManifold
