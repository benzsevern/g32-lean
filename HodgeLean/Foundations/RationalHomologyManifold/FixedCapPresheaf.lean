import HodgeLean.Foundations.RationalHomologyManifold.PresheafPrismCap

/-! Literal fixed-chain cap from ambient cochains to the supported subdivision sheaf.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Cap a specified actual chain, then use the original ambient-chain projection at subdivision stage zero.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
def ambientFixedCapPresheafMap (X : TopCat.{0}) (p q : ℕ)
    (z : (SingularChainComplex ℚ X).X (p + q)) :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (Cochain ℚ (TopCat.toSSet.obj X) p)) ⟶
      ((subdivisionLimitSheafComplex X).X q).obj :=
  (Functor.const (Opens X)ᵒᵖ).map (AddCommGrpCat.ofHom
      (((capLinear ℚ p q).flip z).toAddMonoidHom)) ≫
    ambientChainPresheafProjection X q ≫
      (colimit.ι (presheafSubdivisionDiagram X) 0).f q ≫
        toSheafify (Opens.grothendieckTopology X) ((subdivisionLimitPresheafComplex X).X q)

#print axioms ambientFixedCapPresheafMap
end HodgeLean.Foundations.RationalHomologyManifold
