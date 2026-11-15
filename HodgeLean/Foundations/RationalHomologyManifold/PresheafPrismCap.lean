import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainKernel
import HodgeLean.Foundations.RationalHomologyManifold.PrismCapStabilization
import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionSections

/-! Actual finite prism-cap morphisms from ambient cochains to the supported chain sheaf.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Cap the literal finite prism sum, then use the actual ambient-chain projection and stage-zero sheafification.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, sections 2.1 and 3.3.
HC no distance; AV milestone no distance.
-/
def ambientPrismCapPresheafMap (X : TopCat.{0}) (n p q : ℕ)
    (z : (SingularChainComplex ℚ X).X n) (m : ℕ) :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (Cochain ℚ (TopCat.toSSet.obj X) p)) ⟶
      ((subdivisionLimitSheafComplex X).X q).obj :=
  (Functor.const (Opens X)ᵒᵖ).map (AddCommGrpCat.ofHom
      (((capLinear ℚ p q).flip (rationalPrismSum X n (p + q) m z)).toAddMonoidHom)) ≫
    ambientChainPresheafProjection X q ≫
      (colimit.ι (presheafSubdivisionDiagram X) 0).f q ≫
        toSheafify (Opens.grothendieckTopology X) ((subdivisionLimitPresheafComplex X).X q)

#print axioms ambientPrismCapPresheafMap
/-- The finite presheaf prism-cap map retains the actual ambient cap formula on each open set.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; the stage-zero supported cap representative.
HC no distance; AV milestone no distance.
-/
theorem ambientPrismCapPresheafMap_apply (X : TopCat.{0}) (n p q : ℕ)
    (z : (SingularChainComplex ℚ X).X n) (m : ℕ) (U : Opens X)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p) :
    (ambientPrismCapPresheafMap X n p q z m).app (Opposite.op U) φ =
      subdivisionAmbientSectionMap X q U 0 (cap ℚ p q φ (rationalPrismSum X n (p + q) m z)) := by
  rfl

#print axioms ambientPrismCapPresheafMap_apply
end HodgeLean.Foundations.RationalHomologyManifold
