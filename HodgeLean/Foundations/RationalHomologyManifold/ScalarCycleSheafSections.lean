import HodgeLean.Foundations.RationalHomologyManifold.ScalarCyclePresheaf
import HodgeLean.RealDefs.DegreeZero

/-! Actual scalar homology sections under sheafification.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The scalar cycle homology sheaf morphism evaluates on constant sections by sheafifying the original scalar relative homology presheaf section.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; naturality of homology sheafification.
HC no distance; AV milestone no distance.
-/
theorem scalarCycleHomologySheafMap_constSection (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : (SingularChainComplex ℚ X).d (n + 1) n z = 0) (U : Opens X) (r : ℚ) :
    (scalarCycleHomologySheafMap X n z hz).hom.app (op U)
        (constSection (AddCommGrpCat.of ℚ) U r) =
      (singularChainHomologyPresheafToSheaf ℚ X (n + 1)).app (op U)
        ((scalarCycleHomologyPresheafMap X n z hz).app (op U) r) := by
  let J := Opens.grothendieckTopology X
  have h := congrArg (fun f => (f ≫ (singularChainHomologySheafificationIso ℚ X (n + 1)).hom.hom).app
    (op U) r) (toSheafify_naturality J (scalarCycleHomologyPresheafMap X n z hz))
  exact h.symm

#print axioms scalarCycleHomologySheafMap_constSection
end HodgeLean.Foundations.RationalHomologyManifold
