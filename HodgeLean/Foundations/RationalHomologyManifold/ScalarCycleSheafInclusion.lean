import Mathlib.CategoryTheory.Sites.Abelian
import HodgeLean.Foundations.RationalHomologyManifold.ScalarCyclePresheaf
import HodgeLean.Foundations.RationalHomologyManifold.ScalarChainSheafUnit
import HodgeLean.Foundations.RationalHomologyManifold.ExactHomologyLiftNormalization

/-! Actual inclusion of scalar cycle classes after homology sheafification.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The original scalar cycle class retains its scalar chain section after inclusion in the actual boundary quotient of the chain sheaf.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; exact sheafification of actual cycle classes.
HC no distance; AV milestone no distance.
-/
theorem scalarCycleHomologySheafMap_inclusion (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : (SingularChainComplex ℚ X).d (n + 1) n z = 0) :
    scalarCycleHomologySheafMap X n z hz ≫ (singularChainSheafComplex ℚ X).homologyι (n + 1) =
      scalarChainSheafMap X (n + 1) z ≫ (singularChainSheafComplex ℚ X).pOpcycles (n + 1) := by
  let K := singularChainPresheafComplex ℚ X
  let F : TopCat.Presheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}
  letI : F.Additive := CategoryTheory.presheafToSheaf_additive
  letI : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}))
  letI : PreservesFiniteColimits F := inferInstanceAs
    (PreservesFiniteColimits (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}))
  let S := K.sc (n + 1)
  let k := scalarChainPresheafMap X (n + 1) z
  have hk : k ≫ S.g = 0 := by
    change k ≫ K.d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) = 0
    rw [ChainComplex.next_nat_succ]
    exact scalarChainPresheafMap_cycle X n z hz
  have h := exactFunctor_cycle_class S F k hk
  have h' : F.map (S.liftCycles k hk ≫ S.homologyπ) ≫ (S.mapHomologyIso F).inv =
      (S.map F).liftCycles (F.map k)
        (by change F.map k ≫ F.map S.g = 0; rw [← F.map_comp, hk, F.map_zero]) ≫
          (S.map F).homologyπ := by
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (F.map (S.liftCycles k hk ≫ S.homologyπ) ≫ (S.mapHomologyIso F).inv) ≫
      (S.map F).homologyι = F.map k ≫ (S.map F).pOpcycles
  rw [h', Category.assoc, ShortComplex.homology_π_ι, ← Category.assoc,
    ShortComplex.liftCycles_i]

#print axioms scalarCycleHomologySheafMap_inclusion
end HodgeLean.Foundations.RationalHomologyManifold
