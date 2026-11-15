import HodgeLean.Foundations.RationalHomologyManifold.ScalarCycleAbsoluteSection
import HodgeLean.Foundations.RationalHomologyManifold.OrientationSectionOnOpen
import HodgeLean.Foundations.RationalHomologyManifold.RationalConstantSheafExt

/-! Actual scalar cycle classes and the specified local orientation.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A cycle with the specified actual local values gives exactly the original local orientation morphism in the supported homology sheaf.
Source: Bredon, Sheaf Theory, second edition, V.9, V.16 and VI.12; normalization by actual local generators.
HC no distance; AV milestone no distance.
-/
theorem scalarCycleHomologySheafMap_orientation (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X (n + 1))
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : (SingularChainComplex ℚ X).d (n + 1) n z = 0)
    (hc : localization X (n + 1)
      (((SingularChainComplex ℚ X).sc (n + 1)).moduleCatHomologyClass
        (scalarAmbientCycle X n z hz)) = o.generator) :
    scalarCycleHomologySheafMap X n z hz = (localOrientationHomologySheafIso X (n + 1) o).hom := by
  let e := localOrientationHomologySheafIso X (n + 1) o
  apply (cancel_mono e.inv).mp
  rw [Iso.hom_inv_id]
  apply rationalConstantSheaf_hom_ext_one
  intro U
  have he := (scalarCycleHomologySheafMap_absolute_section X n z hz U).trans
    (absolute_orientation_section_on_open X (n + 1) o _ hc U)
  change e.inv.hom.app (op U)
      ((scalarCycleHomologySheafMap X n z hz).hom.app (op U)
        (constSection (AddCommGrpCat.of ℚ) U 1)) = constSection (AddCommGrpCat.of ℚ) U 1
  rw [he]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op U)) e.hom_inv_id) (constSection (AddCommGrpCat.of ℚ) U 1)

#print axioms scalarCycleHomologySheafMap_orientation
end HodgeLean.Foundations.RationalHomologyManifold
