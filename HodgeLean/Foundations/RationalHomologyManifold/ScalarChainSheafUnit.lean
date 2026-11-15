import HodgeLean.Foundations.RationalHomologyManifold.ScalarChainCapUnit
import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainSheafUnit

/-! Actual scalar chain and cup-unit cap equality after sheafification.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Sheafify the actual supported scalar chain section without changing its relative-chain projection.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; actual supported-chain sheafification.
HC no distance; AV milestone no distance.
-/
def scalarChainSheafMap (X : TopCat.{0}) (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N) :
    TopCat.Sheaf.const X (AddCommGrpCat.of ℚ) ⟶ (singularChainSheafComplex ℚ X).X N :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
    (scalarChainPresheafMap X N z)

#print axioms scalarChainSheafMap
/-- Sheafified actual unit cap is exactly the original supported scalar chain followed by its stage-zero subdivision map.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
theorem scalarChainSheafMap_unit_cap (X : TopCat.{0}) (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N) :
    ambientConstantsToZeroSheaf X ≫ ambientFixedCapSheafMap X 0 N
        (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N)).hom z) =
      scalarChainSheafMap X N z ≫ (subdivisionSheafStage X 0).f N := by
  let J := Opens.grothendieckTopology X
  apply (sheafToPresheaf J AddCommGrpCat).map_injective
  apply sheafify_hom_ext J _ _ ((subdivisionLimitSheafComplex X).X N).property
  change toSheafify J _ ≫ (sheafifyMap J (ambientConstantsToZeroPresheaf X) ≫
      sheafifyLift J (ambientFixedCapPresheafMap X 0 N
        (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N)).hom z)) _) =
    toSheafify J _ ≫ (sheafifyMap J (scalarChainPresheafMap X N z) ≫
      sheafifyMap J ((colimit.ι (presheafSubdivisionDiagram X) 0).f N))
  simp only [← Category.assoc, ← toSheafify_naturality]
  simp only [Category.assoc, toSheafify_sheafifyLift]
  rw [← toSheafify_naturality]
  exact scalarChainPresheafMap_unit_cap X N z

#print axioms scalarChainSheafMap_unit_cap
end HodgeLean.Foundations.RationalHomologyManifold
