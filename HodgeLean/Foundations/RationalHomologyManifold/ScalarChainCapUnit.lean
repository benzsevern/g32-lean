import HodgeLean.Foundations.RationalHomologyManifold.ScalarChainPresheaf
import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainUnit
import HodgeLean.Foundations.RationalHomologyManifold.FixedCapPresheafUnit

/-! Literal equality of scalar chain sections and actual unit cap sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual unit cap retains a chain specified in total degree after the canonical degree transport.
Source: Hatcher, Algebraic Topology, section 3.3; the singular cap unit.
HC no distance; AV milestone no distance.
-/
theorem chain_cap_unit_total (X : TopCat.{0}) (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N) :
    cap ℚ 0 N (HodgeLean.Foundations.Singular.unitCochain (R := ℚ) X)
      (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N)).hom z) = z := by
  let e := (SingularChainComplex ℚ X).XIsoOfEq (Nat.zero_add N)
  change cap ℚ 0 N (HodgeLean.Foundations.Singular.unitCochain (R := ℚ) X) (e.inv z) = z
  rw [chain_cap_unit]
  exact ConcreteCategory.congr_hom e.inv_hom_id z

#print axioms chain_cap_unit_total
/-- Before sheafification, actual fixed cap by scalar multiples of the original unit equals the actual stage-zero supported scalar chain section.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
theorem scalarChainPresheafMap_unit_cap (X : TopCat.{0}) (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N) :
    ambientConstantsToZeroPresheaf X ≫ ambientFixedCapPresheafMap X 0 N
        (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N)).hom z) =
      scalarChainPresheafMap X N z ≫ (colimit.ι (presheafSubdivisionDiagram X) 0).f N ≫
        toSheafify (Opens.grothendieckTopology X) ((subdivisionLimitPresheafComplex X).X N) := by
  let a : AddCommGrpCat.of ℚ ⟶ AddCommGrpCat.of (Cochain ℚ (TopCat.toSSet.obj X) 0) := AddCommGrpCat.ofHom (LinearMap.toSpanSingleton ℚ _
    (HodgeLean.Foundations.Singular.unitCochain (R := ℚ) X)).toAddMonoidHom
  let b : AddCommGrpCat.of (Cochain ℚ (TopCat.toSSet.obj X) 0) ⟶
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).obj ((SingularChainComplex ℚ X).X N) := AddCommGrpCat.ofHom (((capLinear ℚ 0 N).flip
    (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N)).hom z)).toAddMonoidHom)
  let c : AddCommGrpCat.of ℚ ⟶
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).obj ((SingularChainComplex ℚ X).X N) := AddCommGrpCat.ofHom (LinearMap.toSpanSingleton ℚ _ z).toAddMonoidHom
  have hc : a ≫ b = c := by
    ext r
    change ℚ at r
    change ((capLinear ℚ 0 N).flip
      (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N)).hom z))
        (r • HodgeLean.Foundations.Singular.unitCochain (R := ℚ) X) = r • z
    rw [map_smul]
    exact congrArg (r • ·) (chain_cap_unit_total X N z)
  let F : AddCommGrpCat.{0} ⥤ TopCat.Presheaf AddCommGrpCat.{0} X := Functor.const (Opens X)ᵒᵖ
  change F.map a ≫ F.map b ≫ ambientChainPresheafProjection X N ≫
      (colimit.ι (presheafSubdivisionDiagram X) 0).f N ≫
        toSheafify (Opens.grothendieckTopology X) ((subdivisionLimitPresheafComplex X).X N) =
    (F.map c ≫ ambientChainPresheafProjection X N) ≫ _
  rw [← Category.assoc (F.map a) (F.map b), ← F.map_comp, hc, Category.assoc]

#print axioms scalarChainPresheafMap_unit_cap
end HodgeLean.Foundations.RationalHomologyManifold
