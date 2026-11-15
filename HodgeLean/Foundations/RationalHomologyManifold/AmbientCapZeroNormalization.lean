import HodgeLean.Foundations.RationalHomologyManifold.AmbientCapComponents

/-! The actual degree-zero bounded cap component.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- In degree zero, bounded cap is literal fixed-chain cap followed by the actual top-chain boundary quotient.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
theorem ambientCapTargetComponent_zero (X : TopCat.{0}) (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N) :
    ambientCapTargetComponent X N z 0 ≫ (capTargetZeroTermIso X N).hom =
      ambientFixedCapSheafMap X 0 N
        (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N)).hom z) ≫
          (subdivisionLimitSheafComplex X).pOpcycles N := by
  simp only [ambientCapTargetComponent, dif_pos rfl, dite_true, ite_true, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

#print axioms ambientCapTargetComponent_zero
end HodgeLean.Foundations.RationalHomologyManifold
