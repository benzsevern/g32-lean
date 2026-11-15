import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapGlobalComplex

/-! Literal middle normalization of actual global fixed-cycle cap.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- In a positive complementary degree the actual global cap map retains literal singular cap followed by the original stage-zero supported chain projection.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
theorem globalFixedCycleCapComplexHom_component (X : TopCat.{0}) (N p q : ℕ)
    (hp : 0 < p) (hN : p + q = N)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0) :
    (globalFixedCycleCapComplexHom X N z hz).f p ≫
        (subdivisionGlobalSectionsFunctor X).map (capTargetTermIso X N p q hp hN).hom =
      AddCommGrpCat.ofHom (((capLinear ℚ p q).flip
        (((SingularChainComplex ℚ X).XIsoOfEq hN.symm).hom z)).toAddMonoidHom) ≫
          subdivisionAmbientSectionMap X q ⊤ 0 := by
  let E := subdivisionGlobalSectionsFunctor X
  change ((ambientCochainGlobalUnit X).f p ≫ E.map (ambientCapTargetComponent X N z p)) ≫
    E.map (capTargetTermIso X N p q hp hN).hom = _
  rw [Category.assoc, ← E.map_comp, ambientCapTargetComponent_positive X N p q z hp hN]
  have h := congrArg (fun f => f.app (op (⊤ : Opens X)))
    (toSheafify_sheafifyLift (Opens.grothendieckTopology X)
      (ambientFixedCapPresheafMap X p q (((SingularChainComplex ℚ X).XIsoOfEq hN.symm).hom z))
      ((subdivisionLimitSheafComplex X).X q).property)
  exact h

#print axioms globalFixedCycleCapComplexHom_component
end HodgeLean.Foundations.RationalHomologyManifold
