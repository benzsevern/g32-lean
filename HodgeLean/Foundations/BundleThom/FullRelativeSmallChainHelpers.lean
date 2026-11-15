import HodgeLean.Foundations.BundleThom.RelativeSmallChainComparisonHelpers

/-! # Actual relative comparison for the full singular subcomplex

Both ambient and relative-subspace singular inclusions are isomorphisms before taking relative homology.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- The full-subcomplex relative comparison into the actual topological pair is a quasi-isomorphism.
Source: Hatcher, Algebraic Topology, §2.1, full singular relative chains. -/
theorem i1_fullRelativeSmallChainComparison_quasiIso (X : TopCat) (Z : Set X) :
    QuasiIso (i1_relativeSmallChainComparison X Z ⊤) := by
  apply i1_relativeSmallChainComparison_quasiIso X Z ⊤
  · change QuasiIso (SSet.chainComplexMap
      (SSet.Subcomplex.topIso (TopCat.toSSet.obj (TopCat.of Z))).hom (ModuleCat.of ℚ ℚ))
    infer_instance
  · change QuasiIso (SSet.chainComplexMap
      (SSet.Subcomplex.topIso (TopCat.toSSet.obj X)).hom (ModuleCat.of ℚ ℚ))
    infer_instance

end HodgeLean.Foundations.BundleThom
