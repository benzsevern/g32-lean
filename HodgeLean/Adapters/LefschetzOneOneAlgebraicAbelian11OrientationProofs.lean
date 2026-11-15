import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian11ComparisonProofs

/-! # Compositions from support comparison to the period square

Implication from the named comparison primitives and the bh10 relative square.
HC no distance; AV milestone no distance.
-/
set_option maxRecDepth 2048
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
open TopCat.Sheaf
namespace HodgeLean.Adapters

/-- The exact stage-eight square–torus comparison, assembled from independent bridges.
Source: `bh10_relative_square_torus`, the support comparison and unit normalization. -/
theorem bh11_square_torus_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left)
    (a : CycleComponentSupportedCohomology X x 1)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (ha : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      abelianExp X (bh4_squareEdge X l m z i t) ∉ cycleComponentSupport X x) :
    bh8_torusCoefficient (cohomologyMap ℚ 2 (TopCat.ofHom (bh8_periodTorus X l m z))
      (cupComparison X 2 (forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) 2 a))) =
    relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
      (relativeCohomologyMap ℚ 2 (bh5_componentPairMap X x l m z ha)
        (complexSupportInjectiveSectionCohomologyEquiv X
          (cycleComponentAnalyticClosedSupport X x) ⊤ 2
          ((rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) 2) a))) bh5_diskClass := by
  let S := cycleComponentAnalyticClosedSupport X x
  let b : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint X))
        (cycleComponentSupport X x)) 2 := supportedSingularClass X S 2 a
  let c : Cohomology ℚ (TopCat.of (Set.univ : Set (ComplexPoint X))) 2 :=
    relativeCohomologyToAbsolute ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint X))
        (cycleComponentSupport X x)) 2 b
  let j : TopCat.of (ComplexPoint X) ⟶ TopCat.of (Set.univ : Set (ComplexPoint X)) :=
    TopCat.ofHom ⟨(Homeomorph.Set.univ (ComplexPoint X)).symm,
      (Homeomorph.Set.univ (ComplexPoint X)).symm.continuous⟩
  have hc := bh11_cup_forget_support_aux X S 2 a
  have hcomp :
      cohomologyMap ℚ 2 (TopCat.ofHom (bh8_periodTorus X l m z) ≫ j)
        c =
      cohomologyMap ℚ 2 (TopCat.ofHom (bh8_periodTorus X l m z))
        (cohomologyMap ℚ 2 j c) := by
    rw [cohomologyMap_comp]
    rfl
  have hmap : TopPair.Hom.fst (bh10_periodTorusPairMap X x l m z ha) =
      TopCat.ofHom (bh8_periodTorus X l m z) ≫ j := rfl
  have hb : b = complexSupportInjectiveSectionCohomologyEquiv X S ⊤ 2
      (rationalSupportAddEquivSupportedInjectiveHomology X S 2 a) := rfl
  exact (congrArg (fun v => bh8_torusCoefficient
    (cohomologyMap ℚ 2 (TopCat.ofHom (bh8_periodTorus X l m z)) v)) hc).trans
    ((congrArg bh8_torusCoefficient hcomp.symm).trans
      ((congrArg (fun k => bh8_torusCoefficient
        (cohomologyMap ℚ 2 k c)) hmap.symm).trans
        ((bh10_relative_square_torus X x l m z ha b).trans
          (congrArg (fun c => relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
            (relativeCohomologyMap ℚ 2 (bh5_componentPairMap X x l m z ha) c)
            bh5_diskClass) hb))))

end HodgeLean.Adapters
