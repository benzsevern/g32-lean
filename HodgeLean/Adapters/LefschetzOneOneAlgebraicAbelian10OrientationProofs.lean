import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian10OrientationDefs

set_option backward.isDefEq.respectTransparency false

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
namespace HodgeLean.Adapters

/-- The singular relative period-square comparison, before the sheaf-support comparison.
Source: Hatcher, Algebraic Topology, section 3.3; `bh9_torus_cell_aux`,
`bh10_square_factorization`, and naturality of the relative chain projection. -/
theorem bh10_relative_square_torus_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (l m : abelianPeriodLattice X)
    (z : Fin (dim X.left) → ℂ)
    (ha : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      abelianExp X (bh4_squareEdge X l m z i t) ∉ cycleComponentSupport X x)
    (b : RelativeCohomology ℚ (neighborhoodSupportComplementPair
      ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X)) (cycleComponentSupport X x)) 2) :
    bh8_torusCoefficient
      (cohomologyMap ℚ 2 (TopPair.Hom.fst (bh10_periodTorusPairMap X x l m z ha))
        (relativeCohomologyToAbsolute ℚ _ 2 b)) =
    relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
      (relativeCohomologyMap ℚ 2 (bh5_componentPairMap X x l m z ha) b)
      bh5_diskClass := by
  have hn : relativeCohomologyToAbsolute ℚ bh9_torusPair 2
      (relativeCohomologyMap ℚ 2 (bh10_periodTorusPairMap X x l m z ha) b) =
      cohomologyMap ℚ 2 (TopPair.Hom.fst (bh10_periodTorusPairMap X x l m z ha))
        (relativeCohomologyToAbsolute ℚ _ 2 b) := by
    have hdual := congrArg HomologicalComplex.linearDualMap
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
        (bh10_periodTorusPairMap X x l m z ha))
    rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at hdual
    have hhom := congrArg (fun v ↦ HomologicalComplex.homologyMap v 2) hdual
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
    exact ConcreteCategory.congr_hom hhom b
  rw [← hn]
  have h := bh9_torus_cell_aux
    (relativeCohomologyMap ℚ 2 (bh10_periodTorusPairMap X x l m z ha) b)
  rw [← bh10_square_factorization X x l m z ha, relativeCohomologyMap_comp]
  exact h

end HodgeLean.Adapters
