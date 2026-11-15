import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian10OrientationProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8Examples

/-! # Relative singular period-square comparison

Implication from square-edge avoidance, assembled through the actual torus pair.
The comparison between sheaf-supported and absolute singular classes remains separate.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
namespace HodgeLean.Adapters

/-- The singular relative period-square comparison, before the sheaf-support comparison.
Source: Hatcher, Algebraic Topology, section 3.3; `bh9_torus_cell_aux`,
`bh10_square_factorization`, and naturality of the relative chain projection. -/
theorem bh10_relative_square_torus
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
      bh5_diskClass :=
  bh10_relative_square_torus_aux X x l m z ha b

open HodgeLean.Foundations.Curves HodgeLean.Foundations.Singular

example := bh10_periodTorus_real E 0 0 bh8_cubicWitness.point (1 / 3) (2 / 3)

example : bh8_periodTorus E 0 0 bh8_cubicWitness.point 0 ∉
    cycleComponentSupport E bh8_cubicWitness.x :=
  bh10_periodTorus_skeleton E bh8_cubicWitness.x 0 0 bh8_cubicWitness.point
    (bh8_witness_boundary E bh8_cubicWitness).2 0 (Or.inl rfl)

example : (TopPair.Hom.fst (bh10_periodTorusPairMap E bh8_cubicWitness.x
    0 0 bh8_cubicWitness.point (bh8_witness_boundary E bh8_cubicWitness).2) (0 : UnitAddTorus (Fin 2))).val =
    bh8_periodTorus E 0 0 bh8_cubicWitness.point 0 := rfl

example := bh10_square_factorization E bh8_cubicWitness.x 0 0 bh8_cubicWitness.point
  (bh8_witness_boundary E bh8_cubicWitness).2

example := bh10_relative_square_torus E bh8_cubicWitness.x 0 0 bh8_cubicWitness.point
  (bh8_witness_boundary E bh8_cubicWitness).2
  (supportedSingularClass E (cycleComponentAnalyticClosedSupport E bh8_cubicWitness.x) 2
    (cycleComponentSupportedInjectiveClass E bh8_cubicWitness.x bh8_cubicWitness.codim))

end HodgeLean.Adapters
