import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian11OrientationProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8Examples

/-! # Compositions from support comparison to the period square

Implication from the named comparison primitives and the bh10 relative square.
HC no distance; AV milestone no distance.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
open TopCat.Sheaf
namespace HodgeLean.Adapters

/-- The sheaf-to-singular comparison commutes with forgetting support.
Source: the singular-section edge and sheaf-support edge comparisons. -/
theorem bh11_forget_support_singular
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (S : Closeds (ComplexPoint X)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :
    singularToFieldCohomology ℚ X n
      (cohomologyMap ℚ n
        (TopCat.ofHom ⟨(Homeomorph.Set.univ (ComplexPoint X)).symm,
          (Homeomorph.Set.univ (ComplexPoint X)).symm.continuous⟩)
        (relativeCohomologyToAbsolute ℚ
          (neighborhoodSupportComplementPair Set.univ (S : Set (ComplexPoint X))) n
          (supportedSingularClass X S n u))) = ComplexPoint.forgetSupport ℚ X S n u :=
  bh11_forget_support_singular_aux X S n u

/-- The normalized cup comparison of a supported class is its absolute singular image.
Source: the forget-support bridge and the scalar-one cup comparison. -/
theorem bh11_cup_forget_support
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (S : Closeds (ComplexPoint X)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :
    cupComparison X n (forgetSupport ℚ X S n u) =
      cohomologyMap ℚ n
        (TopCat.ofHom ⟨(Homeomorph.Set.univ (ComplexPoint X)).symm,
          (Homeomorph.Set.univ (ComplexPoint X)).symm.continuous⟩)
        (relativeCohomologyToAbsolute ℚ
          (neighborhoodSupportComplementPair Set.univ (S : Set (ComplexPoint X))) n
          (supportedSingularClass X S n u)) :=
  bh11_cup_forget_support_aux X S n u

/-- The exact stage-eight square–torus comparison, assembled from independent bridges.
Source: `bh10_relative_square_torus`, the support comparison and unit normalization. -/
theorem bh11_square_torus
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
            (cycleComponentAnalyticClosedSupport X x) 2) a))) bh5_diskClass :=
  bh11_square_torus_aux X x a l m z ha

open HodgeLean.Foundations.Curves

example := bh11_forget_support_singular E
  (cycleComponentAnalyticClosedSupport E bh8_cubicWitness.x) 2
  (cycleComponentSupportedInjectiveClass E bh8_cubicWitness.x bh8_cubicWitness.codim)

example := bh11_cup_forget_support E
  (cycleComponentAnalyticClosedSupport E bh8_cubicWitness.x) 2
  (cycleComponentSupportedInjectiveClass E bh8_cubicWitness.x bh8_cubicWitness.codim)

example := bh11_square_torus E bh8_cubicWitness.x
  (cycleComponentSupportedInjectiveClass E bh8_cubicWitness.x bh8_cubicWitness.codim)
  0 0 bh8_cubicWitness.point (bh8_witness_boundary E bh8_cubicWitness).2

end HodgeLean.Adapters
