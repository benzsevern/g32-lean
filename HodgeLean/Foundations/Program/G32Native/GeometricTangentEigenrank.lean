import HodgeLean.Foundations.Program.G32Native.HolomorphicPeriodDual
import HodgeLean.Foundations.Program.G32Native.InvariantEigenrank

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Module TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native

/-- Analytic tangent eigenvalue multiplicities equal the multiplicities on holomorphic
cohomology, for every rational geometric endomorphism and every complex eigenvalue.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.2 (analytic and rational
representations) and Theorem 1.4.1; duality between invariant one-forms and the tangent space.
This is a rank comparison for the transpose, with the same eigenvalue. -/
theorem geometric_holomorphic_eigenrank_aux
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (f : AbelianEnd0 A) (z : ℂ) :
    letI := (torusCohomology_cupProductOf A).finite
    finrank ℂ ↥(Module.End.eigenspace ((abelianEnd0Action A f).unop.baseChange ℂ) z ⊓
      (abelianWeightOneHodgeStructure A).H (1, 0)) =
      finrank ℂ (Module.End.eigenspace (printedAnalyticAction A f) z) := by
  letI := (torusCohomology_cupProductOf A).finite
  let T := (abelianEnd0Action A f).unop.baseChange ℂ
  let S := (printedAnalyticAction A f).dualMap
  have hT : ∀ x ∈ complexHolomorphicH1 A, T x ∈ complexHolomorphicH1 A := by
    intro x hx
    exact (spec_g4_abelianEnd0Action_mem_hodgeEndH1 A f).1
      (Submodule.mem_map_of_mem hx)
  have he : ∀ x : complexHolomorphicH1 A,
      holomorphicPeriodDual A ⟨T x, hT x x.property⟩ = S (holomorphicPeriodDual A x) := by
    intro x
    apply LinearMap.ext
    intro v
    change abelianPeriodComplexEquiv A (T x) v =
      abelianPeriodComplexEquiv A x (printedAnalyticAction A f v)
    exact congrArg (fun φ : DegreeOneLatticeDual (dim A.left) => φ v)
      (geometricPeriod_rational A f x)
  have hH : (abelianWeightOneHodgeStructure A).H (1, 0) = complexHolomorphicH1 A := by
    change cohomologyHodgePiece A 1 (1, 0) = _
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp only [latticeHodgePieces, ↓reduceIte]
  rw [hH]
  exact (invariantEigenspaceEquiv T S (complexHolomorphicH1 A) hT
    (holomorphicPeriodDual A) he z).finrank_eq.trans
      (tangentDual_eigenrank (printedAnalyticAction A f) z)

#print axioms geometric_holomorphic_eigenrank_aux
end HodgeLean.Foundations.Program.G32Native
