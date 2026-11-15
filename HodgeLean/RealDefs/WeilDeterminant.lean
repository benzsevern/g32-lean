import HodgeLean.RealDefs.WeilClasses
import HodgeLean.Blocks.Weil.QuadraticDeterminant

/-! # Transport of the quadratic determinant through the cup-wedge map -/

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
noncomputable section

namespace HodgeLean.RealDefs

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [GrpObj X] {μ : CupProduct X}
  (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
  (hT : TorusCohomology μ)

variable {d : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ -d + 0 * r)]
    (A : letI := hT.finite; HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (hd : 0 < d)
    (hκ : letI := hT.finite; 1 ≤ Module.finrank ℂ
      ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)))

/-- A quadratic determinant vector carried by the same cup-wedge map as
`WeilClassesAlgebraic` belongs to `weilClassOf`. -/
theorem quadraticDeterminant_cup_mem_weilClassOf (w) :
    letI := hT.finite
    ((HQ.castEquiv X (two_mul _).symm).toLinearMap ∘ₗ μ.cupWedgeMap _)
      (A.quadraticDeterminantInclusion (h10_sup_h01_eq_top hF hB hD hT) hW hd hκ w) ∈
      weilClassOf hF hB hD hT A hW := by
  letI := hT.finite
  exact ⟨_, A.quadraticDeterminantInclusion_mem
    (h10_sup_h01_eq_top hF hB hD hT) hW hd hκ w, rfl⟩

/-- Algebraicity of the rational Weil space applies to every quadratic determinant vector. -/
theorem quadraticDeterminant_cup_algebraic
    (hWA : WeilClassesAlgebraic hF hB hD hT A hW) (w) :
    letI := hT.finite
    ((HQ.castEquiv X (two_mul _).symm).toLinearMap ∘ₗ μ.cupWedgeMap _)
      (A.quadraticDeterminantInclusion (h10_sup_h01_eq_top hF hB hD hT) hW hd hκ w) ∈
      algebraicCycleClassSpan X (Module.finrank ℂ
        ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0))) := by
  letI := hT.finite
  exact hWA (quadraticDeterminant_cup_mem_weilClassOf hF hB hD hT A hW hd hκ w)

#print axioms quadraticDeterminant_cup_mem_weilClassOf
#print axioms quadraticDeterminant_cup_algebraic

end HodgeLean.RealDefs
