import HodgeLean.Foundations.Program.MilneCentralizer
import HodgeLean.Papers.PapersLefschetzAbelian

/-! # Rational degree-two comparison operator

Concrete contraction coordinates for Milne's divisor comparison.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

/-- The contraction matrix of a degree-two class relative to a polarization.
Source: Milne, Lefschetz classes on abelian varieties (1999), §1,
Proposition 1.3, in the dual H¹ convention. -/
def m2_operator (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (d : HQ J 2) : Module.End ℚ (HQ J 1) :=
  contract (polarizationVec (torusCohomology_cupProductOf J) d) ∘ₗ
    (contractEquiv hη).symm.toLinearMap

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) :
    m2_operator J pol hη pol = 1 := by
  ext x
  exact contract_contractEquiv_symm hη x

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (q : ℚ) (d : HQ J 2) :
    m2_operator J pol hη (q • d) = q • m2_operator J pol hη d := by
  simp only [m2_operator, polarizationVec, map_smul, LinearMap.smul_comp]

end HodgeLean.Foundations.Program
