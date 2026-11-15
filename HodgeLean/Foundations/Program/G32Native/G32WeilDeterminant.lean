import HodgeLean.RealDefs.F1569
import HodgeLean.Adapters.TorusCohomology
import HodgeLean.Adapters.AbelianHodgeDischarge
import HodgeLean.Foundations.ComplexSheafSingular
import HodgeLean.RealDefs.WeilDeterminant

/-! # G32 Theorem A on the entire quadratic determinant space -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

variable
    (W : letI := (torusCohomology_cupProductOf X).finite; HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian X)
        (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian X)
        (torusCohomology_cupProductOf X)).weight1 3)
    (pol : HQ X 2)
    (hM : IsMemberOfM (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X) W pol)

include hM

/-- G32 membership ensures positive middle degree. -/
theorem g32_quadraticDeterminant_positive :
    letI := (torusCohomology_cupProductOf X).finite
    1 ≤ Module.finrank ℂ
      ↥(W.Vs ⊓ (abelianVarietyCohomologyOf (finiteBetti_abelian X)
        (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian X)
        (torusCohomology_cupProductOf X)).weight1.H (1, 0)) := by
  letI := (torusCohomology_cupProductOf X).finite
  rw [hM.finrank_eq_three]
  norm_num

/-- Every vector of the printed quadratic determinant space maps into the rational
Weil classes by the existing cup-wedge map. -/
theorem g32_quadraticDeterminant_cup_mem_weilClassOf (w) :
    letI := (torusCohomology_cupProductOf X).finite
    ((HQ.castEquiv X (two_mul _).symm).toLinearMap ∘ₗ (cupProductOf X).cupWedgeMap _)
      (W.quadraticDeterminantInclusion
        (h10_sup_h01_eq_top (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X))
        hM.isWeilType (by norm_num) (g32_quadraticDeterminant_positive X W pol hM) w) ∈
      weilClassOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X) W hM.isWeilType := by
  letI := (torusCohomology_cupProductOf X).finite
  exact quadraticDeterminant_cup_mem_weilClassOf _ _ _ _ W hM.isWeilType _ _ w

#print axioms g32_quadraticDeterminant_cup_mem_weilClassOf
#print axioms g32_quadraticDeterminant_positive

end HodgeLean.Foundations.Program
