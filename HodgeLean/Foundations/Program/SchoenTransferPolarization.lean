import HodgeLean.Foundations.Program.SchoenTransferDefs
import HodgeLean.Adapters.PolarizedHodgeAbelian
import HodgeLean.Foundations.ChowProjective

/-! The divisor input for the inverse Lefschetz construction. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

theorem s4_positive_polarization_mem_cycleSpan
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη) :
    pol ∈ cfd_cycleSpan A 1 := by
  have hh := ((spec_polarizationPositive_iff A (finiteBetti_abelian A)
    (spec_bettiDeRhamIso_abelian A) hη).mp hpos).1
  exact chowG_lefschetzOneOne_abelian A hh

end HodgeLean.Foundations.Program
