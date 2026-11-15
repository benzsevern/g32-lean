import HodgeLean.Foundations.Program.G32Native.G32PaperFinalC3
import HodgeLean.Foundations.Program.G32Native.TypeIIIFormDiscriminantNorm

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Corollary 8.2 first clause with −b disc(T) = −2 imposed on the intrinsic
class of the supplied form, before any choice of orthogonal presentation. -/
theorem g32_c3_final_corollary82_first_of_form_intrinsic (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (pol : HQ A 2) (F : G32Native.TypeIIIFormData A pol)
    (hdisc : F.discriminantClass = classNegTwo) :
    let Q := F.diagonal
    let hd := F.discriminantClass_eq.symm.trans hdisc
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
        (G32Native.typeIIIWeilAction Q)
        (G32Native.typeIII_member_of_discriminant Q hd).isWeilType := by
  exact g32_c3_final_corollary82_first A pol F.diagonal
    (F.discriminantClass_eq.symm.trans hdisc)

end HodgeLean.Foundations.Program
#print axioms HodgeLean.Foundations.Program.g32_c3_final_corollary82_first_of_form_intrinsic
