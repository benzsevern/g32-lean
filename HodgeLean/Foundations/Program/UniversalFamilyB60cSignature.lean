import HodgeLean.Foundations.Program.UniversalFamilyCoverDefs
import HodgeLean.Adapters.PolarizedHodgeAbelian

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-- The member package specializes the polarized weight-one signature comparison. -/
theorem b60c_signature_from_member (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    hermSignature (b60c_H P hP) = (3, 3) := by
  have hs := (spec_isWeilType_iff_hermSignature_eq P.X
    (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
    (d := (3 : ℚ)) (by norm_num) hP.dim_eq P.W hP.nondegenerate hP.rosati hP.positive).1
    hP.isWeilType
  simpa only [b60c_H, b60c_J] using hs

end HodgeLean.Foundations.Program
