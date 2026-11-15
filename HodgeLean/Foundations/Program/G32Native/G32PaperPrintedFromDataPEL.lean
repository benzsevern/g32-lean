import HodgeLean.Foundations.Program.G32Native.G32PaperPrintedFromData
import HodgeLean.Foundations.Program.G32Native.PELTypeIIIGenerality

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
open GeneralTypeIII

/-- The powers clause with generality against the member's connected PEL group.
Source: G32 v0.18, Corollary 8.2(ii), lines 706 and 710. -/
theorem g32_final_corollary82_second_printed_from_data_pel
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (pol : HQ A 2) (Q : G32Native.TypeIIIFormData A pol)
    (hdisc : Q.discriminantClass = classNegTwo)
    (hgeneral : g2_hodgeGroup (latticeHodgePieces A)
      (spec_latticeHodgePieces_isInternal A) (PELSplitReference.ofTypeIII Q).basis =
      g1_identityComponent (pelIsometryGroup
        ((PELSplitReference.ofTypeIII Q).form.map (algebraMap ℚ ℂ))
        (Set.range fun i : Fin 4 =>
          ((PELSplitReference.ofTypeIII Q).operator
            (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 Q.b i)).map
              (algebraMap ℚ ℂ)))) :
    ∀ r : ℕ, 0 < r → ∀ q : ℕ,
      Hdg^q(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) q :=
  g32_final_corollary82_second_printed_from_data A pol Q hdisc
    ((g32_from_data_generality_iff_pel Q).mpr hgeneral)

end HodgeLean.Foundations.Program
