import HodgeLean.Foundations.Program.G32Native.PELSplitReferenceFromTypeIII
import HodgeLean.Foundations.Program.G32Native.G32PaperPrintedFamilyFree

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
open GeneralTypeIII

/-- The printed general-member powers clause with the reference constructed from the form.
Source: G32 v0.18, Corollary 8.2(ii), lines 706 and 710. -/
theorem g32_final_corollary82_second_printed_from_data
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (pol : HQ A 2) (Q : G32Native.TypeIIIFormData A pol)
    (hdisc : Q.discriminantClass = classNegTwo)
    (hgeneral : g2_hodgeGroup (latticeHodgePieces A)
      (spec_latticeHodgePieces_isInternal A) (PELSplitReference.ofTypeIII Q).basis =
        pelDomainHodgeGroup (PELSplitReference.ofTypeIII Q)
          (pel_hodgeGenericPoint (PELSplitReference.ofTypeIII Q)).val) :
    ∀ r : ℕ, 0 < r → ∀ q : ℕ,
      Hdg^q(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) q :=
  g32_final_corollary82_second_printed_familyfree
    (PELSplitReference.ofTypeIII Q) Q hdisc hgeneral

#print axioms g32_final_corollary82_second_printed_from_data
end HodgeLean.Foundations.Program
