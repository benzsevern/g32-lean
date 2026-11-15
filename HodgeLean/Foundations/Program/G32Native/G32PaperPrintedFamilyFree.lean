import HodgeLean.Foundations.Program.G32Native.PELDomainFormMember
import HodgeLean.Foundations.Program.G32Native.G32PaperActualPowers

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
open GeneralTypeIII

/-- The printed general-member powers clause on retained type-III form data.
Source: G32 v0.18, Corollary 8.2(ii), lines 706 and 710. -/
theorem g32_final_corollary82_second_printed_familyfree (R : PELSplitReference)
    (Q : G32Native.TypeIIIFormData R.B.X R.B.pol)
    (hdisc : Q.discriminantClass = classNegTwo)
    (hgeneral : g2_hodgeGroup (latticeHodgePieces R.B.X)
      (spec_latticeHodgePieces_isInternal R.B.X) R.basis =
        pelDomainHodgeGroup R (pel_hodgeGenericPoint R).val) :
    ∀ r : ℕ, 0 < r → ∀ q : ℕ,
      Hdg^q(g3_power R.B.X r; ℚ) ≤ algebraicCycleClassSpan (g3_power R.B.X r) q :=
  g32_final_corollary82_second_c3_supplied_actual R.B.X _ R.B.pol _
    (generalPELMember_of_form_domain_generic R Q hdisc hgeneral)

#print axioms g32_final_corollary82_second_printed_familyfree
end HodgeLean.Foundations.Program
