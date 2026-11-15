import HodgeLean.Foundations.Program.G32Native.G32PaperPrintedPowers
import HodgeLean.Foundations.Program.G32Native.PELReferenceMembership

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
open GeneralTypeIII

/-- Every rational Hodge class on every positive power of a general member
of the effective polarized PEL family is algebraic, using reference membership.
Source: G32 v0.18, Corollary 8.2(ii), lines 706 and 710. -/
theorem g32_final_corollary82_second_printed_of_reference
    {R : PELSplitReference} (F : PELSplitFamily R) (z : PELSplitComponent R)
    (hgeneral : F.hodgeGroup z = F.genericGroup)
    (h : IsMemberOfM (finiteBetti_abelian R.B.X)
      (spec_bettiDeRhamIso_abelian R.B.X) (hodgeDecomposition_of_abelian R.B.X)
      (torusCohomology_cupProductOf R.B.X) R.B.W R.B.pol) :
    ∀ r : ℕ, 0 < r → ∀ q : ℕ,
      Hdg^q(g3_power (F.fibre z).X r; ℚ) ≤
        algebraicCycleClassSpan (g3_power (F.fibre z).X r) q :=
  @g32_final_corollary82_second_printed R F z hgeneral
    (@PELSplitFamily.member_of_reference R F h z)

#print axioms g32_final_corollary82_second_printed_of_reference
end HodgeLean.Foundations.Program
