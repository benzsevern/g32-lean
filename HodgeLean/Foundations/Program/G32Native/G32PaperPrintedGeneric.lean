import HodgeLean.Foundations.Program.G32Native.G32PaperPrintedReferencePowers
import HodgeLean.Foundations.Program.G32Native.PELReferenceMembership
import HodgeLean.Foundations.Program.G32Native.PELGenericFibre

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
open GeneralTypeIII

/-- Equality with the selected Hodge-generic fibre supplies the printed
family comparison for all positive powers, from reference membership. -/
theorem g32_final_corollary82_second_printed_generic
    {R : PELSplitReference} (F : PELSplitFamily R) (z : PELSplitComponent R)
    (hgeneral : F.hodgeGroup z = F.hodgeGroup (pel_hodgeGenericFibre F))
    (h : IsMemberOfM (finiteBetti_abelian R.B.X)
      (spec_bettiDeRhamIso_abelian R.B.X) (hodgeDecomposition_of_abelian R.B.X)
      (torusCohomology_cupProductOf R.B.X) R.B.W R.B.pol) :
    ∀ r : ℕ, 0 < r → ∀ q : ℕ,
      Hdg^q(g3_power (F.fibre z).X r; ℚ) ≤
        algebraicCycleClassSpan (g3_power (F.fibre z).X r) q :=
  @g32_final_corollary82_second_printed_of_reference R F z
    (F.general_of_generic_fibre (pel_hodgeGenericFibre F) z
      (pel_hodgeGenericFibre_contains F) hgeneral) h

#print axioms g32_final_corollary82_second_printed_generic
end HodgeLean.Foundations.Program
