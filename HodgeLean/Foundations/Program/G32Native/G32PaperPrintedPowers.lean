import HodgeLean.Foundations.Program.G32Native.G32PELFamilyGenericMember
import HodgeLean.Foundations.Program.G32Native.G32PaperActualPowers

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
open GeneralTypeIII

/-- Every rational Hodge class on every positive power of a general member
of the effective polarized PEL family is algebraic.
Source: G32 v0.18, Corollary 8.2(ii), lines 706 and 710. -/
theorem g32_final_corollary82_second_printed
    {R : PELSplitReference} (F : PELSplitFamily R) (z : PELSplitComponent R)
    (hgeneral : F.hodgeGroup z = F.genericGroup)
    (h : IsMemberOfM (finiteBetti_abelian (F.fibre z).X)
      (spec_bettiDeRhamIso_abelian (F.fibre z).X)
      (hodgeDecomposition_of_abelian (F.fibre z).X)
      (torusCohomology_cupProductOf (F.fibre z).X) (F.fibre z).W (F.fibre z).pol) :
    ∀ r : ℕ, 0 < r → ∀ q : ℕ,
      Hdg^q(g3_power (F.fibre z).X r; ℚ) ≤
        algebraicCycleClassSpan (g3_power (F.fibre z).X r) q := by
  exact g32_final_corollary82_second_c3_supplied_actual
    (F.fibre z).X (F.fibre z).W (F.fibre z).pol h
    (F.g32_generalPELMember_of_family z hgeneral h)

#print axioms g32_final_corollary82_second_printed
end HodgeLean.Foundations.Program
