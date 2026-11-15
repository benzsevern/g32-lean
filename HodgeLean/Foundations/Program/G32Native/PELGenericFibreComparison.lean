import HodgeLean.Foundations.Program.G32Native.PELGenericMemberScope

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII
namespace PELSplitFamily
variable {R : PELSplitReference} (F : PELSplitFamily R)

/-- A fibre containing all marked fibre groups attains the family intersection. -/
theorem genericGroup_eq_of_generic_fibre (g : PELSplitComponent R)
    (hg : ∀ z, F.hodgeGroup z ⊆ F.hodgeGroup g) :
    F.genericGroup = F.hodgeGroup g :=
  F.genericGroup_eq_of_dominating_fibre g hg

end PELSplitFamily
#print axioms PELSplitFamily.genericGroup_eq_of_generic_fibre
end HodgeLean.Foundations.Program.GeneralTypeIII
