import HodgeLean.Foundations.Program.G32Native.PELSplitTransport
import HodgeLean.Foundations.HodgeGroupAlgebraic

noncomputable section
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII
namespace PELSplitFamily

/-- Each fibre group is contained in the independently defined family group. -/
theorem hodgeGroup_subset_genericGroup {R : PELSplitReference}
    (F : PELSplitFamily R) (z : PELSplitComponent R) :
    F.hodgeGroup z ⊆ F.genericGroup := by
  intro g hg G hG
  exact hG.2 z hg

/-- A fibre containing every fibre group attains the family intersection.
Source: Abdulali, Annals 155 (2002), §2.3, pp. 918–919. -/
theorem genericGroup_eq_of_dominating_fibre {R : PELSplitReference}
    (F : PELSplitFamily R) (z : PELSplitComponent R)
    (hdom : ∀ y, F.hodgeGroup y ⊆ F.hodgeGroup z) :
    F.genericGroup = F.hodgeGroup z := by
  apply Set.Subset.antisymm
  · intro g hg
    exact hg (F.hodgeGroup z)
      ⟨g2_isRatAlgSubgroup_hodgeGroup _ _ (F.basis z), hdom⟩
  · exact F.hodgeGroup_subset_genericGroup z

/-- The equality used by the powers consumer is equivalent to fibrewise
containment, in the common rational coordinates. This does not assert existence. -/
theorem general_iff_dominating {R : PELSplitReference}
    (F : PELSplitFamily R) (z : PELSplitComponent R) :
    F.hodgeGroup z = F.genericGroup ↔ ∀ y, F.hodgeGroup y ⊆ F.hodgeGroup z := by
  constructor
  · intro hz y
    rw [hz]
    exact F.hodgeGroup_subset_genericGroup y
  · intro hz
    exact (F.genericGroup_eq_of_dominating_fibre z hz).symm

/-- Printed generality relative to a dominating generic fibre implies the
precise equality consumed by the printed powers theorem.
Source: G32 v0.18, Corollary 8.2(ii), line 710; Abdulali, Annals 155 (2002), §2.3. -/
theorem general_of_generic_fibre {R : PELSplitReference}
    (F : PELSplitFamily R) (generic z : PELSplitComponent R)
    (hdom : ∀ y, F.hodgeGroup y ⊆ F.hodgeGroup generic)
    (hgeneral : F.hodgeGroup z = F.hodgeGroup generic) :
    F.hodgeGroup z = F.genericGroup :=
  hgeneral.trans (F.genericGroup_eq_of_dominating_fibre generic hdom).symm

#print axioms hodgeGroup_subset_genericGroup
#print axioms genericGroup_eq_of_dominating_fibre
#print axioms general_iff_dominating
#print axioms general_of_generic_fibre
end PELSplitFamily
end HodgeLean.Foundations.Program.GeneralTypeIII
