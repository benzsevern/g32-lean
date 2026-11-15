import HodgeLean.Foundations.Program.SchoenCycleC1MarkedLabelEquiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The original signed coefficient product over the marked points of a
selected tuple is the product over its occurring original labels. -/
theorem s2e_c1_marked_product_reindex
    {I P M : Type*} [Fintype I] [DecidableEq P] [CommMonoid M]
    (marks : I → P) (hinj : Function.Injective marks) (A : Finset P)
    (F : A → M) :
    (∏ j ∈ Finset.univ.filter (fun j : A => ∃ i, j.val = marks i), F j) =
      ∏ i : {i : I // marks i ∈ A}, F ⟨marks i.val, i.property⟩ := by
  classical
  obtain ⟨e, he⟩ := s2e_c1_marked_label_equiv marks hinj A
  rw [Finset.prod_subtype (p := fun j : A => ∃ i, j.val = marks i) _ (by simp)]
  symm
  apply Fintype.prod_equiv e
  intro i
  congr 1
  exact Subtype.ext (he i).symm

end HodgeLean.Foundations.Program
