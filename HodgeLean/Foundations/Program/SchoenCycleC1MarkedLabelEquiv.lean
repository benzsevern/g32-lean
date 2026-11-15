import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.EquivFin

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Distinct original marks identify the marked points in a selected tuple
with precisely those original labels that occur in that tuple. -/
theorem s2e_c1_marked_label_equiv
    {I P : Type*} [Fintype I] [DecidableEq P]
    (marks : I → P) (hinj : Function.Injective marks) (A : Finset P) :
    ∃ e : {i : I // marks i ∈ A} ≃ {j : A // ∃ i, j.val = marks i},
      ∀ i, (e i).val.val = marks i.val := by
  classical
  let f : {i : I // marks i ∈ A} → {j : A // ∃ i, j.val = marks i} :=
    fun i => ⟨⟨marks i.val, i.property⟩, i.val, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      apply Subtype.ext
      apply hinj
      exact congrArg (fun x => x.val.val) h
    · intro j
      obtain ⟨i, hi⟩ := j.property
      refine ⟨⟨i, hi ▸ j.val.property⟩, ?_⟩
      apply Subtype.ext
      exact Subtype.ext hi.symm
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

end HodgeLean.Foundations.Program
