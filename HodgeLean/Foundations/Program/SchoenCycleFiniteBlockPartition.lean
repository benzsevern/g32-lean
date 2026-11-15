import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Set.Finite.Range

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Any finite tuple has positive indexed collision blocks with distinct centres and an actual indexing equivalence.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_finite_tuple_block_partition
    {α : Type*} (n : ℕ) (f : Fin n → α) :
    ∃ (b : ℕ) (m : Fin b → ℕ), (∀ a, 0 < m a) ∧
      ∃ (ι : (Σ a, Fin (m a)) ≃ Fin n) (p : Fin b → α),
        Function.Injective p ∧ ∀ a j, f (ι ⟨a, j⟩) = p a := by
  classical
  let T := Set.range f
  letI : Fintype T := Fintype.ofFinite T
  let b := Fintype.card T
  let E : T ≃ Fin b := Fintype.equivFin T
  let g (i : Fin n) : Fin b := E ⟨f i, ⟨i, rfl⟩⟩
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨i, hi⟩ := (E.symm a).property
    refine ⟨i, ?_⟩
    change E ⟨f i, ⟨i, rfl⟩⟩ = a
    rw [← E.apply_symm_apply a]
    congr 1
    exact Subtype.ext hi
  let m (a : Fin b) := Fintype.card {i : Fin n // g i = a}
  have hm (a : Fin b) : 0 < m a := by
    obtain ⟨i, hi⟩ := hg a
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  let ι : (Σ a, Fin (m a)) ≃ Fin n :=
    (Equiv.sigmaCongrRight (fun a => (Fintype.equivFin {i : Fin n // g i = a}).symm)).trans
      (Equiv.sigmaFiberEquiv g)
  let p (a : Fin b) : α := (E.symm a).val
  refine ⟨b, m, hm, ι, p, ?_, ?_⟩
  · intro a a' h
    apply E.symm.injective
    exact Subtype.ext h
  · intro a j
    let i := (Fintype.equivFin {i : Fin n // g i = a}).symm j
    have hi : g i.val = a := i.property
    have he := congrArg (fun a : Fin b => (E.symm a).val) hi
    change f i.val = p a
    simpa only [g, E.symm_apply_apply] using he

#print axioms s2e_finite_tuple_block_partition
end HodgeLean.Foundations.Program
