import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice

/-! Finite compatible cells inside the carrier retain the original partition and all marks. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_refinement_selection {X ι : Type*} [Fintype ι] {q m : ℕ}
    (T : ι → Set X) (A F : Set X) (hFA : F ⊆ A)
    (hne : ∀ i, (T i).Nonempty)
    (hdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hcover : (⋃ i, T i) = A)
    (hF : ∀ i, T i ⊆ F ∨ Disjoint (T i) F)
    (a : Fin q → Set X) (ha : (⋃ j, a j) = F)
    (haT : ∀ i j, T i ⊆ a j ∨ Disjoint (T i) (a j))
    (b : Fin m → Set X)
    (hbT : ∀ i j, T i ⊆ b j ∨ Disjoint (T i) (b j)) :
    ∃ k : ℕ, ∃ idx : Fin k → ι, Function.Injective idx ∧
      (∀ i, (T (idx i)).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (T (idx i)) (T (idx j))) ∧
      (⋃ i, T (idx i)) = F ∧
      (∀ i j, T (idx i) ⊆ b j ∨ Disjoint (T (idx i)) (b j)) ∧
      (∀ i, ∃ j, T (idx i) ⊆ a j) := by
  classical
  let I : Finset ι := Finset.univ.filter (fun i => T i ⊆ F)
  let e := (Fintype.equivFin I).symm
  let idx : Fin (Fintype.card I) → ι := fun i => (e i).val
  have hinj : Function.Injective idx := fun _ _ h => e.injective (Subtype.ext h)
  have hsub (i : Fin (Fintype.card I)) : T (idx i) ⊆ F :=
    (Finset.mem_filter.mp (e i).property).2
  refine ⟨Fintype.card I, idx, hinj, (fun i => hne (idx i)),
    (fun i j hij => hdis _ _ (fun he => hij (hinj he))), ?_,
    (fun i j => hbT (idx i) j), ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hsub i hi
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover.symm ▸ hFA hx)
      have hiF : T i ⊆ F := by
        rcases hF i with h | h
        · exact h
        · exact False.elim (Set.disjoint_left.mp h hi hx)
      have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiF⟩
      refine Set.mem_iUnion.mpr ⟨(Fintype.equivFin I) ⟨i, hiI⟩, ?_⟩
      simpa only [idx, e, Equiv.symm_apply_apply] using hi
  · intro i
    obtain ⟨x, hx⟩ := hne (idx i)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (ha.symm ▸ hsub i hx)
    rcases haT (idx i) j with h | h
    · exact ⟨j, h⟩
    · exact False.elim (Set.disjoint_left.mp h hx hj)

end HodgeLean.Foundations.Program
