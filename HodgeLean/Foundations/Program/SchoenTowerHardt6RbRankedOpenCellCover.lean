import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic

/-! A ranked boundary system covers its entire carrier by its actual open parts. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ranked_open_cell_cover {X ι : Type*}
    (T O : ι → Set X) (D : ι → Finset ι) (rank : ι → ℕ)
    (hD : ∀ i j, j ∈ D i → rank j < rank i)
    (hO : ∀ i, O i ⊆ T i) (hboundary : ∀ i, T i \ O i = ⋃ j : D i, T j.val) :
    (⋃ i, T i) = ⋃ i, O i := by
  classical
  have hpoint : ∀ k, ∀ i, rank i = k → T i ⊆ ⋃ j, O j := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi x hx
      by_cases hxo : x ∈ O i
      · exact Set.mem_iUnion.mpr ⟨i, hxo⟩
      · have hxb : x ∈ ⋃ j : D i, T j.val := hboundary i ▸ ⟨hx, hxo⟩
        obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxb
        exact ih (rank j.val) (hi ▸ hD i j.val j.property) j.val rfl hxj
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hpoint (rank i) i rfl hi
  · exact Set.iUnion_mono hO

end HodgeLean.Foundations.Program
