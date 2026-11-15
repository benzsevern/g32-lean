import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRestrictedVertices
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedPrism

/-! Shared base vertex sets carry all the restricted geometric staircase faces. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_shared_prism_face {E : Type*}
    [AddCommGroup E] [Module ℝ E] [LinearOrder E]
    (s V : Finset E) (hV : V.Nonempty) (l u : E → ℝ)
    (L : Geometry.SimplicialComplex ℝ (E × ℝ))
    (hfaces : ∀ r, r ∈ L.faces ↔ ∃ j : V,
      (↑r : Set (E × ℝ)) ⊆
        (((fun i : V => (i.val, l i.val)) '' {i | j ≤ i}) ∪
          ((fun i : V => (i.val, u i.val)) '' {i | i ≤ j})) ∧ r.Nonempty)
    (j : s) (r : Finset (E × ℝ)) (hr : r.Nonempty)
    (hrstair : (↑r : Set (E × ℝ)) ⊆
      (((fun i : s => (i.val, l i.val)) '' {i | j ≤ i}) ∪
        ((fun i : s => (i.val, u i.val)) '' {i | i ≤ j})))
    (hrV : ∀ p ∈ r, p.1 ∈ V) : r ∈ L.faces := by
  obtain ⟨k, hk⟩ := s2v_hardt6rb_restricted_staircase_vertices
    (id : E → E) Function.injective_id l u j.val V hV
  apply (hfaces r).mpr
  refine ⟨k, ?_, hr⟩
  intro p hp
  apply hk
  constructor
  · rcases hrstair hp with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact Or.inl ⟨i.val, hi, rfl⟩
    · exact Or.inr ⟨i.val, hi, rfl⟩
  · exact ⟨p.1, hrV p hp, rfl⟩

end HodgeLean.Foundations.Program
