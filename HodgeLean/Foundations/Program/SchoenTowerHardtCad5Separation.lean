import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Defs

/-! Relative openness and ambient limit separation. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_relative_separation {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hA : A ⊆ C) (hB : B ⊆ C)
    (ho : IsOpen {x : C | x.val ∈ B}) (hd : Disjoint B A) :
    Disjoint B (closure A) := by
  obtain ⟨O, hO, he⟩ := isOpen_induced_iff.mp ho
  have hBO : B ⊆ O := by
    intro x hx
    have : (⟨x, hB hx⟩ : C) ∈ {x : C | x.val ∈ B} := hx
    rw [← he] at this
    exact this
  have hOA : Disjoint O A := by
    apply Set.disjoint_left.mpr
    intro x hx ha
    have hb : x ∈ B := by
      have : (⟨x, hA ha⟩ : C) ∈ Subtype.val ⁻¹' O := hx
      rw [he] at this
      exact this
    exact Set.disjoint_left.mp hd hb ha
  exact (hOA.closure_right hO).mono_left hBO

theorem s2v_hardt_cad5_cross_parent_separation {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hA : A ⊆ C) (hd : Disjoint B C)
    (hb : Disjoint B (closure C \ C)) : Disjoint B (closure A) := by
  apply Set.disjoint_left.mpr
  intro x hx ha
  have hc : x ∈ closure C := closure_mono hA ha
  have hn : x ∉ C := fun h => Set.disjoint_left.mp hd hx h
  exact Set.disjoint_left.mp hb hx ⟨hc, hn⟩

end HodgeLean.Foundations.Program
