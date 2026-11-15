import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Data.Real.Basic

/-! In a cone complex the faces avoiding the apex are exactly the prescribed base faces. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_cone_face_restriction {E : Type*} [DecidableEq E]
    [AddCommGroup E] [Module ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (a : E) (ha : a ∉ K.space)
    (hfaces : ∀ s, s ∈ L.faces ↔ ∃ t ∈ K.faces, s ⊆ insert a t ∧ s.Nonempty) :
    ∀ s ∈ L.faces, s ∈ K.faces ↔ a ∉ s := by
  intro s hs
  constructor
  · intro hsk has
    exact ha (K.convexHull_subset_space hsk (subset_convexHull ℝ _ has))
  · intro has
    obtain ⟨t, ht, hst, hn⟩ := (hfaces s).mp hs
    apply K.down_closed ht _ hn
    intro x hx
    obtain hxa | hxt := Finset.mem_insert.mp (hst hx)
    · exact False.elim (has (hxa ▸ hx))
    · exact hxt

end HodgeLean.Foundations.Program
