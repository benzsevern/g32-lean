import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

/-! A nonempty finite chain of vertex sets has a largest face. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_chain_max {ι : Type*}
    (C : Finset (Finset ι)) (hC : C.Nonempty)
    (hchain : ∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S) :
    ∃ S ∈ C, ∀ T ∈ C, T ⊆ S := by
  obtain ⟨S, hS, hmax⟩ := C.exists_max_image Finset.card hC
  refine ⟨S, hS, ?_⟩
  intro T hT
  rcases hchain T hT S hS with hTS | hST
  · exact hTS
  · exact (Finset.eq_of_subset_of_card_le hST (hmax T hT)).symm.subset

end HodgeLean.Foundations.Program
