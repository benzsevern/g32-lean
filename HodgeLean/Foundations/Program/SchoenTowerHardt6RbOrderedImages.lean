import Mathlib.Data.Finset.Sort

/-! Order-preserving reindexing of the two staircase vertex blocks. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ordered_images {ι κ F : Type*} [Preorder ι] [Preorder κ]
    (e : ι ≃o κ) (f : κ → F) (j : ι) :
    (f ∘ e) '' {i | j ≤ i} = f '' {i | e j ≤ i} ∧
    (f ∘ e) '' {i | i ≤ j} = f '' {i | i ≤ e j} := by
  constructor
  · ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e i, e.monotone hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨e.symm i, ?_, by simp⟩
      exact e.le_iff_le.mp (by simpa using hi)
  · ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e i, e.monotone hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨e.symm i, ?_, by simp⟩
      exact e.le_iff_le.mp (by simpa using hi)

end HodgeLean.Foundations.Program
