import Mathlib.Data.Finset.Max

/-! A staircase cut induces a permissible pivot on any nonempty base face. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_pivot {ι : Type*} [LinearOrder ι]
    (I : Finset ι) (hI : I.Nonempty) (j : ι) :
    ∃ k ∈ I, (∀ i ∈ I, j ≤ i → k ≤ i) ∧
      (∀ i ∈ I, i ≤ j → i ≤ k) := by
  classical
  let J := I.filter (fun i => i ≤ j)
  by_cases hJ : J.Nonempty
  · refine ⟨J.max' hJ, (Finset.mem_filter.mp (J.max'_mem hJ)).1, ?_, ?_⟩
    · intro i hi hji
      exact ((Finset.mem_filter.mp (J.max'_mem hJ)).2).trans hji
    · intro i hi hij
      exact J.le_max' i (Finset.mem_filter.mpr ⟨hi, hij⟩)
  · refine ⟨I.min' hI, I.min'_mem hI, ?_, ?_⟩
    · intro i hi hji
      exact I.min'_le i hi
    · intro i hi hij
      exact False.elim (hJ ⟨i, Finset.mem_filter.mpr ⟨hi, hij⟩⟩)

end HodgeLean.Foundations.Program
