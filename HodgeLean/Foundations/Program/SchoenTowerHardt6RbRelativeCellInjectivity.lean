import Mathlib.Topology.Homeomorph.Defs

/-! An extension agreeing on the previously mapped cell boundary preserves injectivity across the two carriers. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_relative_cell_cross_injective {E F : Type*}
    [TopologicalSpace E] [TopologicalSpace F]
    (A C : Set E) (B D : Set F) (e : A ≃ₜ B) (k : C ≃ₜ D)
    (hmem : ∀ x : A, x.val ∈ C ↔ (e x).val ∈ D)
    (hagree : ∀ (x : E) (hxA : x ∈ A) (hxC : x ∈ C),
      (k ⟨x, hxC⟩).val = (e ⟨x, hxA⟩).val) :
    ∀ (x : A) (y : C), (e x).val = (k y).val → x.val = y.val := by
  intro x y hxy
  have hxC : x.val ∈ C := (hmem x).mpr (hxy ▸ (k y).property)
  have heq : k ⟨x.val, hxC⟩ = k y :=
    Subtype.ext ((hagree x.val x.property hxC).trans hxy)
  exact congrArg Subtype.val (k.injective heq)

end HodgeLean.Foundations.Program
