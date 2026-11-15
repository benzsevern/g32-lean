import Mathlib

/-! # Injectivity of maps between indexed tensor products -/

open scoped TensorProduct

noncomputable section

/-- An indexed tensor product of injective linear maps over a field is injective. -/
theorem PiTensorProduct.map_injective_of_field
    {R ι : Type*} [Field R]
    (M N : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by
  classical
  choose g hg using fun i ↦
    (f i).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hf i))
  apply Function.LeftInverse.injective (g := PiTensorProduct.map g)
  intro x
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  simp only [hg, PiTensorProduct.map_id, LinearMap.id_apply]
