import HodgeLean.Foundations.Program.SchoenTowerI2aKummerGenerator

/-! # Cyclic Galois data from the actual fixed elements
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A finite extension whose specified automorphism has exactly the base field as its fixed elements is cyclic Galois with that generator.
Source: Mathlib, IsGalois.of_fixedField_eq_bot and IntermediateField.fixingSubgroup_fixedField. -/
theorem s2v_i2a_cyclic_galois_of_fixed_elements
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (d : K ≃ₐ[F] K)
    (hfixed : ∀ x : K, d x = x → x ∈ Set.range (algebraMap F K)) :
    IsGalois F K ∧ ∀ σ : K ≃ₐ[F] K, σ ∈ Subgroup.zpowers d := by
  have hz : IntermediateField.fixedField (Subgroup.zpowers d) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [IntermediateField.mem_bot]
    exact hfixed x ((IntermediateField.mem_fixedField_iff _ _).mp hx d (Subgroup.mem_zpowers d))
  have ht : IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [IntermediateField.mem_bot]
    exact hfixed x ((IntermediateField.mem_fixedField_iff _ _).mp hx d (Subgroup.mem_top d))
  refine ⟨IsGalois.of_fixedField_eq_bot F K ht, ?_⟩
  have H := IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers d)
  rw [hz, IntermediateField.fixingSubgroup_bot] at H
  intro σ
  rw [← H]
  exact Subgroup.mem_top σ

end HodgeLean.Foundations.Program
