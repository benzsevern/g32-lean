import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ReciprocalChartTopology

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The two reciprocal chart support tests identify the prescribed zero and infinite endpoints. -/
theorem reciprocal_endpoint_supports {T : Type*}
    (a₁ a₂ : ℂ → T) (D₁ D₂ : Set T)
    (hcover : ∀ x, (∃ z, a₁ z = x) ∨ ∃ z, a₂ z = x)
    (h₁ : ∀ z, a₁ z ∈ D₁ ↔ z = 0) (h₂ : ∀ z, a₂ z ∉ D₁)
    (h₃ : ∀ z, a₁ z ∉ D₂) (h₄ : ∀ z, a₂ z ∈ D₂ ↔ z = 0)
    (E : T ≃ OnePoint ℂ) (hzero : E (a₁ 0) = ((0 : ℂ) : OnePoint ℂ))
    (hinfty : E (a₂ 0) = ∞) :
    ∀ x, (x ∈ D₁ ↔ E x = ((0 : ℂ) : OnePoint ℂ)) ∧
      (x ∈ D₂ ↔ E x = ∞) := by
  have hD₁ (x : T) : x ∈ D₁ ↔ x = a₁ 0 := by
    rcases hcover x with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · constructor
      · intro hz
        rw [(h₁ z).mp hz]
      · intro hz
        rw [hz]
        exact (h₁ 0).mpr rfl
    · constructor
      · intro hz
        exact (h₂ z hz).elim
      · intro hz
        apply False.elim
        apply h₂ z
        rw [hz]
        exact (h₁ 0).mpr rfl
  have hD₂ (x : T) : x ∈ D₂ ↔ x = a₂ 0 := by
    rcases hcover x with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · constructor
      · intro hz
        exact (h₃ z hz).elim
      · intro hz
        apply False.elim
        apply h₃ z
        rw [hz]
        exact (h₄ 0).mpr rfl
    · constructor
      · intro hz
        rw [(h₄ z).mp hz]
      · intro hz
        rw [hz]
        exact (h₄ 0).mpr rfl
  intro x
  constructor
  · rw [hD₁]
    exact ⟨fun h => h ▸ hzero, fun h => E.injective (h.trans hzero.symm)⟩
  · rw [hD₂]
    exact ⟨fun h => h ▸ hinfty, fun h => E.injective (h.trans hinfty.symm)⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
