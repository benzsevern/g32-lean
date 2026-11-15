import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs

/-! Pointed contractible neighborhood bases transported by the specified homeomorphism. -/
noncomputable section
set_option maxHeartbeats 400000
open TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

theorem homeomorph_contractible_basis {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y)
    (hY : ∀ (y : Y) (U : Opens Y), y ∈ U →
      ∃ V : Opens Y, y ∈ V ∧ ContractibleSpace V ∧ V ≤ U) :
    ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  intro x U hx
  let U' : Opens Y := ⟨H.symm ⁻¹' U, U.isOpen.preimage H.symm.continuous⟩
  obtain ⟨V, hxV, hcV, hVU⟩ := hY (H x) U' (by simpa [U'] using hx)
  let W : Opens X := ⟨H ⁻¹' V, V.isOpen.preimage H.continuous⟩
  refine ⟨W, hxV, (H.sets rfl).contractibleSpace_iff.mpr hcV, ?_⟩
  intro y hy
  have h := hVU hy
  simpa [U'] using h

#print axioms homeomorph_contractible_basis
end HodgeLean.Foundations.QuotientDuality
