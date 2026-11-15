import HodgeLean.Foundations.BundleResolution.ChernDefs

/-! # Literal fibre coordinates in a base chart and normal frame

The inverse product chart restricts to the original inverse linear frame.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Bundle Topology
namespace HodgeLean.Foundations.TubularEuler

theorem frame_product_inverse_fibre {B : Type} [TopologicalSpace B]
    (k : ℕ) (E : B → Type) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E)) [e.IsLinear ℂ]
    (b : OpenPartialHomeomorph B (Fin k → ℂ))
    (x : B) (hx : x ∈ e.baseSet) (hbx : x ∈ b.source) (w : Fin k → ℂ) :
    (e.toOpenPartialHomeomorph.trans (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))).symm
      (b x, w) = (⟨x, (e.continuousLinearEquivAt ℂ x hx).symm w⟩ : TotalSpace (Fin k → ℂ) E) := by
  let z : TotalSpace (Fin k → ℂ) E := ⟨x, (e.continuousLinearEquivAt ℂ x hx).symm w⟩
  let P := e.toOpenPartialHomeomorph.trans (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
  have he : e z = (x, w) := by
    rw [e.apply_eq_prod_continuousLinearEquivAt ℂ _ hx]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hz : z ∈ P.source := by
    refine ⟨e.mem_source.mpr hx, ?_⟩
    change e z ∈ (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ))).source
    rw [he]
    exact ⟨hbx, Set.mem_univ _⟩
  have hP : P z = (b x, w) := by
    change (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ))) (e z) = _
    rw [he]
    rfl
  rw [← hP]
  exact P.left_inv hz

#print axioms frame_product_inverse_fibre

end HodgeLean.Foundations.TubularEuler
