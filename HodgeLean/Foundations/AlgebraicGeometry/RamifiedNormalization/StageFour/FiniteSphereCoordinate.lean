import Mathlib.Topology.Compactification.OnePoint.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The finite part of the prescribed sphere retains its original affine coordinate. -/
def onePointFiniteHomeomorph {A : Type*} [TopologicalSpace A] :
    {z : OnePoint A // z ≠ ∞} ≃ₜ A := by
  let f : A → {z : OnePoint A // z ≠ ∞} := fun a => ⟨(a : OnePoint A), OnePoint.coe_ne_infty a⟩
  have hf : Topology.IsEmbedding f :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.codRestrict _ (fun a => OnePoint.coe_ne_infty a)
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    cases z with
    | infty => exact (hz rfl).elim
    | coe a => exact ⟨a, rfl⟩
  exact ((Equiv.ofBijective f ⟨hf.injective, hsurj⟩).toHomeomorphOfIsInducing hf.isInducing).symm

end AlgebraicGeometry.RamifiedNormalization.StageFour
