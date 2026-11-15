import HodgeLean.Foundations.Program.SchoenCycleStep1Field
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A retained original-field symmetry preserving the generic base square is linear over the same original base field and retains its exact order. -/
theorem original_generic_field_symmetry
    {L : Type} [Field L] (X : Scheme) [IsIntegral X]
    (η : Spec ↧L ⟶ X) (κ : X.functionField →+* L)
    (hκ : Spec.map (CommRingCat.ofHom κ) ≫ X.fromSpecStalk (genericPoint X) = η)
    (σ : L ≃+* L)
    (hσ : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ η = η) :
    letI := κ.toAlgebra
    ∃ δ : L ≃ₐ[X.functionField] L, δ.toRingEquiv = σ ∧ orderOf δ = orderOf σ := by
  letI := κ.toAlgebra
  have hfix : σ.toRingHom.comp κ = κ := by
    change (CommRingCat.ofHom (σ.toRingHom.comp κ)).hom = (CommRingCat.ofHom κ).hom
    apply CommRingCat.hom_ext_iff.mp
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    change Spec.map (CommRingCat.ofHom κ ≫ CommRingCat.ofHom σ.toRingHom) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, hκ, hσ]
  let δ : L ≃ₐ[X.functionField] L := { σ with
    commutes' := fun x => DFunLike.congr_fun hfix x }
  let f : (L ≃ₐ[X.functionField] L) →* (L ≃+* L) :=
    { toFun := AlgEquiv.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
  refine ⟨δ, rfl, ?_⟩
  exact (orderOf_injective f AlgEquiv.toRingEquiv_injective δ).symm

end AlgebraicGeometry.RamifiedNormalization.StageFour
