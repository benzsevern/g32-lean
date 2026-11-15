import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.Defs

/-! # Field evaluation and integral-ring actions
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageThree

theorem fieldCoeff_spec {K : Type} [Field K] {V : Scheme} (η : Spec ↧K ⟶ V) :
    Spec.map (CommRingCat.ofHom (fieldCoeff η)) = η ≫ V.toSpecΓ := by
  change Spec.map (η.appTop ≫ (Scheme.ΓSpecIso ↧K).hom) = _
  rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, Scheme.toSpecΓ_naturality]

def integralAction {A K : Type} [CommRing A] [Field K] (f : A →+* K)
    (σ : K ≃+* K) (hσ : ∀ a, σ (f a) = f a) :
    normalizedChart f ≃+* normalizedChart f := by
  letI := f.toAlgebra
  let e : K ≃ₐ[A] K := { σ with commutes' := hσ }
  have hmem (x : K) : x ∈ normalizedChart f ↔ e x ∈ normalizedChart f := by
    change _root_.IsIntegral A x ↔ _root_.IsIntegral A (e x)
    exact (isIntegral_algHom_iff e.toAlgHom e.injective).symm
  exact {
    toFun := fun b => ⟨σ b, (hmem b).mp b.property⟩
    invFun := fun b => ⟨σ.symm b, (hmem (σ.symm b)).mpr (by
      change σ (σ.symm (b : K)) ∈ normalizedChart f
      rw [σ.apply_symm_apply]
      exact b.property)⟩
    left_inv := fun b => Subtype.ext (σ.symm_apply_apply b)
    right_inv := fun b => Subtype.ext (σ.apply_symm_apply b)
    map_mul' := fun a b => Subtype.ext (σ.map_mul a b)
    map_add' := fun a b => Subtype.ext (σ.map_add a b) }

end AlgebraicGeometry.RamifiedNormalization.StageThree
