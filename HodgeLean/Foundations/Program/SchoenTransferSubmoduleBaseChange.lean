import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- A linear map fixing a subspace fixes its scalar extension. -/
theorem s4_baseChange_fixed {K L V : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] (U : Submodule K V) (F : V →ₗ[K] V)
    (hF : ∀ x ∈ U, F x = x) {z : L ⊗[K] V} (hz : z ∈ U.baseChange L) :
    F.baseChange L z = z := by
  have he : F.comp U.subtype = U.subtype := LinearMap.ext (fun x => hF x x.property)
  have heb := congrArg (LinearMap.baseChange L) he
  rw [LinearMap.baseChange_comp] at heb
  obtain ⟨w, rfl⟩ := hz
  exact LinearMap.congr_fun heb w

/-- A linear map annihilating a subspace annihilates its scalar extension. -/
theorem s4_baseChange_annihilates {K L V W : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (U : Submodule K V) (F : V →ₗ[K] W)
    (hF : ∀ x ∈ U, F x = 0) {z : L ⊗[K] V} (hz : z ∈ U.baseChange L) :
    F.baseChange L z = 0 := by
  have he : F.comp U.subtype = 0 := LinearMap.ext (fun x => hF x x.property)
  have heb := congrArg (LinearMap.baseChange L) he
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_zero] at heb
  obtain ⟨w, rfl⟩ := hz
  exact LinearMap.congr_fun heb w

/-- Subspace containment transports through extension of scalars. -/
theorem s4_baseChange_le {K L V : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] {U W : Submodule K V} (h : U ≤ W) :
    U.baseChange L ≤ W.baseChange L := by
  have he : U.subtype = W.subtype.comp (Submodule.inclusion h) := rfl
  rw [Submodule.baseChange, he, LinearMap.baseChange_comp]
  exact LinearMap.range_comp_le_range _ _

end HodgeLean.Foundations.Program
