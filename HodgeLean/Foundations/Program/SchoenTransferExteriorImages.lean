import Mathlib.LinearAlgebra.ExteriorPower.Basic

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Exterior powers carry a subspace image to the exterior image of that subspace. -/
theorem exterior_image_submodule {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (n : ℕ) (F : M →ₗ[K] N) (U : Submodule K M) :
    (LinearMap.range (exteriorPower.map n U.subtype)).map (exteriorPower.map n F) =
      LinearMap.range (exteriorPower.map n (U.map F).subtype) := by
  let G : U →ₗ[K] U.map F :=
    { toFun := fun x => ⟨F x, ⟨x, x.property, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (F.map_add x y)
      map_smul' := fun c x => Subtype.ext (F.map_smul c x) }
  have hG : Function.Surjective G := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hcomp : F ∘ₗ U.subtype = (U.map F).subtype ∘ₗ G := rfl
  rw [← LinearMap.range_comp, ← exteriorPower.map_comp, hcomp,
    exteriorPower.map_comp, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.mpr (exteriorPower.map_surjective hG)

end HodgeLean.Foundations.Program
