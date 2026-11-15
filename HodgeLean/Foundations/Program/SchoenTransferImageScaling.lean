import Mathlib.Algebra.Module.Submodule.Map

namespace HodgeLean.Foundations.Program

/-- Pointwise agreement on a subspace gives equal image subspaces. -/
theorem submodule_image_of_agreement {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (U : Submodule K M) (F G : M →ₗ[K] N)
    (h : ∀ x ∈ U, F x = G x) : U.map F = U.map G := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (h x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, h x hx⟩

/-- A nonzero scalar in a map does not change its subspace image. -/
theorem submodule_image_of_scaled_agreement {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (U : Submodule K M) (F G : M →ₗ[K] N) (c : K) (hc : c ≠ 0)
    (h : ∀ x ∈ U, F x = c • G x) : U.map F = U.map G := by
  calc
    U.map F = U.map (c • G) := submodule_image_of_agreement U F (c • G) h
    _ = U.map G := Submodule.map_smul G U c hc

end HodgeLean.Foundations.Program
