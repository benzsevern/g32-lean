import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Projectivity of a quotient in a split differential sequence -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.G32Native

/-- A quotient of a projective module by a retract is projective.
Source: Stacks Project, Tag 05CF. -/
theorem residual_projective_of_split_exact
    (R K M N : Type*) [Ring R] [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [Module R K] [Module R M] [Module R N] [Module.Projective R M]
    (f : K →ₗ[R] M) (g : M →ₗ[R] N) (s : M →ₗ[R] K)
    (hs : s.comp f = LinearMap.id) (he : Function.Exact f g)
    (hg : Function.Surjective g) : Module.Projective R N := by
  let p : M →ₗ[R] M := LinearMap.id - f.comp s
  have hp : LinearMap.ker g ≤ LinearMap.ker p := by
    intro x hx
    obtain ⟨k, rfl⟩ := (he x).mp hx
    have hsk : s (f k) = k := DFunLike.congr_fun hs k
    change f k - f (s (f k)) = 0
    rw [hsk, sub_self]
  let t : N →ₗ[R] M := g.liftOfSurjective hg ⟨p, hp⟩
  apply Module.Projective.of_split t g
  ext n
  obtain ⟨m, rfl⟩ := hg n
  change g ((g.liftOfSurjective hg) ⟨p, hp⟩ (g m)) = g m
  rw [LinearMap.equivOfSurjective_apply]
  change g (m - f (s m)) = g m
  rw [map_sub, he.apply_apply_eq_zero, sub_zero]

#print axioms residual_projective_of_split_exact
end HodgeLean.Foundations.Program.G32Native
