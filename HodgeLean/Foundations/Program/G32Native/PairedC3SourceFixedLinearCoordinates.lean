import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! # Ambient coordinates retaining the original source vectors -/

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [Module.Finite K U]

/-- Two embeddings of the same finite-dimensional source differ by an ambient
linear automorphism which retains the source vector exactly.
Source: Mathlib.LinearAlgebra.FiniteDimensional.Basic,
`Submodule.exists_linearEquiv_restrict_eq`. -/
theorem paired_c3_source_fixed_ambient_coordinates
    (f g : U →ₗ[K] V) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ e : V ≃ₗ[K] V, ∀ u, e (f u) = g u := by
  let ef := LinearEquiv.ofInjective f hf
  let eg := LinearEquiv.ofInjective g hg
  let a : LinearMap.range f ≃ₗ[K] LinearMap.range g := ef.symm.trans eg
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq a
  refine ⟨e, fun u => ?_⟩
  have h := he (ef u)
  change (a (ef u) : V) = e (f u) at h
  simpa only [a, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    eg, LinearEquiv.ofInjective_apply] using h.symm

/-- The same ambient automorphism identifies the projective embeddings,
with the identity map on their projective source. -/
theorem paired_c3_source_fixed_projective_coordinates
    (f g : U →ₗ[K] V) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ e : V ≃ₗ[K] V,
      Projectivization.map e.toLinearMap e.injective ∘ Projectivization.map f hf =
        Projectivization.map g hg := by
  obtain ⟨e, he⟩ := paired_c3_source_fixed_ambient_coordinates f g hf hg
  refine ⟨e, ?_⟩
  funext p
  induction p using Projectivization.ind with
  | h u hu =>
    change Projectivization.mk K (e (f u)) _ = Projectivization.mk K (g u) _
    congr 1
    exact he u

#print axioms paired_c3_source_fixed_ambient_coordinates
#print axioms paired_c3_source_fixed_projective_coordinates

end HodgeLean.Foundations.Program.G32Native
