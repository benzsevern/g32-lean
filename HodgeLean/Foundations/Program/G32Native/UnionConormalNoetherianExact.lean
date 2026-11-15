import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Noetherian.Orzech

/-! # Determining a noetherian quotient from an epic comparison -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- With a noetherian last module, any surjective last arrow annihilating
an already specified kernel gives the same middle exactness. -/
lemma unionConormal_exact_of_noetherian_quotient
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [IsNoetherian R P]
    (f : M →ₗ[R] N) (g₀ g : N →ₗ[R] P)
    (he : Function.Exact f g₀) (hg₀ : Function.Surjective g₀)
    (hz : g.comp f = 0) (hg : Function.Surjective g) : Function.Exact f g := by
  have hk : LinearMap.ker g₀ ≤ LinearMap.ker g := by
    rw [he.linearMap_ker_eq]
    rintro n ⟨m, rfl⟩
    exact LinearMap.congr_fun hz m
  let a : P →ₗ[R] P := g₀.liftOfSurjective hg₀ ⟨g, hk⟩
  have ha (n : N) : a (g₀ n) = g n := LinearMap.equivOfSurjective_apply hg₀ hk
  have has : Function.Surjective a := by
    intro p
    obtain ⟨n, hn⟩ := hg p
    exact ⟨g₀ n, (ha n).trans hn⟩
  have hai := IsNoetherian.injective_of_surjective_endomorphism a has
  intro n
  rw [← ha n, ← a.map_zero, hai.eq_iff]
  exact he n

#print axioms unionConormal_exact_of_noetherian_quotient
end HodgeLean.Foundations.Program.G32Native
