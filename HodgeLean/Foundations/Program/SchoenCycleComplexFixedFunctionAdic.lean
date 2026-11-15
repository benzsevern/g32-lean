import HodgeLean.Foundations.Program.SchoenCycleFixedPrimeAdicComparison
import HodgeLean.Foundations.Program.SchoenCycleInvariantScalarValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual fixed-function algebra at a fixed maximal prime has exactly the complex formal invariants, with the canonical inclusion values retained.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_complex_fixed_function_adic_invariants
    (C G : Type*) [CommRing C] [Algebra ℂ C] [IsNoetherianRing C]
    [Group G] [Fintype G] [MulSemiringAction G C] [SMulCommClass G ℂ C]
    (P : Ideal C) [P.IsMaximal] (hfix : ∀ g : G, g • P = P) :
    let S := FixedPoints.subalgebra ℂ C G
    let Q := P.under S
    let α := MulSemiringAction.toAlgAut G S C
    ∃ (hP : ∀ (g : G) n c, c ∈ P ^ n → α g c ∈ P ^ n)
      (hQ : ∀ n s, s ∈ Q ^ n → algebraMap S C s ∈ P ^ n)
      (E : AdicCompletion Q S ≃ₐ[ℂ]
        (⨅ g : G, AlgHom.equalizer
          (s2e_adic_algebra_map P P ((α g).toAlgHom.restrictScalars ℂ) (hP g))
          (AlgHom.id ℂ (AdicCompletion P C)) : Subalgebra ℂ (AdicCompletion P C))),
      ∀ x, (E x).val =
        s2e_adic_algebra_map Q P ((Algebra.ofId S C).restrictScalars ℂ) hQ x := by
  dsimp only
  let S := FixedPoints.subalgebra ℂ C G
  obtain ⟨hP, hQ, E, hE⟩ := s2e_fixed_prime_adic_base_comparison S C G
    (fun _ _ h => Subtype.ext h) P hfix
  refine ⟨hP, hQ,
    (E.restrictScalars ℂ).trans (s2e_invariant_restrict_scalars_equiv (k := ℂ) _), ?_⟩
  intro x
  exact hE x

#print axioms s2e_complex_fixed_function_adic_invariants
end HodgeLean.Foundations.Program
