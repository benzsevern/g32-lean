import HodgeLean.Foundations.Program.SchoenCycleC2ConormalPrincipalHelpers
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- A quotient between standard smooth algebras of dimensions `n + k`
and `n` has conormal bases of rank `k` on principal neighbourhoods. -/
theorem s2e_standardSmooth_conormal_principal_basis
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Nontrivial S]
    (P : Algebra.Extension R S) [IsNoetherianRing P.Ring]
    (n k : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension (n + k) R P.Ring]
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] (p : PrimeSpectrum S) :
    ∃ f : S, f ∉ p.asIdeal ∧ Nonempty (Module.Basis
      (Fin k) (Localization.Away f) (LocalizedModule.Away f P.Cotangent)) := by
  let : Algebra.IsStandardSmooth R P.Ring :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n + k)
  let : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let : Nontrivial P.Ring := (algebraMap P.Ring S).domain_nontrivial
  have ha : Module.finrank P.Ring Ω[P.Ring⁄R] = n + k := by
    simp only [Module.finrank,
      Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (n + k),
      Cardinal.toNat_natCast]
  have hs : Module.finrank S Ω[S⁄R] = n := by
    simp only [Module.finrank,
      Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n,
      Cardinal.toNat_natCast]
  apply s2e_conormal_principal_basis_of_stalk_ranks P p n k
  · change Module.rankAtStalk (S ⊗[P.Ring] Ω[P.Ring⁄R]) p = n + k
    rw [Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_finrank_of_free]
    exact ha
  · rw [Module.rankAtStalk_eq_finrank_of_free]
    exact hs

end HodgeLean.Foundations.Program
