import HodgeLean.Foundations.Program.SchoenCycleC2ConormalRankHelpers
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The algebra conormal has a basis on a principal neighbourhood of every
prime, with the same rank as its localization at that prime. -/
theorem s2e_conormal_principal_basis
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) [IsNoetherianRing P.Ring]
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R S]
    (p : PrimeSpectrum S) :
    ∃ f : S, f ∉ p.asIdeal ∧ Nonempty (Module.Basis
      (Fin (Module.rankAtStalk P.Cotangent p)) (Localization.Away f)
      (LocalizedModule.Away f P.Cotangent)) := by
  let : Module.Projective S P.Cotangent := s2e_conormal_projective_of_formallySmooth P
  let : Module.Finite S P.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P) (IsNoetherian.noetherian _)
  let : Module.FinitePresentation S P.Cotangent :=
    Module.finitePresentation_of_projective S P.Cotangent
  let : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl P.Cotangent) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, hrank⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P.Cotangent)
      (Localization.AtPrime p.asIdeal)
  let : Module.Free (Localization.Away f) (LocalizedModule.Away f P.Cotangent) := hfree
  let : Nontrivial (Localization.Away f) :=
    (show Localization.Away f →+* Localization.AtPrime p.asIdeal from
      IsLocalization.map (M := .powers f) (T := p.asIdeal.primeCompl) _
        (RingHom.id S) (Submonoid.powers_le.mpr hf)).domain_nontrivial
  exact ⟨f, hf, ⟨Module.finBasisOfFinrankEq _ _ hrank⟩⟩

/-- The conormal stalk rank and the quotient differential stalk rank add
to the ambient differential stalk rank. -/
theorem s2e_conormal_stalk_rank_add
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) [IsNoetherianRing P.Ring]
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R S]
    [Module.Finite S Ω[S⁄R]] (p : PrimeSpectrum S) :
    Module.rankAtStalk P.Cotangent p + Module.rankAtStalk Ω[S⁄R] p =
      Module.rankAtStalk P.CotangentSpace p := by
  let : Module.Projective S P.Cotangent := s2e_conormal_projective_of_formallySmooth P
  let : Module.Finite S P.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P) (IsNoetherian.noetherian _)
  obtain ⟨e, _, _⟩ := s2e_conormal_split_of_formallySmooth P
  have he := congrFun (Module.rankAtStalk_eq_of_equiv e) p
  simpa only [Module.rankAtStalk_prod, Pi.add_apply] using he.symm

/-- Differential stalk ranks `n + k` and `n` provide actual conormal
bases of rank `k` on principal neighbourhoods. -/
theorem s2e_conormal_principal_basis_of_stalk_ranks
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) [IsNoetherianRing P.Ring]
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R S]
    [Module.Finite S Ω[S⁄R]] (p : PrimeSpectrum S) (n k : ℕ)
    (hambient : Module.rankAtStalk P.CotangentSpace p = n + k)
    (hquotient : Module.rankAtStalk Ω[S⁄R] p = n) :
    ∃ f : S, f ∉ p.asIdeal ∧ Nonempty (Module.Basis
      (Fin k) (Localization.Away f) (LocalizedModule.Away f P.Cotangent)) := by
  have h := s2e_conormal_stalk_rank_add P p
  rw [hambient, hquotient, Nat.add_comm n k] at h
  have hrank : Module.rankAtStalk P.Cotangent p = k := Nat.add_right_cancel h
  obtain ⟨f, hf, ⟨b⟩⟩ := s2e_conormal_principal_basis P p
  exact ⟨f, hf, ⟨b.reindex (finCongr hrank)⟩⟩

end HodgeLean.Foundations.Program
