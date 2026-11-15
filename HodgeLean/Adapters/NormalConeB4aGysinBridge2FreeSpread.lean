import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Localization.Finiteness

/-! # Reformulated bridge of A3-B4a: spreading freeness from the generic point

A finite module over a Noetherian domain is free, of one rank `n`, at every prime of a nonempty
basic open: its localization at the generic point is a vector space, the free locus is open and
the rank is locally constant on it. Source: Matsumura, *Commutative Ring Theory*, Theorem 4.10;
Stacks Project, Tag 00NX. -/

noncomputable section
namespace HodgeLean.Adapters
open Module PrimeSpectrum

/-- A finite module over a Noetherian domain is free of a fixed rank `n` at every prime outside
the zero locus of a nonzero element. Source: Stacks Project, Tag 00NX. -/
theorem a3b4g_exists_free_rank_basicOpen {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ r : R, r ≠ 0 ∧ ∃ n : ℕ, ∀ (Q : Ideal R) [Q.IsPrime], r ∉ Q →
      Nonempty (LocalizedModule Q.primeCompl M ≃ₗ[Localization.AtPrime Q]
        (Fin n → Localization.AtPrime Q)) := by
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  let p0 : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have h0 : p0 ∈ freeLocus R M := by
    rw [mem_freeLocus]
    have : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
      simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal R).primeCompl)
    letI : Field (Localization.AtPrime (⊥ : Ideal R)) := IsFractionRing.toField R
    exact Module.Free.of_divisionRing _ _
  let U : Set (PrimeSpectrum R) := Subtype.val ''
    {x : freeLocus R M | rankAtStalk M x.1 = rankAtStalk M p0}
  have hU : IsOpen U := by
    refine (isOpen_freeLocus.isOpenEmbedding_subtypeVal).isOpenMap _ ?_
    exact isLocallyConstant_rankAtStalk_freeLocus.isOpen_fiber _
  have h0U : p0 ∈ U := ⟨⟨p0, h0⟩, rfl, rfl⟩
  obtain ⟨_, ⟨r, rfl⟩, hr, hrU⟩ :=
    isTopologicalBasis_basic_opens.exists_subset_of_mem_open h0U hU
  refine ⟨r, fun h => hr (by simp [p0, h]), rankAtStalk M p0, fun Q _ hQ => ?_⟩
  obtain ⟨⟨x, hx⟩, hrank, hxQ⟩ := hrU (show (⟨Q, inferInstance⟩ : PrimeSpectrum R) ∈
    (basicOpen r : Set (PrimeSpectrum R)) from hQ)
  subst hxQ
  have : Module.Free (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M) := hx
  have hfin : Module.finrank (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M) =
      rankAtStalk M p0 := hrank
  exact ⟨(Module.finBasisOfFinrankEq _ _ hfin).equivFun⟩

end HodgeLean.Adapters
