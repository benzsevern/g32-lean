import HodgeLean.Adapters.NormalConeB4aGysinLocalModel

/-! # Exact fibre lengths on a neighborhood of a finite flat model -/

noncomputable section
namespace HodgeLean.Adapters

/-- Near a local fibre in a finite flat finitely presented algebra, every
reduced fibre with algebraically closed residue field has as many points as
the exact length of that local fibre. No domain hypothesis on the base is needed. -/
theorem a3b4a_gysin_local_fibre_length_eq_card_nearby
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.FinitePresentation R A] [Module.Flat R A]
    (p : PrimeSpectrum R) [IsAlgClosed p.asIdeal.ResidueField]
    [IsLocalRing (p.asIdeal.Fiber A)] :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ p ∈ U ∧
      ∀ (q : PrimeSpectrum R), q ∈ U →
        ∀ [IsAlgClosed q.asIdeal.ResidueField] [IsReduced (q.asIdeal.Fiber A)],
          Module.length (p.asIdeal.Fiber A) (p.asIdeal.Fiber A) =
            (Nat.card (PrimeSpectrum (q.asIdeal.Fiber A)) : ℕ∞) := by
  obtain ⟨U, hU, hp, hrank⟩ := (Module.isLocallyConstant_rankAtStalk
    (R := R) (M := A)).exists_open p
  refine ⟨U, hU, hp, fun q hq _ _ => ?_⟩
  letI : Fintype (PrimeSpectrum (q.asIdeal.Fiber A)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    a3b4a_gysin_local_length_eq_finrank (k := p.asIdeal.ResidueField),
    ← a3b4a_gysin_reduced_finrank_eq_card (k := q.asIdeal.ResidueField),
    p.asIdeal.finrank_fiber_eq_rankAtStalk, q.asIdeal.finrank_fiber_eq_rankAtStalk,
    hrank q hq]

/-- The same neighborhood comparison retains the full local lengths when the
nearby fibres are nonreduced. -/
theorem a3b4a_gysin_local_fibre_length_eq_sum_nearby
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.FinitePresentation R A] [Module.Flat R A]
    (p : PrimeSpectrum R) [IsAlgClosed p.asIdeal.ResidueField]
    [IsLocalRing (p.asIdeal.Fiber A)] :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ p ∈ U ∧
      ∀ (q : PrimeSpectrum R), q ∈ U → ∀ [IsAlgClosed q.asIdeal.ResidueField],
        Module.length (p.asIdeal.Fiber A) (p.asIdeal.Fiber A) =
          ∑ᶠ x : PrimeSpectrum (q.asIdeal.Fiber A),
            Module.length (Localization.AtPrime x.asIdeal) (Localization.AtPrime x.asIdeal) := by
  obtain ⟨U, hU, hp, hrank⟩ := (Module.isLocallyConstant_rankAtStalk
    (R := R) (M := A)).exists_open p
  refine ⟨U, hU, hp, fun q hq _ => ?_⟩
  letI : Fintype (PrimeSpectrum (q.asIdeal.Fiber A)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype,
    ← a3b4a_gysin_finrank_eq_sum_local_lengths (k := q.asIdeal.ResidueField),
    a3b4a_gysin_local_length_eq_finrank (k := p.asIdeal.ResidueField),
    p.asIdeal.finrank_fiber_eq_rankAtStalk, q.asIdeal.finrank_fiber_eq_rankAtStalk,
    hrank q hq]

end HodgeLean.Adapters
