import HodgeLean.Foundations.Program.SchoenTowerI2aCartierPairNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerI2aPairReesUniqueness

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A paired Cartier image ideal gives a unique actual Rees chart factorization
on a principal neighborhood of every prime of the integral target ring.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13, affine blowup charts. -/
theorem s2v_i2a_cartier_pair_rees_neighborhood
    (R S : Type) [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (x y : R)
    (e : (Ideal.span {φ x, φ y} : Ideal S) ≃ₗ[S] S) (p : PrimeSpectrum S) :
    ∃ s : S, s ∉ p.asIdeal ∧ s ≠ 0 ∧
      let φs := (algebraMap S (Localization.Away s)).comp φ
      ((φs x ≠ 0 ∧ ∃! ψ : s2t_reesChart (Ideal.span {x, y}) x →+* Localization.Away s,
        ψ.comp (algebraMap R _) = φs) ∨
       (φs y ≠ 0 ∧ ∃! ψ : s2t_reesChart (Ideal.span {y, x}) y →+* Localization.Away s,
        ψ.comp (algebraMap R _) = φs)) := by
  obtain ⟨s, hs, hsne, h⟩ := s2v_i2a_cartier_pair_ratio_neighborhood S (φ x) (φ y) e p
  refine ⟨s, hs, hsne, ?_⟩
  letI : IsDomain (Localization.Away s) := Localization.Away.isDomain hsne
  let φs := (algebraMap S (Localization.Away s)).comp φ
  have lift (a b : R) (ha : φs a ≠ 0) (t : Localization.Away s) (ht : φs b = φs a * t) :
      ∃! ψ : s2t_reesChart (Ideal.span {a, b}) a →+* Localization.Away s,
        ψ.comp (algebraMap R _) = φs := by
    obtain ⟨ψ, hψ, _⟩ := s2v_i2a_pair_rees_lift_to_domain R (Localization.Away s) φs a b t ha ht
    refine ⟨ψ, hψ.1, ?_⟩
    intro ψ' hψ'
    exact s2v_i2a_pair_rees_map_unique R (Localization.Away s) φs a b ha ψ' ψ hψ' hψ.1
  rcases h with ⟨hx, t, ht⟩ | ⟨hy, t, ht⟩
  · exact Or.inl ⟨hx, lift x y hx t ht⟩
  · exact Or.inr ⟨hy, lift y x hy t ht⟩

end HodgeLean.Foundations.Program
