import HodgeLean.Foundations.Program.SchoenCycleLocalizationJets
import HodgeLean.Foundations.Program.SchoenCycleAdicRingMaps

/-! # Adic comparison with localization at a maximal ideal -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The finite localization equivalence respects the actual ring map and powers
of the extended ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 3 and 10. -/
theorem s2e_localization_finite_coordinates
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (m : Ideal R) [m.IsMaximal] [IsLocalization.AtPrime S m] (N : ℕ) :
    ∃ e : (R ⧸ m ^ N) ≃+* (S ⧸ (m.map (algebraMap R S)) ^ N),
      ∀ r, e (Ideal.Quotient.mk (m ^ N) r) =
        Ideal.Quotient.mk ((m.map (algebraMap R S)) ^ N) (algebraMap R S r) := by
  have H : ∃ e : (R ⧸ m ^ N) ≃+* (S ⧸ (m ^ N).map (algebraMap R S)),
      ∀ r, e (Ideal.Quotient.mk (m ^ N) r) =
        Ideal.Quotient.mk ((m ^ N).map (algebraMap R S)) (algebraMap R S r) :=
    ⟨(s2e_localization_power_jet_algEquiv R S m N).toRingEquiv, fun _ => rfl⟩
  rw [Ideal.map_pow] at H
  exact H

#print axioms s2e_localization_finite_coordinates

/-- Localization at a maximal ideal preserves its adic ring, via an equivalence
which carries each ring element to its image under the specified localization map.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 3 and 10. -/
theorem s2e_localization_adic_equiv
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (m : Ideal R) [m.IsMaximal] [IsLocalization.AtPrime S m] :
    ∃ E : AdicCompletion m R ≃+* AdicCompletion (m.map (algebraMap R S)) S,
      ∀ r, E (AdicCompletion.of m R r) =
        AdicCompletion.of (m.map (algebraMap R S)) S (algebraMap R S r) := by
  choose e he using s2e_localization_finite_coordinates R S m
  have hc : ∀ {a b : ℕ} (h : a ≤ b) z,
      Ideal.Quotient.factorPow (m.map (algebraMap R S)) h (e b z) =
        e a (Ideal.Quotient.factorPow m h z) := by
    intro a b h z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [he, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  obtain ⟨E, hE⟩ := s2e_adic_coordinates_equiv m (m.map (algebraMap R S)) e hc
  refine ⟨E, fun r => ?_⟩
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [hE, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, he]

#print axioms s2e_localization_adic_equiv
/-- The actual localization map induces a bijection of adic rings.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 3 and 10. -/
theorem s2e_localization_adic_map_bijective
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (m : Ideal R) [m.IsMaximal] [IsLocalization.AtPrime S m] :
    Function.Bijective (s2e_adic_ring_map m (m.map (algebraMap R S))
      (algebraMap R S) le_rfl) := by
  apply s2e_adic_ring_map_bijective
  intro n
  obtain ⟨e, he⟩ := s2e_localization_finite_coordinates R S m n
  have h : (s2e_adic_quotient_ring_map m (m.map (algebraMap R S))
      (algebraMap R S) le_rfl n : (R ⧸ m ^ n) → S ⧸ (m.map (algebraMap R S)) ^ n) = e := by
    funext z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact (he r).symm
  rw [h]
  exact e.bijective

#print axioms s2e_localization_adic_map_bijective
end HodgeLean.Foundations.Program
