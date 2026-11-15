import HodgeLean.Foundations.Program.SchoenCycleCanonicalLocalizationAdic
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A bijective retained adic map induces the canonical formal equivalence between the actual prime localizations, retaining every localized source function value.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 3 and 10. -/
theorem s2e_localized_adic_equivalence_with_values
    (A S : Type*) [CommRing A] [CommRing S] [Algebra A S]
    (I : Ideal A) [I.IsMaximal] (Q : Ideal S) [Q.IsMaximal] [Q.LiesOver I]
    (h : ∀ n a, a ∈ I ^ n → algebraMap A S a ∈ Q ^ n)
    (hbij : Function.Bijective (s2e_adic_algebra_map I Q (Algebra.ofId A S) h)) :
    let R := Localization.AtPrime I
    let T := Localization.AtPrime Q
    letI := Localization.AtPrime.algebraOfLiesOver I Q
    ∃ E : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[A]
        AdicCompletion (IsLocalRing.maximalIdeal T) T,
      ∀ r, E (AdicCompletion.of _ _ r) =
        AdicCompletion.of _ _ (algebraMap R T r) := by
  let R := Localization.AtPrime I
  let T := Localization.AtPrime Q
  letI := Localization.AtPrime.algebraOfLiesOver I Q
  let ER := s2e_canonical_localization_adic_equiv I R
  let ET := (s2e_canonical_localization_adic_equiv Q T).restrictScalars A
  let E0 := AlgEquiv.ofBijective (s2e_adic_algebra_map I Q (Algebra.ofId A S) h) hbij
  let E := ER.symm.trans (E0.trans ET)
  let L := E.toAlgHom.comp (IsScalarTower.toAlgHom A R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
  let M := (IsScalarTower.toAlgHom A T (AdicCompletion (IsLocalRing.maximalIdeal T) T)).comp
    (IsScalarTower.toAlgHom A R T)
  have he : L = M := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext I.primeCompl
    apply RingHom.ext
    intro a
    exact (L.commutes a).trans (M.commutes a).symm
  refine ⟨E, ?_⟩
  intro r
  exact DFunLike.congr_fun he r

#print axioms s2e_localized_adic_equivalence_with_values
end HodgeLean.Foundations.Program
