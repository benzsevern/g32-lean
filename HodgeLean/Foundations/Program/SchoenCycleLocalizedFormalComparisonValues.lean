import HodgeLean.Foundations.Program.SchoenCycleCanonicalLocalizationAdic
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A retained formal comparison extends through the actual prime localization and retains the prescribed actual local pullback on every local function.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_localized_formal_comparison_values
    {k S R : Type*} [CommRing k] [CommRing S] [CommRing R]
    [Algebra k S] [Algebra k R] [IsLocalRing R]
    (Q : Ideal S) [Q.IsMaximal]
    (K : Subalgebra k (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (E : AdicCompletion Q S ≃ₐ[k] K)
    (f : S →ₐ[k] R) (l : Localization.AtPrime Q →ₐ[k] R)
    (hl : ∀ s, l (algebraMap S (Localization.AtPrime Q) s) = f s)
    (hE : ∀ s, (E (AdicCompletion.of Q S s)).val =
      AdicCompletion.of (IsLocalRing.maximalIdeal R) R (f s)) :
    ∃ F : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (Localization.AtPrime Q) ≃ₐ[k] K,
      ∀ t, (F (AdicCompletion.of (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (Localization.AtPrime Q) t)).val =
          AdicCompletion.of (IsLocalRing.maximalIdeal R) R (l t) := by
  let T := Localization.AtPrime Q
  let J := IsLocalRing.maximalIdeal T
  let D := (s2e_canonical_localization_adic_equiv Q T).restrictScalars k
  let F := D.symm.trans E
  have hD (s : S) : D (AdicCompletion.of Q S s) = AdicCompletion.of J T (algebraMap S T s) := by
    have hg (n : ℕ) (s : S) (hs : s ∈ Q ^ n) : algebraMap S T s ∈ J ^ n := by
      change algebraMap S T s ∈ IsLocalRing.maximalIdeal T ^ n
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q T, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hs
    exact s2e_adic_algebra_map_of Q J (Algebra.ofId S T) hg s
  let L := (K.val.comp F.toAlgHom).comp (IsScalarTower.toAlgHom k T (AdicCompletion J T))
  let M := (IsScalarTower.toAlgHom k R
    (AdicCompletion (IsLocalRing.maximalIdeal R) R)).comp l
  have hLM : L = M := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext Q.primeCompl
    apply RingHom.ext
    intro s
    change (E (D.symm (AdicCompletion.of J T (algebraMap S T s)))).val =
      AdicCompletion.of (IsLocalRing.maximalIdeal R) R (l (algebraMap S T s))
    rw [show D.symm (AdicCompletion.of J T (algebraMap S T s)) = AdicCompletion.of Q S s from
      (D.symm_apply_eq).mpr (hD s).symm, hl, hE]
  refine ⟨F, ?_⟩
  intro t
  exact DFunLike.congr_fun hLM t

#print axioms s2e_localized_formal_comparison_values
end HodgeLean.Foundations.Program
