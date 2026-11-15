import HodgeLean.Foundations.Program.SchoenCycleAdicMapBijective
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A local algebra equivalence induces the maximal-adic algebra equivalence and retains every actual function value.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_local_adic_equivalence_with_values
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsLocalRing A] [IsLocalRing B] (e : A ≃ₐ[k] B) :
    ∃ E : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[k]
        AdicCompletion (IsLocalRing.maximalIdeal B) B,
      ∀ a, E (AdicCompletion.of _ _ a) = AdicCompletion.of _ _ (e a) := by
  let I := IsLocalRing.maximalIdeal A
  let J := IsLocalRing.maximalIdeal B
  have hmap : I.map e.toRingHom = J := IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  have h (n : ℕ) (a : A) (ha : a ∈ I ^ n) : e a ∈ J ^ n := by
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  have hbij : Function.Bijective (s2e_adic_algebra_map I J e.toAlgHom h) := by
    apply s2e_adic_algebra_map_bijective
    intro n
    have hn : (I ^ n).map e.toRingHom = J ^ n := by rw [Ideal.map_pow, hmap]
    refine ⟨Ideal.quotientEquivAlg _ _ e hn.symm, ?_⟩
    intro a
    rfl
  refine ⟨AlgEquiv.ofBijective (s2e_adic_algebra_map I J e.toAlgHom h) hbij, ?_⟩
  intro a
  exact s2e_adic_algebra_map_of I J e.toAlgHom h a

#print axioms s2e_local_adic_equivalence_with_values
end HodgeLean.Foundations.Program
