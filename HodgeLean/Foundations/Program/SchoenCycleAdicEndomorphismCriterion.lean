import HodgeLean.Foundations.Program.SchoenCycleNoetherianRingEndomorphism
import HodgeLean.Foundations.Program.SchoenCycleAugmentationResidueEquiv
import Mathlib.RingTheory.AdicCompletion.Functoriality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An endomorphism preserving the maximal ideal as an extended ideal is bijective on a Noetherian maximal-adic local algebra with its scalar residue augmentation.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 7 and 10. -/
theorem s2e_adic_augmented_endomorphism_bijective
    (k R : Type*) [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra k R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (ε : R →ₐ[k] k) (f : R →ₐ[k] R)
    (hmap : (IsLocalRing.maximalIdeal R).map f.toRingHom = IsLocalRing.maximalIdeal R) :
    Function.Bijective f := by
  let E := s2e_augmentation_residue_equiv k R ε
  have hs : Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp f.toRingHom) := by
    intro z
    refine ⟨algebraMap k R (E z), ?_⟩
    apply E.injective
    change E (IsLocalRing.residue R (f (algebraMap k R (E z)))) = E z
    rw [f.commutes]
    change E (algebraMap k (IsLocalRing.ResidueField R) (E z)) = E z
    exact E.commutes (E z)
  letI : IsHausdorff ((IsLocalRing.maximalIdeal R).map f.toRingHom) R :=
    hmap.symm ▸ inferInstance
  have hf : Function.Surjective f :=
    surjective_of_mk_map_comp_surjective
      (I := IsLocalRing.maximalIdeal R) f.toRingHom (by rw [hmap]; exact hs)
  exact ⟨s2e_noetherian_ring_endomorphism_injective R f.toRingHom hf, hf⟩

#print axioms s2e_adic_augmented_endomorphism_bijective
end HodgeLean.Foundations.Program
