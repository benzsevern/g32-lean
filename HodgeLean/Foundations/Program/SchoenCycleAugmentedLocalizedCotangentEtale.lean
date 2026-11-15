import HodgeLean.Foundations.Program.SchoenCycleAugmentedLocalDifferentialBasis
import HodgeLean.Foundations.Program.SchoenCycleSmoothDifferentialFibreDimension
import HodgeLean.Foundations.Program.SchoenCyclePrescribedLocalizedEtale

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential
namespace HodgeLean.Foundations.Program

/-- Actual functions representing a cotangent basis at an augmented prime of a standard smooth algebra give actual étale coordinates on a basic neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.11.1; Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_etale_neighbourhood_of_augmented_localized_cotangent_basis
    (k S σ : Type*) [Field k] [CommRing S] [Nontrivial S] [Algebra k S] [Finite σ]
    [Algebra.IsStandardSmoothOfRelativeDimension (Nat.card σ) k S]
    (p : Ideal S) [p.IsPrime] (A : Type*) [CommRing A] [IsLocalRing A]
    [Algebra k A] [Algebra S A] [IsScalarTower k S A] [IsLocalization.AtPrime A p]
    (ε : A →ₐ[k] k)
    (c : σ → S) (hc : ∀ i, algebraMap S (A) (c i) ∈
      IsLocalRing.maximalIdeal (A))
    (b : Module.Basis σ k (IsLocalRing.maximalIdeal (A)).Cotangent)
    (hb : ∀ i, b i = (IsLocalRing.maximalIdeal (A)).toCotangent
      ⟨algebraMap S (A) (c i), hc i⟩) :
    ∃ g : S, g ∉ p ∧
      (MvPolynomial.aeval (R := k) (fun i => algebraMap S (Localization.Away g) (c i))).toRingHom.Etale := by
  letI : Algebra.IsStandardSmooth k S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (Nat.card σ)
  letI : Algebra.FormallyEtale S A := Algebra.FormallyEtale.of_isLocalization p.primeCompl
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  letI : Algebra A k := ε.toAlgebra
  letI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq' ε.comp_algebraMap.symm
  letI : Algebra S k := (ε.toRingHom.comp (algebraMap S A)).toAlgebra
  letI : IsScalarTower S A k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hε : Function.Surjective ε := fun a => ⟨algebraMap k A a, ε.commutes a⟩
  have hker : RingHom.ker (algebraMap A k) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε
  let E := (Ideal.Cotangent.equivOfEq _ _ hker.symm).restrictScalars k
  let b' := b.map E
  let c' : σ → RingHom.ker (algebraMap A k) :=
    fun i => ⟨algebraMap S A (c i), hker.symm ▸ hc i⟩
  have hb' (i : σ) : b' i = (RingHom.ker (algebraMap A k)).toCotangent (c' i) := by
    change E (b i) = _
    rw [hb]
    rfl
  let EΩ := tensorKaehlerEquivOfFormallyEtale k S A
  letI : Module.Free A Ω[A⁄k] := Module.Free.of_equiv EΩ
  letI : Module.Finite A Ω[A⁄k] := Module.Finite.of_surjective EΩ.toLinearMap EΩ.surjective
  letI : Module.FinitePresentation A Ω[A⁄k] := Module.finitePresentation_of_finite A Ω[A⁄k]
  have hdim : Module.finrank k (TensorProduct A k Ω[A⁄k]) = Nat.card σ :=
    s2e_smooth_differential_fibre_finrank k S A k (Nat.card σ)
  obtain ⟨B, hB⟩ := s2e_augmented_local_differential_basis k A σ ε c' b' hb' hdim
  exact s2e_prescribed_etale_neighbourhood_of_localized_differential_basis k S σ p A c B hB

#print axioms s2e_etale_neighbourhood_of_augmented_localized_cotangent_basis
end HodgeLean.Foundations.Program
