import HodgeLean.Foundations.Program.SchoenCyclePrescribedDifferentialEtale
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential
namespace HodgeLean.Foundations.Program

/-- A prescribed differential basis at a prime of a smooth algebra extends to actual étale coordinates on one basic neighbourhood of that prime.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.11.1. -/
theorem s2e_prescribed_etale_neighbourhood_of_localized_differential_basis
    (R S σ : Type*) [CommRing R] [IsNoetherianRing R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] [Finite σ]
    (p : Ideal S) [p.IsPrime] (A : Type*) [CommRing A]
    [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [IsLocalization.AtPrime A p] (c : σ → S)
    (b : Module.Basis σ (A) Ω[A⁄R])
    (hb : ∀ i, b i = D R (A) (algebraMap S (A) (c i))) :
    ∃ g : S, g ∉ p ∧
      (MvPolynomial.aeval (R := R) (fun i => algebraMap S (Localization.Away g) (c i))).toRingHom.Etale := by
  classical
  let e : (σ →₀ S) →ₗ[S] Ω[S⁄R] := Finsupp.linearCombination S (fun i => D R S (c i))
  let l₁ : (σ →₀ S) →ₗ[S] (σ →₀ A) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (A))
  let l₂ : Ω[S⁄R] →ₗ[S] Ω[A⁄R] := map R R S (A)
  let eₚ : (σ →₀ A) →ₗ[A] Ω[A⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (A) e
  have heₚ : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e (l₁ (Finsupp.single i 1))
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb]
  have he : Function.Bijective eₚ := by
    rw [heₚ]
    exact b.repr.symm.bijective
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ he
  let l₁ₜ : (σ →₀ S) →ₗ[S] (σ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ : Ω[S⁄R] →ₗ[S] Ω[Localization.Away g⁄R] := map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ : (σ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  let bₜ : Module.Basis σ (Localization.Away g) Ω[Localization.Away g⁄R] :=
    .ofRepr (LinearEquiv.ofBijective eₜ h).symm
  refine ⟨g, hg, s2e_prescribed_polynomial_etale_of_differential_basis R (Localization.Away g) σ
    (fun i => algebraMap S (Localization.Away g) (c i)) bₜ ?_⟩
  intro i
  simp +zetaDelta [IsLocalizedModule.map_linearCombination]

#print axioms s2e_prescribed_etale_neighbourhood_of_localized_differential_basis
end HodgeLean.Foundations.Program
