import Mathlib.RingTheory.RingHom.Etale
import HodgeLean.Foundations.Program.SchoenCycleFormalCoordinateFlatness
import HodgeLean.Foundations.Program.SchoenCycleCotangentUnramified
import HodgeLean.Foundations.Program.SchoenCycleFlatUnramifiedAtEtale
import Mathlib.RingTheory.Etale.Locus

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial KaehlerDifferential
namespace HodgeLean.Foundations.Program

/-- A coefficient formal model and actual cotangent coordinate representatives give an actual étale neighbourhood of a finite-type affine algebra, without a smoothness premise on that algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.6.1 and 17.11.1; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_etale_neighbourhood_of_formal_model
    (k S σ : Type*) [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [Finite σ]
    (p : Ideal S) [p.IsPrime] (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] [Algebra S A] [IsScalarTower k S A] [IsLocalization.AtPrime A p]
    (ε : A →ₐ[k] k)
    (E : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[k]
      AdicCompletion (idealOfVars σ k) (MvPolynomial σ k))
    (c : σ → S) (hc : ∀ i, algebraMap S A (c i) ∈ IsLocalRing.maximalIdeal A)
    (b : Module.Basis σ k (IsLocalRing.maximalIdeal A).Cotangent)
    (hb : ∀ i, b i = (IsLocalRing.maximalIdeal A).toCotangent ⟨algebraMap S A (c i), hc i⟩) :
    ∃ g : S, g ∉ p ∧
      (aeval (R := k) (fun i => algebraMap S (Localization.Away g) (c i))).toRingHom.Etale := by
  let P := MvPolynomial σ k
  let f : P →ₐ[k] S := aeval c
  let fA : P →ₐ[k] A := aeval (fun i => algebraMap S A (c i))
  letI : Algebra P S := f.toAlgebra
  letI : Algebra P A := fA.toAlgebra
  letI : IsScalarTower k P S := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' fA.comp_algebraMap.symm
  have hcomp : (IsScalarTower.toAlgHom k S A).comp f = fA := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, f, fA, aeval_X, IsScalarTower.coe_toAlgHom']
  letI : IsScalarTower P S A := IsScalarTower.of_algebraMap_eq'
    (congrArg AlgHom.toRingHom hcomp).symm
  letI : Algebra.FiniteType P S := Algebra.FiniteType.of_restrictScalars_finiteType k P S
  letI : Algebra.FinitePresentation P S := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  letI : Algebra.EssFiniteType S A := Algebra.EssFiniteType.of_isLocalization A p.primeCompl
  letI : Algebra.EssFiniteType P A := Algebra.EssFiniteType.comp P S A
  let cA : σ → IsLocalRing.maximalIdeal A := fun i => ⟨algebraMap S A (c i), hc i⟩
  letI : Module.Flat P A := s2e_polynomial_coordinates_flat_of_formal_model k A σ E cA b hb
  letI : Algebra.FormallyUnramified P A := s2e_formallyUnramified_of_source_cotangent_basis
    k P A σ ε cA b hb (fun i => ⟨X i, by change fA (X i) = _; rw [aeval_X]⟩)
  let L := Localization.AtPrime p
  let EL := (IsLocalization.algEquiv p.primeCompl A L).restrictScalars P
  letI : Module.Flat P L := Module.Flat.of_linearEquiv EL.symm.toLinearEquiv
  letI : Algebra.FormallyUnramified P L := Algebra.FormallyUnramified.of_equiv EL
  letI : Algebra.IsEtaleAt P p := s2e_isEtaleAt_of_flat_unramified_localization P S p
  obtain ⟨g, hg, het⟩ := Algebra.exists_etale_of_isEtaleAt (R := P) p
  refine ⟨g, hg, ?_⟩
  have hf : IsScalarTower.toAlgHom k P (Localization.Away g) =
      aeval (R := k) (fun i => algebraMap S (Localization.Away g) (c i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    change algebraMap P (Localization.Away g) (X i) = _
    rw [IsScalarTower.algebraMap_apply P S (Localization.Away g)]
    change algebraMap S (Localization.Away g) (f (X i)) = _
    rw [aeval_X, aeval_X]
  rw [← hf]
  exact RingHom.etale_algebraMap.mpr het

#print axioms s2e_etale_neighbourhood_of_formal_model
end HodgeLean.Foundations.Program
