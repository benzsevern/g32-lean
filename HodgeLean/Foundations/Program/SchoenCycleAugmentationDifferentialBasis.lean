import HodgeLean.Foundations.Program.SchoenCycleAugmentationCotangentDifferential
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential
namespace HodgeLean.Foundations.Program

/-- A cotangent basis maps to a differential fibre basis whenever the two finite dimensions agree.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8, the conormal sequence. -/
theorem s2e_augmentation_differential_basis
    (k A σ : Type*) [Field k] [CommRing A] [Algebra k A] [Finite σ]
    (ε : A →ₐ[k] k) :
    letI : Algebra A k := ε.toAlgebra
    letI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq' ε.comp_algebraMap.symm
    ∀ (b : Module.Basis σ k (RingHom.ker (algebraMap A k)).Cotangent),
      Module.finrank k (TensorProduct A k Ω[A⁄k]) = Module.finrank k (RingHom.ker (algebraMap A k)).Cotangent →
      ∃ B : Module.Basis σ k (TensorProduct A k Ω[A⁄k]),
        ∀ i, B i = kerCotangentToTensor k A k (b i) := by
  letI : Algebra A k := ε.toAlgebra
  letI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq' ε.comp_algebraMap.symm
  intro b hdim
  let f := (kerCotangentToTensor k A k).restrictScalars k
  have hf : Function.Surjective f := s2e_augmentation_cotangent_differential_surjective k A ε
  letI : Module.Finite k (RingHom.ker (algebraMap A k)).Cotangent := Module.Finite.of_basis b
  letI : Module.Finite k (TensorProduct A k Ω[A⁄k]) := Module.Finite.of_surjective f hf
  let E := LinearEquiv.ofBijective f
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).mpr hf, hf⟩
  exact ⟨b.map E, fun _ => rfl⟩

#print axioms s2e_augmentation_differential_basis
end HodgeLean.Foundations.Program
