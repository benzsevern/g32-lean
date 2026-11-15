import HodgeLean.Foundations.Program.SchoenCycleAugmentationDifferentialBasis
import HodgeLean.Foundations.Program.SchoenCycleAugmentationFibreBasis
import Mathlib.RingTheory.LocalRing.Module

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential TensorProduct
namespace HodgeLean.Foundations.Program

/-- Actual representatives of an augmentation cotangent basis form a local differential basis when the smooth differential fibre has the expected dimension.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Nakayama's lemma. -/
theorem s2e_augmented_local_differential_basis
    (k A σ : Type*) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A] [Finite σ]
    [Module.FinitePresentation A Ω[A⁄k]] [Module.Flat A Ω[A⁄k]]
    (ε : A →ₐ[k] k) :
    letI : Algebra A k := ε.toAlgebra
    letI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq' ε.comp_algebraMap.symm
    ∀ (c : σ → RingHom.ker (algebraMap A k))
      (b : Module.Basis σ k (RingHom.ker (algebraMap A k)).Cotangent),
      (∀ i, b i = (RingHom.ker (algebraMap A k)).toCotangent (c i)) →
      Module.finrank k (TensorProduct A k Ω[A⁄k]) = Nat.card σ →
      ∃ B : Module.Basis σ A Ω[A⁄k], ∀ i, B i = D k A (c i).val := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  letI : Algebra A k := ε.toAlgebra
  letI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq' ε.comp_algebraMap.symm
  intro c b hb hdim
  obtain ⟨B, hB⟩ := s2e_augmentation_differential_basis k A σ ε b (by
    rw [hdim, Module.finrank_eq_card_basis b, Nat.card_eq_fintype_card])
  have hB' (i : σ) : B i = 1 ⊗ₜ[A] D k A (c i).val := by
    rw [hB, hb, kerCotangentToTensor_toCotangent]
  obtain ⟨C, hC⟩ := s2e_augmentation_fibre_basis k A Ω[A⁄k] σ ε
    (fun i => D k A (c i).val) B hB'
  have hC' : (TensorProduct.mk A (IsLocalRing.ResidueField A) Ω[A⁄k] 1 ∘
      (fun i => D k A (c i).val)) = C := by
    funext i
    exact (hC i).symm
  exact Module.exists_basis_of_basis_baseChange (fun i => D k A (c i).val)
    (by rw [hC']; exact C.linearIndependent) (by rw [hC']; exact C.span_eq)
    (Module.Flat.rTensor_preserves_injective_linearMap
      (IsLocalRing.maximalIdeal A).subtype Subtype.val_injective)

#print axioms s2e_augmented_local_differential_basis
end HodgeLean.Foundations.Program
