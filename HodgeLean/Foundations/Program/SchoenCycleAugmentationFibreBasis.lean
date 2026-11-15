import HodgeLean.Foundations.Program.SchoenCycleAugmentationResidueEquiv
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open TensorProduct
namespace HodgeLean.Foundations.Program

/-- A basis in an augmented scalar fibre gives the same indexed basis in the actual residue fibre, preserving the actual vectors.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_augmentation_fibre_basis
    (k A M σ : Type*) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    (ε : A →ₐ[k] k) :
    letI : Algebra A k := ε.toAlgebra
    ∀ (v : σ → M) (b : Module.Basis σ k (TensorProduct A k M)),
      (∀ i, b i = 1 ⊗ₜ[A] v i) →
      ∃ B : Module.Basis σ (IsLocalRing.ResidueField A)
        (TensorProduct A (IsLocalRing.ResidueField A) M),
        ∀ i, B i = 1 ⊗ₜ[A] v i := by
  letI : Algebra A k := ε.toAlgebra
  let E := s2e_augmentation_residue_equiv k A ε
  letI : IsScalarTower A k (IsLocalRing.ResidueField A) :=
    IsScalarTower.of_algebraMap_eq (by
      intro a
      apply E.injective
      rw [E.commutes]
      exact s2e_augmentation_residue_equiv_apply k A ε a)
  intro v b hb
  let B := (b.baseChange (IsLocalRing.ResidueField A)).map
    (AlgebraTensorModule.cancelBaseChange A k (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A) M)
  refine ⟨B, ?_⟩
  intro i
  simp only [B, Module.Basis.map_apply, Module.Basis.baseChange_apply, hb,
    AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

#print axioms s2e_augmentation_fibre_basis
end HodgeLean.Foundations.Program
