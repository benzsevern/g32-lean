import HodgeLean.Foundations.Program.SchoenCycleAugmentationResidueEquiv
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Returning an augmented differential injection to the actual residue field -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- An injection on the original scalar augmentation fibre is an injection
on the actual residue fibre of the same local algebra.
Source: Hartshorne, Algebraic Geometry, II.8; scalar extension over fields. -/
theorem residual_residue_injective_of_augmentation
    (k A M N : Type*) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (ε : A →ₐ[k] k) (f : M →ₗ[A] N) :
    letI : Algebra A k := ε.toAlgebra
    Function.Injective (f.baseChange k) →
      Function.Injective (f.baseChange (IsLocalRing.ResidueField A)) := by
  letI : Algebra A k := ε.toAlgebra
  let E := s2e_augmentation_residue_equiv k A ε
  letI : IsScalarTower A k (IsLocalRing.ResidueField A) :=
    IsScalarTower.of_algebraMap_eq (by
      intro a
      apply E.injective
      rw [E.commutes]
      exact s2e_augmentation_residue_equiv_apply k A ε a)
  intro h
  have hi := Module.Flat.lTensor_preserves_injective_linearMap
    (f.baseChange k) h (M := IsLocalRing.ResidueField A)
  let eM := AlgebraTensorModule.cancelBaseChange A k (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField A) M
  let eN := AlgebraTensorModule.cancelBaseChange A k (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField A) N
  have hc : (f.baseChange (IsLocalRing.ResidueField A)).comp eM.toLinearMap =
      eN.toLinearMap.comp ((f.baseChange k).baseChange (IsLocalRing.ResidueField A)) := by
    ext m
    change f.baseChange (IsLocalRing.ResidueField A) (eM (1 ⊗ₜ[k] (1 ⊗ₜ[A] m))) =
      eN ((f.baseChange k).baseChange (IsLocalRing.ResidueField A) (1 ⊗ₜ[k] (1 ⊗ₜ[A] m)))
    simp only [eM, eN, LinearMap.baseChange_tmul,
      AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  intro x y hxy
  obtain ⟨x, rfl⟩ := eM.surjective x
  obtain ⟨y, rfl⟩ := eM.surjective y
  apply congrArg eM
  apply hi
  apply eN.injective
  exact (DFunLike.congr_fun hc x).symm.trans (hxy.trans (DFunLike.congr_fun hc y))

#print axioms residual_residue_injective_of_augmentation
end HodgeLean.Foundations.Program.G32Native
