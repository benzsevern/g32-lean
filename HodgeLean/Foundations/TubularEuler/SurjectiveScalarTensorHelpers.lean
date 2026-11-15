import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! # Tensor representatives along a surjective scalar map

Every tensor has a representative with first factor one when all scalar
coefficients lift to the original ring. HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

theorem tensor_exists_one_tmul_of_surjective
    {A C N : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup N] [Module A N]
    (hs : Function.Surjective (algebraMap A C)) (t : C ⊗[A] N) :
    ∃ n : N, t = (1 : C) ⊗ₜ[A] n := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [TensorProduct.tmul_zero]⟩
  | tmul c n =>
    obtain ⟨a, rfl⟩ := hs c
    refine ⟨a • n, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  | add t u ht hu =>
    obtain ⟨n, rfl⟩ := ht
    obtain ⟨m, rfl⟩ := hu
    exact ⟨n + m, (TensorProduct.tmul_add _ _ _).symm⟩

theorem liftBaseChange_injective_of_surjective
    {A C N M : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup N] [Module A N] [AddCommGroup M] [Module A M] [Module C M]
    [IsScalarTower A C M] (f : N →ₗ[A] M)
    (hs : Function.Surjective (algebraMap A C)) (hf : Function.Injective f) :
    Function.Injective (f.liftBaseChange C) := by
  intro u v huv
  obtain ⟨n, hn⟩ := tensor_exists_one_tmul_of_surjective hs (u - v)
  have ht : f.liftBaseChange C (u - v) = 0 := by rw [map_sub, huv, sub_self]
  rw [hn, LinearMap.liftBaseChange_one_tmul] at ht
  have hzero : n = 0 := hf (ht.trans (map_zero f).symm)
  apply sub_eq_zero.mp
  rw [hn, hzero, TensorProduct.tmul_zero]

#print axioms liftBaseChange_injective_of_surjective

#print axioms tensor_exists_one_tmul_of_surjective

end HodgeLean.Foundations.TubularEuler
