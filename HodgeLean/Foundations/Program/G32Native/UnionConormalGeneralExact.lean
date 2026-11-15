import HodgeLean.Foundations.Program.G32Native.UnionConormalGeneralReduction
import HodgeLean.Foundations.Program.G32Native.UnionConormalTensorKernel
import HodgeLean.Foundations.Program.G32Native.UnionConormalAlgebra

/-! # Middle exactness in arbitrary affine scalar coordinates -/
noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The arbitrary-coordinate last map evaluates on unit tensor generators. -/
lemma unionConormalGeneralLast_one
    {R B C D : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D] [Algebra B D] [Algebra C D]
    [IsScalarTower R B D] [IsScalarTower R C D]
    (I : Ideal R) (K : Ideal C) (hK : I.map (algebraMap R C) = K) (x : I) :
    unionConormalGeneralLast (B := B) (D := D) I K hK ((1 : B) ⊗ₜ[R] x) =
      (1 : D) ⊗ₜ[C] unionConormalGeneralReduction I K hK x := by
  simp only [unionConormalGeneralLast, LinearMap.liftBaseChange_tmul, one_smul,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply]

end HodgeLean.Foundations.Program.G32Native
