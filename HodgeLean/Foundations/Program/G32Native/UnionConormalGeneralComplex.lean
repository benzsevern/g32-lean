import HodgeLean.Foundations.Program.G32Native.UnionConormalGeneralKernel

/-! # The ideal tensor complex in arbitrary affine coordinates -/
noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The ideal inclusion and natural tensor reduction have zero composite. -/
lemma unionConormalGeneralLast_comp
    {R B C D : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D] [Algebra B D] [Algebra C D]
    [IsScalarTower R B D] [IsScalarTower R C D]
    (I : Ideal R)
    (hK : I.map (algebraMap R C) = RingHom.ker (algebraMap C D)) :
    (unionConormalGeneralLast (B := B) (D := D) I _ hK).comp
      ((Submodule.inclusion (show I ⊓ RingHom.ker (algebraMap R C) ≤ I from inf_le_left)).baseChange B) = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    rw [LinearMap.comp_apply, LinearMap.baseChange_tmul]
    change b • ((1 : D) ⊗ₜ[C] unionConormalGeneralReduction I _ hK
      (Submodule.inclusion inf_le_left x)) = 0
    have hx : unionConormalGeneralReduction I _ hK
        (Submodule.inclusion inf_le_left x) = 0 := by
      apply Subtype.ext
      exact x.property.2
    rw [hx, TensorProduct.tmul_zero, smul_zero]
  | add x y hx hy => simpa only [map_add, hx, hy, add_zero]

end HodgeLean.Foundations.Program.G32Native
