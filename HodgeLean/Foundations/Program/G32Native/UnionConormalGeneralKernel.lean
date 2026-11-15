import HodgeLean.Foundations.Program.G32Native.UnionConormalGeneralExact

/-! # The middle kernel in arbitrary affine coordinates -/
noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Unit-tensor vanishing reduces to the ambient square and the second kernel. -/
lemma unionConormalGeneralLast_one_eq_zero_iff
    {R B C D : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D] [Algebra B D] [Algebra C D]
    [IsScalarTower R B D] [IsScalarTower R C D]
    (hr : Function.Surjective (algebraMap R C))
    (hs : Function.Surjective (algebraMap C D))
    (I : Ideal R)
    (hK : I.map (algebraMap R C) = RingHom.ker (algebraMap C D)) (x : I) :
    unionConormalGeneralLast (B := B) (D := D) I _ hK ((1 : B) ⊗ₜ[R] x) = 0 ↔
      x.val ∈ I ^ 2 ⊔ RingHom.ker (algebraMap R C) := by
  rw [unionConormalGeneralLast_one, unionConormal_one_tensor_eq_zero_iff hs]
  change algebraMap R C x.val ∈ RingHom.ker (algebraMap C D) ^ 2 ↔ _
  rw [← hK, ← Ideal.map_pow]
  change x.val ∈ Ideal.comap (algebraMap R C) ((I ^ 2).map (algebraMap R C)) ↔ _
  rw [Ideal.comap_map_of_surjective _ hr]
  rfl

end HodgeLean.Foundations.Program.G32Native
