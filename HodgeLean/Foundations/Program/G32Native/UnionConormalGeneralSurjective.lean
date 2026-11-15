import HodgeLean.Foundations.Program.G32Native.UnionConormalGeneralExact

/-! # Surjectivity of the affine tensor reduction -/
noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Unit tensors and surjective ideal reduction generate the last module. -/
lemma unionConormalGeneralLast_surjective
    {R B C D : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D] [Algebra B D] [Algebra C D]
    [IsScalarTower R B D] [IsScalarTower R C D]
    (hr : Function.Surjective (algebraMap R C))
    (hs : Function.Surjective (algebraMap C D))
    (I : Ideal R) (K : Ideal C) (hK : I.map (algebraMap R C) = K) :
    Function.Surjective (unionConormalGeneralLast (B := B) (D := D) I K hK) := by
  intro p
  obtain ⟨z, rfl⟩ := TensorProduct.mk_surjective C K D hs p
  obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_iff_of_surjective _ hr).mp
    (show z.val ∈ I.map (algebraMap R C) from hK.symm ▸ z.property)
  have he : unionConormalGeneralReduction I K hK ⟨x, hx⟩ = z := Subtype.ext hxe
  refine ⟨(1 : B) ⊗ₜ[R] (⟨x, hx⟩ : I), ?_⟩
  rw [unionConormalGeneralLast_one, he]
  rfl

end HodgeLean.Foundations.Program.G32Native
