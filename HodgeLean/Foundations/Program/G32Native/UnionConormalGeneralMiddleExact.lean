import HodgeLean.Foundations.Program.G32Native.UnionConormalGeneralComplex

/-! # Exactness of the affine ideal tensor sequence -/
noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The natural ideal tensor sequence is exact for arbitrary surjective coordinates. -/
lemma unionConormalGeneralLast_exact
    {R B C D : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D] [Algebra B D] [Algebra C D]
    [IsScalarTower R B D] [IsScalarTower R C D]
    (hq : Function.Surjective (algebraMap R B))
    (hr : Function.Surjective (algebraMap R C))
    (hs : Function.Surjective (algebraMap C D))
    (hK : (RingHom.ker (algebraMap R B)).map (algebraMap R C) =
      RingHom.ker (algebraMap C D)) :
    Function.Exact
      ((Submodule.inclusion (show RingHom.ker (algebraMap R B) ⊓
        RingHom.ker (algebraMap R C) ≤ RingHom.ker (algebraMap R B) from inf_le_left)).baseChange B)
      (unionConormalGeneralLast (B := B) (D := D) _ _ hK) := by
  apply LinearMap.exact_of_comp_of_mem_range (unionConormalGeneralLast_comp _ hK)
  intro n hn
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective R (RingHom.ker (algebraMap R B)) B hq n
  have hx := (unionConormalGeneralLast_one_eq_zero_iff hr hs _ hK x).mp hn
  have hx' : x.val ∈ RingHom.ker (algebraMap R B) ^ 2 ⊔
      (RingHom.ker (algebraMap R B) ⊓ RingHom.ker (algebraMap R C)) := by
    rw [← unionConormal_square_intersection]
    exact ⟨x.property, hx⟩
  obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp hx'
  let y' : RingHom.ker (algebraMap R B) :=
    ⟨y, Ideal.pow_le_self (by decide : 2 ≠ 0) hy⟩
  have hy0 : (1 : B) ⊗ₜ[R] y' = 0 :=
    (unionConormal_one_tensor_eq_zero_iff hq y').mpr hy
  have hd : (⟨z, hz.1⟩ : RingHom.ker (algebraMap R B)) + y' = x := by
    apply Subtype.ext
    exact (add_comm z y).trans he
  have ht := congrArg (fun v : RingHom.ker (algebraMap R B) => (1 : B) ⊗ₜ[R] v) hd
  rw [TensorProduct.tmul_add, hy0, add_zero] at ht
  refine ⟨(1 : B) ⊗ₜ[R] (⟨z, hz⟩ : ↥(RingHom.ker (algebraMap R B) ⊓
      RingHom.ker (algebraMap R C))), ?_⟩
  rw [LinearMap.baseChange_tmul]
  exact ht

end HodgeLean.Foundations.Program.G32Native
