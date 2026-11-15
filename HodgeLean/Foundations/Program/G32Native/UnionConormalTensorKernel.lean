import Mathlib.RingTheory.Extension.Basic

/-! # Vanishing of unit tensors in a surjective conormal presentation -/
noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- A unit tensor in the kernel of a surjection vanishes exactly on the square ideal. -/
lemma unionConormal_one_tensor_eq_zero_iff
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (hq : Function.Surjective (algebraMap R B)) (x : RingHom.ker (algebraMap R B)) :
    (1 : B) ⊗ₜ[R] x = 0 ↔ x.val ∈ RingHom.ker (algebraMap R B) ^ 2 := by
  let P : Algebra.Extension R B := {
    Ring := R
    σ := fun b => (hq b).choose
    algebraMap_σ := fun b => (hq b).choose_spec }
  change (1 : B) ⊗ₜ[P.Ring] (⟨x.val, x.property⟩ : P.ker) = 0 ↔ x.val ∈ P.ker ^ 2
  rw [← P.cotangentEquiv.map_eq_zero_iff, Algebra.Extension.cotangentEquiv_tmul,
    one_smul, Algebra.Extension.Cotangent.mk_eq_zero_iff]

end HodgeLean.Foundations.Program.G32Native
