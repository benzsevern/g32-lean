import HodgeLean.Foundations.Program.G32Native.UnionConormalGenericModule
import Mathlib.RingTheory.Ideal.Operations

/-! # Generic surjectivity of the ideal-intersection map -/

noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Multiplication by an element of the second ideal lands in the intersection. -/
def unionIdealMultiply {R : Type*} [CommRing R] (I J : Ideal R)
    (a : J) : I →ₗ[R] (I ⊓ J : Ideal R) where
  toFun x := ⟨a.val * x.val, I.mul_mem_left _ x.property,
    J.mul_mem_right _ a.property⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' r x := Subtype.ext (by
    change a.val * (r * x.val) = r * (a.val * x.val)
    ring)

/-- Inclusion after multiplication is scalar multiplication on the first ideal. -/
lemma unionIdealMultiply_comp {R : Type*} [CommRing R] (I J : Ideal R) (a : J) :
    (Submodule.inclusion (inf_le_left : I ⊓ J ≤ I)).comp
      (unionIdealMultiply I J a) = a.val • (LinearMap.id : I →ₗ[R] I) := by
  ext x
  rfl

/-- After extending scalars to a field where an element of the second ideal
is nonzero, the intersection inclusion is surjective. -/
lemma unionIdeal_generic_surjective
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (I J : Ideal R) (a : J) (ha : algebraMap R K a.val ≠ 0) :
    Function.Surjective
      ((Submodule.inclusion (inf_le_left : I ⊓ J ≤ I)).baseChange K) := by
  let f := (Submodule.inclusion (inf_le_left : I ⊓ J ≤ I)).baseChange K
  let g := (unionIdealMultiply I J a).baseChange K
  have hfg (z : K ⊗[R] I) : f (g z) = algebraMap R K a.val • z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | tmul b x =>
      change b ⊗ₜ[R] (a.val • x) = algebraMap R K a.val • (b ⊗ₜ[R] x)
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      congr 1
      exact Algebra.smul_def _ _
    | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  intro z
  refine ⟨g ((algebraMap R K a.val)⁻¹ • z), ?_⟩
  rw [hfg, smul_smul, mul_inv_cancel₀ ha, one_smul]

/-- A scalar right inverse gives generic surjectivity after that scalar is inverted. -/
lemma union_generic_surjective_of_scalar_right_inverse
    {A K M N : Type*} [CommRing A] [Field K] [Algebra A K]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (g : N →ₗ[A] M) (a : A)
    (hfg : f.comp g = a • (LinearMap.id : N →ₗ[A] N))
    (ha : algebraMap A K a ≠ 0) : Function.Surjective (f.baseChange K) := by
  have h (z : K ⊗[A] N) :
      f.baseChange K (g.baseChange K z) = algebraMap A K a • z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | tmul b x =>
      simp only [LinearMap.baseChange_tmul]
      have hx : f (g x) = a • x := LinearMap.congr_fun hfg x
      rw [hx, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      congr 1
      exact Algebra.smul_def _ _
    | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  intro z
  refine ⟨g.baseChange K ((algebraMap A K a)⁻¹ • z), ?_⟩
  rw [h, smul_smul, mul_inv_cancel₀ ha, one_smul]

/-- The scalar-extended intersection map is injective between equally ranked
finite free modules if the second ideal contains a generically nonzero element. -/
lemma unionIdeal_tensor_injective
    {R A K : Type*} [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra A K]
    (I J : Ideal R)
    [Module.Free A (A ⊗[R] (I ⊓ J : Ideal R))]
    [Module.Finite A (A ⊗[R] (I ⊓ J : Ideal R))]
    [Module.Free A (A ⊗[R] I)] [Module.Finite A (A ⊗[R] I)]
    (hAK : Function.Injective (algebraMap A K))
    (hrank : Module.finrank A (A ⊗[R] (I ⊓ J : Ideal R)) =
      Module.finrank A (A ⊗[R] I))
    (a : J) (ha : algebraMap R A a.val ≠ 0) :
    Function.Injective
      ((Submodule.inclusion (inf_le_left : I ⊓ J ≤ I)).baseChange A) := by
  apply union_free_injective_of_generic_surjective hAK hrank
  apply union_generic_surjective_of_scalar_right_inverse
    _ ((unionIdealMultiply I J a).baseChange A) (algebraMap R A a.val)
  · apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [LinearMap.comp_apply, map_zero, LinearMap.smul_apply,
        LinearMap.id_apply, smul_zero]
    | tmul b x =>
      change b ⊗ₜ[R] (a.val • x) = algebraMap R A a.val • (b ⊗ₜ[R] x)
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      congr 1
      exact Algebra.smul_def _ _
    | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      rw [hx, hy]
  · simpa only [map_zero] using hAK.ne ha

#print axioms unionIdealMultiply_comp
#print axioms unionIdeal_generic_surjective
#print axioms union_generic_surjective_of_scalar_right_inverse
#print axioms unionIdeal_tensor_injective
end HodgeLean.Foundations.Program.G32Native
