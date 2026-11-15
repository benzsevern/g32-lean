import HodgeLean.Foundations.Program.G32Native.PELIntegralOperators

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The integral homology action induces a contravariant rational dual action.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.2–1.3. -/
def integralOrderPullback {O : Type*} [Ring O] {Λ : Type} [AddCommGroup Λ]
    (σ : O →+* Module.End ℤ Λ) : O →+* (Module.End ℚ (b2b_dual Λ))ᵐᵒᵖ where
  toFun a := MulOpposite.op (b60b_dualPrecomp (σ a).toAddMonoidHom)
  map_one' := by
    apply MulOpposite.unop_injective
    ext f x
    change f (σ 1 x) = f x
    rw [map_one, Module.End.one_apply]
  map_zero' := by
    apply MulOpposite.unop_injective
    ext f x
    change f (σ 0 x) = 0
    rw [map_zero, LinearMap.zero_apply, map_zero]
  map_add' a b := by
    apply MulOpposite.unop_injective
    ext f x
    change f (σ (a + b) x) = f (σ a x) + f (σ b x)
    rw [map_add, LinearMap.add_apply, map_add]
  map_mul' a b := by
    apply MulOpposite.unop_injective
    ext f x
    change f (σ (a * b) x) = f (σ a (σ b x))
    rw [map_mul, Module.End.mul_apply]

/-- Every element of the retained integral homology ring preserves the original
integral dual. No selection of an auxiliary stable lattice occurs.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§1.2–1.3. -/
theorem integralOrderPullback_preserves {O : Type*} [Ring O]
    {Λ : Type} [AddCommGroup Λ] (σ : O →+* Module.End ℤ Λ)
    (a : O) (f : b2b_dual Λ) (hf : f ∈ integralDual Λ) :
    (integralOrderPullback σ a).unop f ∈ integralDual Λ := by
  intro x
  exact hf (σ a x)

#print axioms integralOrderPullback
#print axioms integralOrderPullback_preserves
end HodgeLean.Foundations.Program.GeneralTypeIII
