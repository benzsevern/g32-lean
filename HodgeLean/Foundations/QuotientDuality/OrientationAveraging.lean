import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Rational averaging for inverse actions and equivariant maps. -/

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

def inverseActionAverage (a : G → Module.End ℚ V) : Module.End ℚ V :=
  (Fintype.card G : ℚ)⁻¹ • ∑ g : G, a g

lemma inverseActionAverage_fixed (a : G → Module.End ℚ V)
    (hmul : ∀ g h x, a g (a h x) = a (h * g) x) (x : V) (g : G) :
    a g (inverseActionAverage a x) = inverseActionAverage a x := by
  classical
  simp only [inverseActionAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => hmul g h x)

lemma inverseActionAverage_preserves_map (a : G → Module.End ℚ V) (f : V →ₗ[ℚ] W)
    (hf : ∀ g x, f (a g x) = f x) (x : V) :
    f (inverseActionAverage a x) = f x := by
  classical
  have hcard : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [inverseActionAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, hf, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end HodgeLean.Foundations.QuotientDuality
