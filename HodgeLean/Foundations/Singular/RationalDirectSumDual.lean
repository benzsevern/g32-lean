import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Field.Rat

/-! Canonical duality of actual rational direct sums and products. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped DirectSum
namespace HodgeLean.Foundations.Singular

/-- Restriction to the summands identifies the rational dual of a direct sum with the product of duals.
Source: Hatcher, Algebraic Topology, §3.1, functionals on direct sums. -/
def rationalDirectSumDualEquiv {ι : Type} [DecidableEq ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)] :
    Module.Dual ℚ (⨁ i, V i) ≃ₗ[ℚ] ∀ i, Module.Dual ℚ (V i) where
  toFun φ i := φ.comp (DirectSum.lof ℚ ι V i)
  invFun ψ := DirectSum.toModule ℚ ι ℚ ψ
  left_inv φ := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro z
    exact DirectSum.toModule_lof (φ := fun j => φ.comp (DirectSum.lof ℚ ι V j)) ℚ i z
  right_inv ψ := by
    funext i
    apply LinearMap.ext
    intro z
    exact DirectSum.toModule_lof (φ := ψ) ℚ i z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Over a finite index set the actual rational dual of a direct sum is the direct sum of the duals.
Source: Hatcher, Algebraic Topology, §3.1, finite direct sums and their duals. -/
def rationalFiniteDirectSumDualEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)] :
    Module.Dual ℚ (⨁ i, V i) ≃ₗ[ℚ] ⨁ i, Module.Dual ℚ (V i) :=
  (rationalDirectSumDualEquiv V).trans
    (DirectSum.linearEquivFunOnFintype ℚ ι (fun i => Module.Dual ℚ (V i))).symm

/-- The inverse finite direct-sum duality map evaluates each summand by its actual component functional.
Source: Hatcher, Algebraic Topology, §3.1, finite direct sums and their duals. -/
theorem rationalFiniteDirectSumDualEquiv_symm_lof
    {ι : Type} [Fintype ι] [DecidableEq ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    (φ : ⨁ i, Module.Dual ℚ (V i)) (i : ι) (z : V i) :
    (rationalFiniteDirectSumDualEquiv V).symm φ (DirectSum.lof ℚ ι V i z) = φ i z := by
  change DirectSum.toModule ℚ ι ℚ (fun j => φ j) (DirectSum.lof ℚ ι V i z) = φ i z
  exact DirectSum.toModule_lof (φ := fun j => φ j) ℚ i z

#print axioms rationalFiniteDirectSumDualEquiv_symm_lof
#print axioms rationalFiniteDirectSumDualEquiv
#print axioms rationalDirectSumDualEquiv
end HodgeLean.Foundations.Singular
