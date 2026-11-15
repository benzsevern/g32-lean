import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.Fintype.Perm

open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- When all noninjective coordinate assignments vanish, a multilinear sum runs over permutations. -/
theorem multilinear_coordinate_expansion {K M N I : Type*} [CommSemiring K]
    [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [Fintype I] [DecidableEq I]
    (B : MultilinearMap K (fun _ : I => M) N) (v : I → I → M)
    (hz : ∀ r : I → I, ¬ Function.Injective r → B (fun i => v i (r i)) = 0) :
    B (fun i => ∑ j, v i j) =
      ∑ σ : Equiv.Perm I, B (fun i => v i (σ i)) := by
  classical
  rw [B.map_sum]
  symm
  apply Fintype.sum_of_injective (fun σ : Equiv.Perm I => (σ : I → I))
    (fun σ τ h => Equiv.ext (congrFun h))
  · intro r hr
    apply hz r
    intro hinj
    exact hr ⟨Equiv.ofBijective r ((Finite.injective_iff_bijective).mp hinj), rfl⟩
  · intro σ
    rfl

end HodgeLean.Foundations.Program
