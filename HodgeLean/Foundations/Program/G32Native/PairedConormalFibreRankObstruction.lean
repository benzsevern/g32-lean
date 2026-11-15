import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Fibre rank obstruction to a zero relation after pullback -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A relation cannot become zero when its pulled cokernel has a different fibre dimension from its target. -/
theorem conormal_relation_pullback_ne_zero_of_fibre_rank
    {K : Type} [Field K] {X : Scheme} (x : Spec (CommRingCat.of K) ⟶ X)
    {I A : X.Modules} (a : I ⟶ A)
    (h : Module.finrank K ((moduleSpecΓFunctor (R := CommRingCat.of K)).obj
        ((Scheme.Modules.pullback x).obj (cokernel a))) ≠
      Module.finrank K ((moduleSpecΓFunctor (R := CommRingCat.of K)).obj
        ((Scheme.Modules.pullback x).obj A))) :
    (Scheme.Modules.pullback x).map a ≠ 0 := by
  intro hz
  let F := Scheme.Modules.pullback x
  let G := moduleSpecΓFunctor (R := CommRingCat.of K)
  let e : F.obj (cokernel a) ≅ F.obj A :=
    PreservesCokernel.iso F a ≪≫ cokernelIsoOfEq hz ≪≫ cokernelZeroIsoTarget
  exact h (G.mapIso e).toLinearEquiv.finrank_eq

end HodgeLean.Foundations.Program.G32Native
