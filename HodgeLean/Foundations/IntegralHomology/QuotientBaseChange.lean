import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Scalar extension through submodules annihilated by a base change map.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace HodgeLean.Foundations.IntegralHomology

lemma quotient_baseChange_equiv {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (f : M →ₗ[R] N) (hf : IsBaseChange S f)
    (p : Submodule R M) (hp : p ≤ LinearMap.ker f) :
    ∃ e : (S ⊗[R] (M ⧸ p)) ≃ₗ[S] N,
      ∀ m, e (1 ⊗ₜ[R] (Submodule.Quotient.mk m : M ⧸ p)) = f m := by
  let q := p.mkQ.baseChange S
  let g := (p.liftQ f hp).liftBaseChange S
  have h : g.comp q = hf.equiv.toLinearMap := by
    ext m
    change (1 : S) • f m = hf.equiv (1 ⊗ₜ[R] m)
    rw [IsBaseChange.equiv_tmul]
  have hi : Function.Injective q := by
    intro x y hxy
    apply hf.equiv.injective
    change hf.equiv.toLinearMap x = hf.equiv.toLinearMap y
    rw [← h]
    exact congrArg g hxy
  let eQ := LinearEquiv.ofBijective q
    ⟨hi, LinearMap.baseChange_surjective S p.mkQ_surjective⟩
  refine ⟨eQ.symm.trans hf.equiv, ?_⟩
  intro m
  have hq : eQ (1 ⊗ₜ[R] m) = 1 ⊗ₜ[R] (Submodule.Quotient.mk m : M ⧸ p) :=
    LinearMap.baseChange_tmul _ _ _
  rw [LinearEquiv.trans_apply, ← hq, LinearEquiv.symm_apply_apply,
    IsBaseChange.equiv_tmul, one_smul]

end HodgeLean.Foundations.IntegralHomology
