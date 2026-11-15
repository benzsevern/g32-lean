import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalTowerMono

/-! # Scalar extension of ambient kernel inclusion in a smooth tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

variable {K A B C : Type*} [CommRing K] [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower K A B] [IsScalarTower K A C] [IsScalarTower K B C]
    [IsScalarTower A B C]

/-- The original ambient ideal inclusion in a quotient tower.
Source: Hartshorne, Algebraic Geometry, II.8.12, ideal form. -/
def pairedC3TowerKernelInclusion :
    RingHom.ker (algebraMap A B) →ₗ[A] RingHom.ker (algebraMap A C) :=
  Submodule.inclusion (by
    intro t ht
    change algebraMap A C t = 0
    rw [IsScalarTower.algebraMap_apply A B C, RingHom.mem_ker.mp ht, map_zero])

/-- Tensoring the ambient kernel inclusion with the final quotient is
injective for a smooth intermediate quotient, through its conormal map.
Source: Hartshorne, Algebraic Geometry, II.8.12 and II.8.17. -/
theorem paired_c3_ideal_conormal_inclusion_injective
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]
    (hAB : Function.Surjective (algebraMap A B))
    (hAC : Function.Surjective (algebraMap A C)) :
    Function.Injective ((pairedC3TowerKernelInclusion (A := A) (B := B) (C := C)).baseChange C) := by
  let P := pairedC3QuotientPresentation (K := K) hAB
  let P' := pairedC3QuotientPresentation (K := K) hAC
  let f := pairedC3TowerExtensionMap (K := K) hAB hAC
  let a := (Algebra.Extension.Cotangent.map f).liftBaseChange C
  let m := (pairedC3TowerKernelInclusion (A := A) (B := B) (C := C)).baseChange C
  let e₁ : C ⊗[A] RingHom.ker (algebraMap A B) ≃ₗ[C] C ⊗[B] P.Cotangent :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C _).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) P.cotangentEquiv
  let e₂ : C ⊗[A] RingHom.ker (algebraMap A C) ≃ₗ[C] P'.Cotangent :=
    P'.cotangentEquiv
  have he (z) : e₂ (m z) = a (e₁ z) := by
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul r t =>
      change P'.cotangentEquiv
          (r ⊗ₜ[A] pairedC3TowerKernelInclusion (A := A) (B := B) (C := C) t) =
        a (r ⊗ₜ[B] P.cotangentEquiv (1 ⊗ₜ[A] t))
      have ht₁ : P'.cotangentEquiv
          (r ⊗ₜ[A] pairedC3TowerKernelInclusion (A := A) (B := B) (C := C) t) =
          r • Algebra.Extension.Cotangent.mk
            (P := P') (pairedC3TowerKernelInclusion (A := A) (B := B) (C := C) t) :=
        P'.cotangentEquiv_tmul r _
      have ht₂ : P.cotangentEquiv (1 ⊗ₜ[A] t) = Algebra.Extension.Cotangent.mk (P := P) t :=
        (P.cotangentEquiv_tmul (1 : B) t).trans (one_smul _ _)
      calc
        _ = _ := ht₁
        _ = a (r ⊗ₜ[B] Algebra.Extension.Cotangent.mk (P := P) t) := by
          change r • Algebra.Extension.Cotangent.mk
            (P := P') (pairedC3TowerKernelInclusion (A := A) (B := B) (C := C) t) =
            r • Algebra.Extension.Cotangent.map f (Algebra.Extension.Cotangent.mk (P := P) t)
          rw [Algebra.Extension.Cotangent.map_mk f]
          apply congrArg (fun u : P'.Cotangent => r • u)
          apply congrArg (Algebra.Extension.Cotangent.mk (P := P'))
          apply Subtype.ext
          rfl
        _ = _ := congrArg (fun u : P.Cotangent => a (r ⊗ₜ[B] u)) ht₂.symm
  have hi : Function.Injective a := paired_c3_tower_conormal_injective (K := K) hAB hAC
  intro z w hzw
  apply e₁.injective
  apply hi
  exact (he z).symm.trans ((congrArg e₂ hzw).trans (he w))

#print axioms pairedC3TowerKernelInclusion
#print axioms paired_c3_ideal_conormal_inclusion_injective
end HodgeLean.Foundations.Program.G32Native
