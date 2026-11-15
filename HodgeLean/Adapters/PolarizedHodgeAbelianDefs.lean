import HodgeLean.RealDefs.F1569
import HodgeLean.Adapters.CupLeftFiltrationAbelian

/-! # Polarized weight-one Hodge structures on abelian varieties (FROZEN DEFINITIONS) -/

noncomputable section

namespace HodgeLean.Adapters

open HodgeLean.Foundations
open scoped TensorProduct

/-- Complexify a real endomorphism of the real scalar extension of a rational vector space,
and identify the iterated scalar extension with the direct complex scalar extension.
Source: Bourbaki, *Algebra*, Ch. II, §3 (associativity of extension of scalars). -/
def complexifyRealEnd {V : Type*} [AddCommGroup V] [Module ℚ V]
    (I : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V) : Module.End ℂ (ℂ ⊗[ℚ] V) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V).toLinearMap ∘ₗ
    I.baseChange ℂ ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V).symm.toLinearMap

example {V : Type*} [AddCommGroup V] [Module ℚ V] :
    complexifyRealEnd (LinearMap.id : Module.End ℝ (ℝ ⊗[ℚ] V)) = LinearMap.id := by
  simp [complexifyRealEnd]

/-- The standard alternating form on the rational plane.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Ch. 1. -/
def pol1StandardSymplectic : LinearMap.BilinForm ℚ (Fin 2 → ℚ) :=
  LinearMap.mk₂ ℚ (fun x y => x 0 * y 1 - x 1 * y 0)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)

example (x y : Fin 2 → ℚ) :
    pol1StandardSymplectic x y = x 0 * y 1 - x 1 * y 0 := rfl

/-- The first coordinate line in the rational plane.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Ch. 1. -/
def pol1IsotropicLine : Submodule ℚ (Fin 2 → ℚ) :=
  Submodule.span ℚ {![1, 0]}

example : ![1, 0] ∈ pol1IsotropicLine := Submodule.subset_span (by simp)

end HodgeLean.Adapters
