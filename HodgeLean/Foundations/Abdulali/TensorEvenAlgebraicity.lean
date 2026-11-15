import HodgeLean.Foundations.Abdulali.AlgebraicEvenCup
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000
set_option Elab.async false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
attribute [local irreducible] cupProductOf algebraicCycleClassSpan
variable (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- Quadratic products land in the algebraic family in every tensor degree.
Source: Fulton, Intersection Theory, Corollary 19.2; odd products vanish. -/
theorem tensor_quadratic_products_even {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] (ℂ ⊗[ℚ] HQ Y 1)) (Q : Submodule ℂ (⨂[ℂ]^2 V))
    (hQ : ∀ t ∈ Q, complexCupEquiv Y 2 (exteriorPower.map 2 f
      (InvariantsExterior.wedgeQuotient 2 t)) ∈ (algebraicCycleClassSpan Y 1).baseChange ℂ)
    (n : ℕ) (t : ⨂[ℂ]^n V) (ht : t ∈ m1b_products Q n) :
    complexCupEquiv Y n (exteriorPower.map n f (InvariantsExterior.wedgeQuotient n t)) ∈
      f1575EvenCohomologySpan (algebraicCycleClassSpan Y) n := by
  rcases Nat.even_or_odd n with ⟨p, hp⟩ | hn
  · have he : n = 2*p := by omega
    clear hp
    subst n
    erw [f1575EvenCohomologySpan_even]
    exact tensor_quadratic_products_algebraic Y f Q hQ p t ht
  · rw [m1b_products_odd Q n hn, Submodule.mem_bot] at ht
    rw [ht, map_zero, map_zero, map_zero]
    exact Submodule.zero_mem _


end HodgeLean.Foundations.Abdulali
