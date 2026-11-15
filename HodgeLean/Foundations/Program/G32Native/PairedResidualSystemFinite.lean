import HodgeLean.Foundations.Program.G32Native.PairedResidualQuotientInjectivity
import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemAlgebraic
import HodgeLean.Foundations.Program.SchoenCycleQuotientSeparation
import HodgeLean.Foundations.Program.SchoenCycleCanonicalGraphAlgebraic
import HodgeLean.Foundations.Program.SchoenCyclePairedProjective
import HodgeLean.Foundations.Program.SchoenCyclePairedEvaluation
import HodgeLean.Foundations.Program.SchoenCycleGenusTransport

/-! # Finiteness of the algebraic full-system parametrization -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Adapters HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
  [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] (k s : ℕ)
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)
variable
  (y : Fin (2 * s) → ComplexPoint Z) (hy : Function.Injective y)
  (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
  (hW : ∀ q : W, b4c_IsMeroForm hOne q.val ∧
    (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hOne q.val p) 0) ∧
    (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hOne q.val p) 0) ∧
    ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
  (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * s)
  (γ : g3_power Z (2 * k) ⟶ B) (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "F₀" => (residualProjectiveSystemPoint hOne y hy W hW hgenus γ id)
include hy hW hgenus hγ


variable [IsIntegral B.left] [Smooth B.hom] [IsFinite γ.left]
  (hsurj : Function.Surjective (Point.map γ))
  (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
    (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
include hsurj hquot

variable [IsProjective B.hom] [FiniteDimensional ℂ W]
  (l : ℕ) (hd : Module.finrank ℂ W = l + 1)
include hd

/-- The algebraic full-system parametrization is finite over the supplied quotient. -/
theorem residual_system_morphism_finite
    (f : Over.mk (ProjectiveSpace.toBase (Fin (l + 1)) (Spec ↧ℂ)) ⟶ B)
    (hf : Point.map f = fun R => F₀
      ((s2e_finiteDimensionalProjectivePointEquiv (V := W) l hd).symm R)) :
    IsFinite f.left := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (l + 1)) (Spec ↧ℂ))
  letI : IsProjective PP.hom := ⟨⟨⟨l, 𝟙 _, Category.id_comp _⟩⟩⟩
  haveI : IsProper (f.left ≫ B.hom) := by rw [Over.w f]; infer_instance
  haveI : IsProper f.left := IsProper.of_comp _ B.hom
  have hi : Function.Injective (Point.map f) := by
    rw [hf]
    exact (residual_system_quotient_injective Z B k s y hy W hW hgenus γ hγ hsurj hquot).comp
      (s2e_finiteDimensionalProjectivePointEquiv (V := W) l hd).symm.injective
  apply s2e_isFinite_of_proper_complexPoint_fibres f
  intro b
  exact (Set.finite_singleton b).preimage hi.injOn

#print axioms residual_system_morphism_finite
end HodgeLean.Foundations.Program.G32Native
