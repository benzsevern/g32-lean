import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemInjectivity
import HodgeLean.Foundations.Program.SchoenCycleQuotientSeparation
import HodgeLean.Foundations.Program.SchoenCycleCanonicalGraphAlgebraic
import HodgeLean.Foundations.Program.SchoenCyclePairedProjective
import HodgeLean.Foundations.Program.SchoenCyclePairedEvaluation
import HodgeLean.Foundations.Program.SchoenCycleGenusTransport

/-! # Separation of full-system projective parameters -/
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

/-- Full-system quotient evaluation distinguishes all normalized projective parameters. -/
theorem residual_system_quotient_injective : Function.Injective F₀ := by
  classical
  intro u v h
  apply residualProjectiveDivisor_injective hOne y W
    (fun q => ⟨(hW q).1, (hW q).2.2⟩)
  dsimp only [residualProjectiveSystemPoint] at h
  have he := s2e_symmetricQuotientEvaluation_injective Z B (2 * k) γ hsurj hγ hquot h
  simp only [Sym.map_id] at he
  have hd := congrArg (fun s : Sym (ComplexPoint Z) (2 * k) =>
    (s : Multiset (ComplexPoint Z)).toFinsupp.mapRange (fun m : ℕ => (m : ℤ)) rfl) he
  simpa only [s2e_divisorSym_recover] using hd

#print axioms residual_system_quotient_injective
end HodgeLean.Foundations.Program.G32Native
