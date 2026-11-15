import HodgeLean.Foundations.Program.G32Native.PairedResidualQuotientInjectivity
import HodgeLean.Foundations.Program.SchoenCycleQuotientDivisorRecovery
import HodgeLean.Foundations.Program.SchoenCycleQuotientSeparation
import HodgeLean.Foundations.Program.SchoenCycleCanonicalGraphAlgebraic
import HodgeLean.Foundations.Program.SchoenCyclePairedProjective
import HodgeLean.Foundations.Program.SchoenCyclePairedEvaluation
import HodgeLean.Foundations.Program.SchoenCycleGenusTransport

/-! # Full-system divisors recovered from retained lifts -/
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

/-- A retained lift recovers every full-system adjusted divisor coefficient. -/
theorem residual_system_divisor_of_retained_lift
    (v : W) (hv : v ≠ 0) (q : ComplexPoint (g3_power Z (2 * k)))
    (hq : F₀ (Projectivization.mk ℂ v hv) = Point.map γ q) :
    b4c_divForm (hE := hOne) v.val + s2e_markedPoleDivisor y =
      ∑ i, Finsupp.single (Point.map (g3_proj Z (2 * k) i) q) (1 : ℤ) := by
  apply s2e_retained_quotient_lift_recovers_divisor Z B (2 * k) γ hsurj hγ hquot
    (b4c_divForm (hE := hOne) v.val + s2e_markedPoleDivisor y)
    (residualProjectiveDivisor_effective hOne y hy W hW (Projectivization.mk ℂ v hv))
    (residualProjectiveDivisor_degree hOne y W
      (fun q => ⟨(hW q).1, (hW q).2.2⟩) hgenus (Projectivization.mk ℂ v hv)) q
  have hvD : residualProjectiveDivisor hOne y W (Projectivization.mk ℂ v hv) =
      b4c_divForm (hE := hOne) v.val + s2e_markedPoleDivisor y := rfl
  simpa only [residualProjectiveSystemPoint, Sym.map_id, hvD] using hq

#print axioms residual_system_divisor_of_retained_lift
end HodgeLean.Foundations.Program.G32Native
