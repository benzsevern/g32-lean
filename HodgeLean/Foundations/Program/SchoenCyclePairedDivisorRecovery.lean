import HodgeLean.Foundations.Program.SchoenCycleQuotientDivisorRecovery

/-! # Adjusted divisors recovered from retained lifts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Manifold
open HodgeLean.Adapters
open scoped BigOperators ContDiff Classical
namespace HodgeLean.Foundations.Program

/-- A lift of the paired quotient value retains every adjusted divisor coefficient.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_paired_divisor_of_retained_lift
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom]
    (k r : ℕ)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (x : Fin r → ComplexPoint Z)
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hinv : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (v : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) (hv : v ≠ 0)
    (q : ComplexPoint (g3_power Z (2 * k)))
    (hq : let : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
      s2e_projectiveDifferentialQuotientPoint (Module.finrank_fin_fun (n := 1) ℂ)
        w x hres y hy horder hout hgenus γ id (Projectivization.mk ℂ v hv) = Point.map γ q) :
    s2e_adjustedDifferentialDivisor (Module.finrank_fin_fun (n := 1) ℂ) w y v =
      ∑ i, Finsupp.single (Point.map (g3_proj Z (2 * k) i) q) (1 : ℤ) := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  dsimp only at hq
  apply s2e_retained_quotient_lift_recovers_divisor Z B (2 * k) γ hsurj hinv hquot
    (s2e_adjustedDifferentialDivisor (Module.finrank_fin_fun (n := 1) ℂ) w y v)
    (s2e_adjustedDifferentialDivisor_effective _ w x hres y hy horder hout v hv)
    (s2e_adjustedDifferentialDivisor_degree _ w x hres y hgenus v hv) q
  have hvD : s2e_projectiveDifferentialDivisor (Module.finrank_fin_fun (n := 1) ℂ)
      w y (Projectivization.mk ℂ v hv) =
      s2e_adjustedDifferentialDivisor (Module.finrank_fin_fun (n := 1) ℂ) w y v := rfl
  simpa only [s2e_projectiveDifferentialQuotientPoint, Sym.map_id,
    s2e_projectiveDifferentialSymmetricPower, hvD] using hq

#print axioms s2e_paired_divisor_of_retained_lift
end HodgeLean.Foundations.Program
