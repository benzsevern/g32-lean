import HodgeLean.Foundations.Program.G32Native.PairedResidualConstantMap
import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelEvaluation

/-! # Scheme-level constancy of the full-system Abel composite -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r d : ℕ)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm (Module.finrank_fin_fun (n := 1) ℂ) q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    [FiniteDimensional ℂ W]
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ W = d + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : let : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
      let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd
      Point.map ℓ = fun R => residualProjectiveSystemPoint
        (Module.finrank_fin_fun (n := 1) ℂ) y hy W hW hgenus γ id (ep.symm R))
include hy hW hgenus hd hγ hℓ
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)

/-- The actual full-system Abel composite is the constant scheme morphism at its specified value. -/
theorem residual_system_abel_composite_constant
    (p : ComplexPoint Z) (a : B ⟶ model (C := ComplexPoint Z) hOne)
    (ha : Point.map (γ ≫ a) = fun u => theta (C := ComplexPoint Z) hOne
      (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z (2 * k) i) u)))
    (q₀ : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)))) :
    ℓ ≫ a = residualConstantMap (Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)))
      (model (C := ComplexPoint Z) hOne) (Point.map (ℓ ≫ a) q₀) := by
  dsimp only at hℓ
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ))
  letI : IsIntegral PP.left := HodgeLean.Adapters.IntersectionProductScaf_projective_integral d
  letI : IsProjective PP.hom := ⟨⟨⟨d, 𝟙 _, Category.id_comp _⟩⟩⟩
  apply residual_eq_constantMap PP (model (C := ComplexPoint Z) hOne) (ℓ ≫ a)
  intro q
  let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd
  have hval := residual_system_abel_value_constant Z B k r y hy W hW hgenus p γ hγ a ha
    (ep.symm q) (ep.symm q₀)
  have he (x : ComplexPoint PP) : Point.map (ℓ ≫ a) x =
      Point.map a (residualProjectiveSystemPoint hOne y hy W hW hgenus γ id (ep.symm x)) :=
    (Point.map_comp_apply ℓ a x).trans
      (congrArg (fun b : ComplexPoint B => Point.map a b) (congrFun hℓ x))
  exact (he q).trans (hval.trans (he q₀).symm)

#print axioms residual_system_abel_composite_constant
end HodgeLean.Foundations.Program.G32Native
