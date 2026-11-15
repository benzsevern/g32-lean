import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelConstantComposite
import HodgeLean.Foundations.Program.G32Native.PairedResidualFibreFactor
import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemImmersion

/-! # The actual full-system immersion into its specified Abel fibre -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
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
include hy hW hgenus hd hγ hsurj hquot hℓ
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)

/-- The specified full projective system embeds into its actual scheme-theoretic Abel fibre. -/
theorem residual_system_abel_fibre_immersion
    (p : ComplexPoint Z) (a : B ⟶ model (C := ComplexPoint Z) hOne)
    (ha : Point.map (γ ≫ a) = fun u => theta (C := ComplexPoint Z) hOne
      (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z (2 * k) i) u)))
    (q₀ : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)))) :
    ∃ l : (Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ))).left ⟶
        pullback a.left (Point.map (ℓ ≫ a) q₀).left,
      IsClosedImmersion l ∧
      l ≫ pullback.fst a.left (Point.map (ℓ ≫ a) q₀).left = ℓ.left ∧
      l ≫ pullback.snd a.left (Point.map (ℓ ≫ a) q₀).left =
        ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ) := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ))
  let J := model (C := ComplexPoint Z) hOne
  let z : ComplexPoint J := Point.map (ℓ ≫ a) q₀
  letI : IsClosedImmersion ℓ.left := residual_system_closedImmersion Z B k r d y hy W hW
    hgenus hd γ hγ hsurj hquot ℓ hℓ
  haveI : IsClosedImmersion (z.left ≫ J.hom) := by
    rw [Over.w z]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion z.left := IsClosedImmersion.of_comp z.left J.hom
  exact residual_closedImmersion_into_specified_fibre PP B J ℓ a z
    (residual_system_abel_composite_constant Z B k r d y hy W hW hgenus hd γ hγ ℓ hℓ p a ha q₀)

#print axioms residual_system_abel_fibre_immersion
end HodgeLean.Foundations.Program.G32Native
