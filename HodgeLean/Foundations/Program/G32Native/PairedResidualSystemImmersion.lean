import HodgeLean.Foundations.Program.G32Native.PairedResidualProjectiveDualKernel
import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemFinite
import HodgeLean.Foundations.Program.SchoenCycleU1SchemeStationaryKernel
import HodgeLean.Foundations.Program.SchoenCycleU1SchemeDualCriterion
import HodgeLean.Foundations.Program.SchoenCycleU1Immersion

/-! # Actual scheme immersion of the full normalized differential system -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped BigOperators ContDiff Manifold
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

/-- The actual full-system morphism separates arbitrary dual-number scheme maps. -/
theorem residual_system_first_order_separation :
    Function.Injective (fun f : s2e_u1_specOver (DualNumber ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)) => f ≫ ℓ) := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  dsimp only at hℓ
  have hp : Function.Injective (Point.map ℓ) := by
    rw [hℓ]
    exact (residual_system_quotient_injective Z B k r y hy W hW hgenus γ hγ hsurj hquot).comp
      (s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd).symm.injective
  exact s2e_u1_scheme_dual_injective_of_stationary_kernel _ B ℓ hp
    (fun f hf => residual_system_projective_dual_kernel Z B k r d y hy W hW
      hgenus hd γ hγ hsurj hquot ℓ hℓ f hf)

#print axioms residual_system_first_order_separation
/-- The full normalized differential system embeds as an actual scheme subscheme. -/
theorem residual_system_closedImmersion : IsClosedImmersion ℓ.left := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  dsimp only at hℓ
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ))
  letI : IsProjective PP.hom := ⟨⟨⟨d, 𝟙 _, Category.id_comp _⟩⟩⟩
  letI : IsFinite ℓ.left := residual_system_morphism_finite Z B k r y hy W hW
    hgenus γ hγ hsurj hquot d hd ℓ hℓ
  have hsep := residual_system_first_order_separation Z B k r d y hy W hW
    hgenus hd γ hγ hsurj hquot ℓ hℓ
  letI : FormallyUnramified ℓ.left :=
    s2e_u1_formallyUnramified_of_dual_separation PP B ℓ hsep
  have hp : Function.Injective (Point.map ℓ) := by
    rw [hℓ]
    exact (residual_system_quotient_injective Z B k r y hy W hW hgenus γ hγ hsurj hquot).comp
      (s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd).symm.injective
  exact s2e_u1_finite_unramified_point_separation_immersion PP B ℓ hp

#print axioms residual_system_closedImmersion
end HodgeLean.Foundations.Program.G32Native
