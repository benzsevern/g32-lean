import HodgeLean.Foundations.Program.G32Native.PairedResidualProjectiveChartKernel
import HodgeLean.Foundations.Program.SchoenCycleS1bProjectiveChartKernel
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveDualChartCurve
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveConstantCurve
import HodgeLean.Foundations.Program.SchoenCycleU1DualResiduePoint

/-! # Stationary kernel for actual paired projective dual-number maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Adapters
open scoped Manifold
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The actual full-system stationary dual-number kernel consists of constant maps. -/
theorem residual_system_projective_dual_kernel
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
    (f : s2e_u1_specOver (DualNumber ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)))
    (hstationary : f ≫ ℓ = s2e_u1_constantDualPoint B
      (Point.map ℓ (Point.map f s2e_u1_dualResiduePoint))) :
    f = s2e_u1_constantDualPoint _ (Point.map f s2e_u1_dualResiduePoint) := by
  obtain ⟨i, φ, hrep⟩ := s2e_u1_projective_dual_point_chartCurve d f
  have hb : Point.map f s2e_u1_dualResiduePoint =
      Point.map (s2e_u1_projectiveChartCurve i φ) (s2e_u1_polynomialParameterPoint 0) := by
    rw [← hrep]
    change Point.map (s2e_u1_projectiveChartCurve i φ)
      (Point.map s2e_u1_polynomialDualParameter s2e_u1_dualResiduePoint) = _
    rw [s2e_u1_dualResiduePoint_polynomialParameter]
  have hs : s2e_u1_polynomialDualParameter ≫ (s2e_u1_projectiveChartCurve i φ ≫ ℓ) =
      s2e_u1_constantDualPoint B
        (Point.map (s2e_u1_projectiveChartCurve i φ ≫ ℓ) (s2e_u1_polynomialParameterPoint 0)) := by
    rw [← Category.assoc, hrep, hstationary, hb]
    rfl
  have hφ := residual_system_projectiveChart_kernel Z B k r d y hy W hW hgenus hd
    γ hγ hsurj hquot ℓ hℓ i φ hs
  calc
    f = s2e_u1_polynomialDualParameter ≫ s2e_u1_projectiveChartCurve i φ := hrep.symm
    _ = s2e_u1_constantDualPoint _
        (Point.map (s2e_u1_projectiveChartCurve i φ) (s2e_u1_polynomialParameterPoint 0)) :=
      s2e_u1_projectiveChartCurve_dual_constant i φ hφ
    _ = s2e_u1_constantDualPoint _ (Point.map f s2e_u1_dualResiduePoint) := by rw [hb]

#print axioms residual_system_projective_dual_kernel
end HodgeLean.Foundations.Program.G32Native
