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
namespace HodgeLean.Foundations.Program

theorem s2e_paired_projective_dual_kernel
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    [FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = k + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : let : ConnectedSpace (ComplexPoint Z) :=
        AlgebraicGeometry.ComplexPoint.connectedSpace Z
      let ep := s2e_finiteDimensionalProjectivePointEquiv
        (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
      Point.map ℓ = fun R => s2e_projectiveDifferentialQuotientPoint
        (Module.finrank_fin_fun (n := 1) ℂ) w
        (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id
        (ep.symm R)) 
    (f : s2e_u1_specOver (DualNumber ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (hstationary : f ≫ ℓ = s2e_u1_constantDualPoint B
      (Point.map ℓ (Point.map f s2e_u1_dualResiduePoint))) :
    f = s2e_u1_constantDualPoint _ (Point.map f s2e_u1_dualResiduePoint) := by
  obtain ⟨i, φ, hrep⟩ := s2e_u1_projective_dual_point_chartCurve k f
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
  have hφ := s2e_paired_projectiveChart_kernel Z B k r hr y hy w hres horder hout hgenus hd
    γ hγ hsurj hquot ℓ hℓ i φ hs
  calc
    f = s2e_u1_polynomialDualParameter ≫ s2e_u1_projectiveChartCurve i φ := hrep.symm
    _ = s2e_u1_constantDualPoint _
        (Point.map (s2e_u1_projectiveChartCurve i φ) (s2e_u1_polynomialParameterPoint 0)) :=
      s2e_u1_projectiveChartCurve_dual_constant i φ hφ
    _ = s2e_u1_constantDualPoint _ (Point.map f s2e_u1_dualResiduePoint) := by rw [hb]

end HodgeLean.Foundations.Program
