import HodgeLean.Foundations.Program.SchoenSelectedGeometryProducts

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open MonoidalCategory CartesianMonoidalCategory
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pairing complex points is holomorphic for the smooth product charts.
Source: `analyticAt_productChartComparison_symm`, the analytic inverse function theorem. -/
theorem s0_product_point_pairing_holomorphic
    (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom] :
    ContMDiff (𝓘(ℂ, Fin d → ℂ).prod 𝓘(ℂ, Fin e → ℂ))
      𝓘(ℂ, Fin (d + e) → ℂ) ω (complexPointProdHomeomorph X Y).symm := by
  rintro ⟨x, y⟩
  rw [contMDiffAt_iff]
  refine ⟨(complexPointProdHomeomorph X Y).symm.continuous.continuousAt, ?_⟩
  simp only [extChartAt_prod, ModelWithCorners.range_prod, modelWithCornersSelf_coe,
    Set.range_id, Set.univ_prod_univ, contDiffWithinAt_univ]
  have hfst : Point.map (fst X Y) (lift x y) = x := by simp [Point.map]
  have hsnd : Point.map (snd X Y) (lift x y) = y := by simp [Point.map]
  have h := (analyticAt_productChartComparison_symm X Y d e (lift x y)).contDiffAt (n := ω)
  change ContDiffAt ℂ ω
    (fun p ↦ localChart (X ⊗ Y) (d + e) (lift x y)
      (lift ((localChart X d x).symm p.1) ((localChart Y e y).symm p.2)))
    (localChart X d x x, localChart Y e y y)
  have he (p : ComplexPoint X × ComplexPoint Y) :
      (complexPointProdHomeomorph X Y).toOpenPartialHomeomorph.symm p = lift p.1 p.2 := rfl
  simpa only [productChartComparison, OpenPartialHomeomorph.coe_trans_symm,
    OpenPartialHomeomorph.symm_symm, Function.comp_def,
    OpenPartialHomeomorph.prod_symm_apply, he, hfst, hsnd] using h

#print axioms s0_product_point_pairing_holomorphic
end HodgeLean.Foundations.Program
