import HodgeLean.Foundations.Program.SchoenSelectedGeometryAlgebraicSquare

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- A compatible point action commutes with algebraic quotient pullback. -/
theorem s0_algebraic_quotient_action
    {C : Type} [TopologicalSpace C]
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (e : ContinuousMap C (ComplexPoint X)) (s : ContinuousMap C C)
    (q : X ⟶ Y) (a : Y ⟶ Y)
    (ha : ∀ z, Point.map a (Point.map q (e z)) = Point.map q (e (s z)))
    (n : ℕ) (x : HQ Y n) :
    cohomologyMap ℚ n (TopCat.ofHom e)
      (cupComparison X n (homPullback q n (homPullback a n x))) =
    cohomologyMap ℚ n (TopCat.ofHom s)
      (cohomologyMap ℚ n (TopCat.ofHom e)
        (cupComparison X n (homPullback q n x))) := by
  have hm : TopCat.ofHom e ≫ TopCat.ofHom (Point.continuousMap q) ≫
      TopCat.ofHom (Point.continuousMap a) =
      TopCat.ofHom s ≫ TopCat.ofHom e ≫ TopCat.ofHom (Point.continuousMap q) := by
    ext z : 1
    exact ha z
  have ht := congrArg (fun f ↦ cohomologyMap ℚ n f) hm
  simp only [cohomologyMap_comp] at ht
  have hx := LinearMap.congr_fun ht (cupComparison Y n x)
  simp only [LinearMap.comp_apply] at hx
  simpa only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using hx

#print axioms s0_algebraic_quotient_action
end HodgeLean.Foundations.Program
