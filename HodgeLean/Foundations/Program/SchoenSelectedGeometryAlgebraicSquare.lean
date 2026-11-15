import HodgeLean.Adapters.AbelianHomPullbackDefs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- A square of point maps transports algebraic pullback to singular cohomology. -/
theorem s0_algebraic_pullback_square
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    {C T : Type} [TopologicalSpace C] [TopologicalSpace T]
    (e : ContinuousMap C (ComplexPoint X)) (θ : ContinuousMap T (ComplexPoint Y))
    (aj : ContinuousMap C T) (j : X ⟶ Y)
    (hs : ∀ z, Point.map j (e z) = θ (aj z)) (n : ℕ) (x : HQ Y n) :
    cohomologyMap ℚ n (TopCat.ofHom e) (cupComparison X n (homPullback j n x)) =
      cohomologyMap ℚ n (TopCat.ofHom aj)
        (cohomologyMap ℚ n (TopCat.ofHom θ) (cupComparison Y n x)) := by
  have hm : TopCat.ofHom e ≫ TopCat.ofHom (Point.continuousMap j) =
      TopCat.ofHom aj ≫ TopCat.ofHom θ := by
    ext z : 1
    exact hs z
  simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hm, cohomologyMap_comp,
    LinearMap.comp_apply]

#print axioms s0_algebraic_pullback_square
end HodgeLean.Foundations.Program
