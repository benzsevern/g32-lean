import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Defs
import HodgeLean.Foundations.Program.SchoenSelectedGeometryAbelJacobiBijective
import HodgeLean.Foundations.Program.SchoenSelectedGeometryBettiSquare

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Curves.AbelAdapter
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

/-- The actual algebraic Abel map identifies rational degree-one cohomology. -/
theorem s4_selected_abel_pullback_bijective
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [ChartedSpace E (ComplexPoint X)] [IsManifold 𝓘(ℂ, E) ω (ComplexPoint X)]
    [ConnectedSpace (ComplexPoint X)] (h : Module.finrank ℂ E = 1)
    (p : ComplexPoint X) (j : X ⟶ model h)
    (hj : ∀ x, Point.map j x = modelAbel h p x) :
    Function.Bijective (homPullback j 1) := by
  letI := b3_periodLattice_finite (C := ComplexPoint X) h
  letI := b3_periodLattice_free (E := E) (C := ComplexPoint X)
  letI := b2_latticeMap_discrete (b3_periodF E (ComplexPoint X)) (b3_isWeightOne h)
  have ha := b3_abelJacobi_holomorphic h p (analyticAbel h p)
    (b3_exists_abelJacobi h p).choose_spec
  have hb := s0_abelJacobi_rational_pullback_bijective h p (analyticAbel h p)
    (b3_exists_abelJacobi h p).choose_spec ha.continuous
  have hs : Function.Bijective (AlgebraicTopology.Singular.cohomologyMap ℚ 1
      (TopCat.ofHom (Point.continuousMap j))) := by
    apply s0_pullback_bijective_of_homeomorph_square
      (Homeomorph.refl (ComplexPoint X)) (theta h)
      (TopCat.ofHom ⟨analyticAbel h p, ha.continuous⟩)
      (TopCat.ofHom (Point.continuousMap j)) 1 _ hb
    ext x : 1
    exact hj x
  exact (cupComparison X 1).symm.bijective.comp
    (hs.comp (cupComparison (model h) 1).bijective)

/-- The retained period model has an actual algebraic Abel map with bijective rational H1 pullback. -/
theorem s4_selected_algebraic_abel_exists
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 1) (p : ComplexPoint X) :
    letI := connectedSpace_complexPoint X
    let h : Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1 := by
      simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
        smul_eq_mul, mul_one] using hdim
    ∃ j : X ⟶ model h,
      (∀ x, Point.map j x = modelAbel h p x) ∧ Function.Bijective (homPullback j 1) := by
  letI := connectedSpace_complexPoint X
  have h : Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1 := by
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      smul_eq_mul, mul_one] using hdim
  obtain ⟨j, hj, _⟩ := algebraicAbel X hdim p
  exact ⟨j, hj, s4_selected_abel_pullback_bijective X h p j hj⟩

#print axioms s4_selected_algebraic_abel_exists

#print axioms s4_selected_abel_pullback_bijective

end HodgeLean.Foundations.Program
