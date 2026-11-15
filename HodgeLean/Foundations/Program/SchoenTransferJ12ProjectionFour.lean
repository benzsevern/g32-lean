import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionCross
import HodgeLean.Foundations.Program.SchoenTransferJ12FibreTraceFour

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Singular AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupComparison cohomologyMap cupProductOf
  s4_selected_projection rationalProductCohomologyEquiv

/-- In total degree four, projection along a curve keeps only fibre degree two. -/
theorem s4_selected_projection_four_off_degree
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (q : Fin 5) (hq : q.val ≠ 2)
    (b : HQ Y q.val) (a : HQ A (4 - q.val)) :
    s4_selected_projection A Y 1 2 I
      ((cupProductOf (A ⊗ Y)).cup (by have := q.isLt; omega)
        (homPullback (snd A Y) q.val b) (homPullback (fst A Y) (4 - q.val) a)) = 0 := by
  have hfibre (p : ℕ) : Module.Finite ℚ
      (Cohomology ℚ (TopCat.of (ComplexPoint Y)) p) := by
    letI := (finbetti_finiteBetti Y).finite p
    exact Module.Finite.equiv (cupComparison Y p)
  let h := complexPointProdHomeomorph A Y
  let g : TopCat.of (ComplexPoint A × ComplexPoint Y) ⟶
      TopCat.of (ComplexPoint (A ⊗ Y)) := TopCat.ofHom ⟨h.symm, h.symm.continuous⟩
  have hgA : g ≫ TopCat.ofHom (Point.continuousMap (fst A Y)) =
      productFirst (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint Y)) := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrArg Prod.fst (h.apply_symm_apply z)
  have hgY : g ≫ TopCat.ofHom (Point.continuousMap (snd A Y)) =
      productSecond (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint Y)) := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrArg Prod.snd (h.apply_symm_apply z)
  have hpA : cohomologyMap ℚ (4 - q.val) g
      (cupComparison (A ⊗ Y) (4 - q.val) (homPullback (fst A Y) (4 - q.val) a)) =
      cohomologyMap ℚ (4 - q.val)
        (productFirst (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint Y)))
        (cupComparison A (4 - q.val) a) := by
    simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hgA]
  have hpY : cohomologyMap ℚ q.val g
      (cupComparison (A ⊗ Y) q.val (homPullback (snd A Y) q.val b)) =
      cohomologyMap ℚ q.val
        (productSecond (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint Y)))
        (cupComparison Y q.val b) := by
    simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hgY]
  apply (cupComparison A 2).injective
  rw [map_zero, s4_selected_projection_comparison A Y 1 2 I hfibre, cupComparison_cup,
    cq_cohomologyHomeomorphEquiv_apply]
  change s4_selected_fibre_trace (TopCat.of (ComplexPoint A))
    (TopCat.of (ComplexPoint Y)) hfibre 2 2
    ((cupComparison Y 2).symm.trans I) (cohomologyMap ℚ 4 g _) = 0
  rw [cohomologyMap_cup, hpY, hpA]
  exact s4_selected_fibre_trace_four_off_degree _ _ hfibre _ q hq _ _

#print axioms s4_selected_projection_four_off_degree
end HodgeLean.Foundations.Program
