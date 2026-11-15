import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionCross
import HodgeLean.Foundations.Program.SchoenTransferJ12FibreTraceOffDegree

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

/-- Projection discards an external cup outside its specified top fibre degree.
Source: the actual finite-fibre Künneth contraction under the cycle-class comparison. -/
theorem s4_selected_projection_off_degree
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d n q r : ℕ) (htotal : q + r = 2 * d + n)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (hq : q ≠ 2 * d)
    (b : HQ Y q) (a : HQ A r) :
    s4_selected_projection A Y d n I
      ((cupProductOf (A ⊗ Y)).cup htotal
        (homPullback (snd A Y) q b) (homPullback (fst A Y) r a)) = 0 := by
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
  have hpA : cohomologyMap ℚ r g
      (cupComparison (A ⊗ Y) r (homPullback (fst A Y) r a)) =
      cohomologyMap ℚ r
        (productFirst (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint Y)))
        (cupComparison A r a) := by
    simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hgA]
  have hpY : cohomologyMap ℚ q g
      (cupComparison (A ⊗ Y) q (homPullback (snd A Y) q b)) =
      cohomologyMap ℚ q
        (productSecond (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint Y)))
        (cupComparison Y q b) := by
    simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hgY]
  apply (cupComparison A n).injective
  rw [map_zero, s4_selected_projection_comparison A Y d n I hfibre, cupComparison_cup,
    cq_cohomologyHomeomorphEquiv_apply]
  change s4_selected_fibre_trace (TopCat.of (ComplexPoint A))
    (TopCat.of (ComplexPoint Y)) hfibre (2 * d) n
    ((cupComparison Y (2 * d)).symm.trans I) (cohomologyMap ℚ (2 * d + n) g _) = 0
  rw [cohomologyMap_cup, hpY, hpA]
  exact s4_selected_fibre_trace_off_degree _ _ hfibre (2 * d) n q r htotal hq _ _ _

#print axioms s4_selected_projection_off_degree
end HodgeLean.Foundations.Program
