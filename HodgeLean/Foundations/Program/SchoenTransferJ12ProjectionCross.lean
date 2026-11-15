import HodgeLean.Foundations.Program.SchoenTransferJ12Projection
import HodgeLean.Foundations.Program.CompensationAssemblyProductSupport

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

/-- Integration evaluates a fibre-first external cup on the actual product.
Source: Hatcher, Algebraic Topology, §3.2, field-coefficient Künneth and naturality of cup. -/
theorem s4_selected_projection_fibre_cross
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d n : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (b : HQ Y (2 * d)) (a : HQ A n) :
    s4_selected_projection A Y d n I
      ((cupProductOf (A ⊗ Y)).cup rfl
        (homPullback (snd A Y) (2 * d) b) (homPullback (fst A Y) n a)) = I b • a := by
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
  have hpA : cohomologyMap ℚ n g
      (cupComparison (A ⊗ Y) n (homPullback (fst A Y) n a)) =
      cohomologyMap ℚ n
        (productFirst (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint Y)))
        (cupComparison A n a) := by
    simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hgA]
  have hpY : cohomologyMap ℚ (2 * d) g
      (cupComparison (A ⊗ Y) (2 * d) (homPullback (snd A Y) (2 * d) b)) =
      cohomologyMap ℚ (2 * d)
        (productSecond (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint Y)))
        (cupComparison Y (2 * d) b) := by
    simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hgY]
  apply (cupComparison A n).injective
  rw [s4_selected_projection_comparison A Y d n I hfibre, cupComparison_cup,
    cq_cohomologyHomeomorphEquiv_apply]
  change s4_selected_fibre_trace (TopCat.of (ComplexPoint A))
    (TopCat.of (ComplexPoint Y)) hfibre (2 * d) n
    ((cupComparison Y (2 * d)).symm.trans I)
    (cohomologyMap ℚ (2 * d + n) g _) = _
  rw [cohomologyMap_cup, hpY, hpA, s4_selected_fibre_trace_cross]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_smul]

#print axioms s4_selected_projection_fibre_cross
end HodgeLean.Foundations.Program
