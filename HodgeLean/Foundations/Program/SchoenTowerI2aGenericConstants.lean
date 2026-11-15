import HodgeLean.Foundations.Program.SchoenTowerL1bKummerSections
import HodgeLean.Foundations.Program.SchoenTowerI2aGenericCharts

/-! Scalar compatibility for the original-field point on an affine chart.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An original-field point over the complex base sends chart constants to the actual constant functions in the original field. -/
theorem s2v_i2a_original_field_chart_constants
    (B W : Over (Spec ↧ℂ)) [IsIntegral W.left]
    (η : Spec W.left.functionField ⟶ B.left)
    (hbase : η ≫ B.hom = W.left.fromSpecStalk (genericPoint W.left) ≫ W.hom)
    (V : B.left.Opens) (hηV : ⊤ ≤ η ⁻¹ᵁ V) (c : ℂ) :
    letI := overSpecAlgebra B V
    ((η.appLE V ⊤ hηV ≫ (Scheme.ΓSpecIso W.left.functionField).hom).hom)
      (algebraMap ℂ Γ(B.left, V) c) =
    ((Scheme.ΓSpecIso ↧ℂ).inv ≫ W.hom.appTop ≫ W.left.germToFunctionField ⊤).hom c := by
  letI := overSpecAlgebra B V
  have hcomp : B.hom.appLE ⊤ V le_top ≫ η.appLE V ⊤ hηV =
      (η ≫ B.hom).appTop := by
    rw [Scheme.Hom.appLE_comp_appLE]
    rfl
  change ((Scheme.ΓSpecIso ↧ℂ).inv ≫ B.hom.appLE ⊤ V le_top ≫
    η.appLE V ⊤ hηV ≫ (Scheme.ΓSpecIso W.left.functionField).hom).hom c = _
  rw [← Category.assoc (B.hom.appLE ⊤ V le_top), hcomp, hbase,
    Scheme.Hom.comp_appTop, Category.assoc]
  have H := s2v_l1b_generic_section_germ W.left ⊤ (by simp)
  change (W.left.fromSpecStalk (genericPoint W.left)).appTop ≫
    (Scheme.ΓSpecIso W.left.functionField).hom = W.left.germToFunctionField ⊤ at H
  rw [H]

end HodgeLean.Foundations.Program
