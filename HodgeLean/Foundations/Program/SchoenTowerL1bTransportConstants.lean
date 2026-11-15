import Mathlib.Basic.Complex.Basic
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerSections

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A generic map over the complex base respects the actual constant embeddings. -/
theorem s2v_l1b_generic_constants
    (B W : Over (Spec (CommRingCat.of ℂ)))
    [IsIntegral B.left] [IsIntegral W.left]
    [Nonempty (⊤ : B.left.Opens)] [Nonempty (⊤ : W.left.Opens)]
    (κ : B.left.functionField ⟶ W.left.functionField)
    (h : (Spec.map κ ≫ B.left.fromSpecStalk (genericPoint B.left)) ≫ B.hom =
      W.left.fromSpecStalk (genericPoint W.left) ≫ W.hom) :
    ((Scheme.ΓSpecIso ↧ℂ).inv ≫ B.hom.appTop ≫ B.left.germToFunctionField ⊤) ≫ κ =
      (Scheme.ΓSpecIso ↧ℂ).inv ≫ W.hom.appTop ≫ W.left.germToFunctionField ⊤ := by
  rw [← s2v_l1b_generic_section_germ B.left ⊤ (by simp),
    ← s2v_l1b_generic_section_germ W.left ⊤ (by simp)]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_naturality]
  change (Scheme.ΓSpecIso ↧ℂ).inv ≫ B.hom.appTop ≫
      (B.left.fromSpecStalk (genericPoint B.left)).appTop ≫
      (Spec.map κ).appTop ≫ (Scheme.ΓSpecIso W.left.functionField).hom = _
  have he := congrArg (fun f : Spec W.left.functionField ⟶ Spec ↧ℂ => f.appTop) h
  simp only [Scheme.Hom.comp_appTop] at he
  simpa [Category.assoc, Scheme.Hom.appLE] using
    congrArg (fun f => (Scheme.ΓSpecIso ↧ℂ).inv ≫ f ≫
      (Scheme.ΓSpecIso W.left.functionField).hom) he

end HodgeLean.Foundations.Program
