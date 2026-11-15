import Mathlib.Data.Complex.Basic
import HodgeLean.Foundations.Program.SchoenTowerL1bDeckSections
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerSections

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The original generic action fixes the actual complex constants. -/
theorem s2v_l1b_deck_fixes_constants
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [Nonempty (⊤ : W.left.Opens)]
    (d : W ⟶ W) (φ : W.left.functionField →+* W.left.functionField)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      W.left.fromSpecStalk (genericPoint W.left) =
      W.left.fromSpecStalk (genericPoint W.left) ≫ d.left)
    (c : ℂ) :
    let κ := ((Scheme.ΓSpecIso ↧ℂ).inv ≫ W.hom.appTop ≫
      W.left.germToFunctionField ⊤).hom
    φ (κ c) = κ c := by
  have hinv : Spec.map (CommRingCat.ofHom φ) ≫
      (W.left.fromSpecStalk (genericPoint W.left) ≫ W.hom) =
      W.left.fromSpecStalk (genericPoint W.left) ≫ W.hom := by
    rw [← Category.assoc, hφ, Category.assoc, Over.w d]
  have he := s2v_l1b_invariant_field_point_sections (Spec ↧ℂ)
    (W.left.fromSpecStalk (genericPoint W.left) ≫ W.hom) φ hinv ⊤
    (by simp) ((Scheme.ΓSpecIso ↧ℂ).inv c)
  have hgerm : (W.left.fromSpecStalk (genericPoint W.left)).appTop ≫
      (Scheme.ΓSpecIso W.left.functionField).hom = W.left.germToFunctionField ⊤ :=
    s2v_l1b_generic_section_germ W.left ⊤ (by simp)
  dsimp only
  rw [← hgerm]
  exact he

end HodgeLean.Foundations.Program
