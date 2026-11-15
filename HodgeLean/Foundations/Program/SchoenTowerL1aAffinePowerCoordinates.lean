import HodgeLean.Foundations.Program.SchoenTowerL1aParameterMorphism
import HodgeLean.Foundations.Program.SchoenTowerL1aOrderedEtale
import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction

/-! # Actual affine coordinates on retained ordered powers

Implication from the retained product universal property to its identification
with affine space when the factor is the affine line.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained ordered power of the affine line is actual affine space,
with its retained projections giving exactly the affine coordinates.
Source: Hartshorne, Algebraic Geometry, II.2, polynomial algebras and products. -/
theorem s2v_l1a_affine_line_power_coordinates (n : ℕ) :
    ∃ e : g3_power (Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)) n ≅
        Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ),
      ∀ j, e.hom.left.appTop (AffineSpace.coord (Spec ↧ℂ) j) =
        (g3_proj (Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)) n j).left.appTop
          (AffineSpace.coord (Spec ↧ℂ) (0 : Fin 1)) := by
  let L := Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)
  let A := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)
  let P := g3_power L n
  let z (j : Fin n) := (g3_proj L n j).left.appTop
    (AffineSpace.coord (Spec ↧ℂ) (0 : Fin 1))
  let f : P ⟶ A := (s2t_affineSpaceOverHomEquiv P (Fin n)).symm z
  have hf (j : Fin n) : f.left.appTop (AffineSpace.coord (Spec ↧ℂ) j) = z j :=
    s2t_affineSpaceOverHomEquiv_symm_coord P (Fin n) z j
  let a (j : Fin n) : A ⟶ L := (s2t_affineSpaceOverHomEquiv A (Fin 1)).symm
    (fun _ => AffineSpace.coord (Spec ↧ℂ) j)
  have ha (j : Fin n) : (a j).left.appTop
      (AffineSpace.coord (Spec ↧ℂ) (0 : Fin 1)) = AffineSpace.coord (Spec ↧ℂ) j :=
    s2t_affineSpaceOverHomEquiv_symm_coord A (Fin 1) _ 0
  let g : A ⟶ P := s2_lift n a
  have hg (j : Fin n) : g ≫ g3_proj L n j = a j := s2_check_lift_proj n a j
  have hfg : f ≫ g = 𝟙 P := by
    apply s2_product_hom_ext n
    intro j
    rw [Category.assoc, hg, Category.id_comp]
    apply (s2t_affineSpaceOverHomEquiv P (Fin 1)).injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (f ≫ a j).left.appTop (AffineSpace.coord (Spec ↧ℂ) (0 : Fin 1)) = z j
    rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ha, hf]
  have hgf : g ≫ f = 𝟙 A := by
    apply (s2t_affineSpaceOverHomEquiv A (Fin n)).injective
    funext j
    change (g ≫ f).left.appTop (AffineSpace.coord (Spec ↧ℂ) j) =
      (𝟙 A : A ⟶ A).left.appTop (AffineSpace.coord (Spec ↧ℂ) j)
    rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf]
    change g.left.appTop ((g3_proj L n j).left.appTop
      (AffineSpace.coord (Spec ↧ℂ) (0 : Fin 1))) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    change (g ≫ g3_proj L n j).left.appTop _ = _
    rw [hg, ha]
    rfl
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

end HodgeLean.Foundations.Program
