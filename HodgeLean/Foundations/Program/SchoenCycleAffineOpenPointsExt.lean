import HodgeLean.Foundations.Program.SchoenCycleAffineOpenSpecIso
import HodgeLean.Foundations.Program.SchoenCycleOpenTopSectionEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Original affine section evaluations determine an actual complex point in the original affine open.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_affine_open_points_ext
    (X : Over (Spec ↧ℂ)) (V : X.left.Opens) (hV : IsAffineOpen V)
    (x y : ComplexPoint X) (hx : x ∈ Point.overOpen V) (hy : y ∈ Point.overOpen V)
    (h : ∀ s : Γ(X.left, V), Point.evaluate V s x = Point.evaluate V s y) : x = y := by
  letI := s2e_step1_sectionAlgebra X V
  let Y := ComplexPoint.openScheme X V
  letI := s2e_step1_sectionAlgebra Y ⊤
  let A := Γ(X.left, V)
  let E := s2e_complex_affine_open_spec_iso X V hV
  let xV := (ComplexPoint.openHomeomorph X V).symm ⟨x, hx⟩
  let yV := (ComplexPoint.openHomeomorph X V).symm ⟨y, hy⟩
  have hxV : Point.map (ComplexPoint.openInclusion X V) xV = x :=
    congrArg Subtype.val ((ComplexPoint.openHomeomorph X V).apply_symm_apply ⟨x, hx⟩)
  have hyV : Point.map (ComplexPoint.openInclusion X V) yV = y :=
    congrArg Subtype.val ((ComplexPoint.openHomeomorph X V).apply_symm_apply ⟨y, hy⟩)
  have hev (z : ComplexPoint Y) (s : A) :
      ComplexPoint.affineSpecEquiv A (Point.map E.hom z) s =
        Point.evaluate V s (Point.map (ComplexPoint.openInclusion X V) z) :=
    (s2e_spec_coordinate_evaluation Y A E.hom
      (CommRingCat.ofHom (s2e_complex_open_top_section_equiv X V).toAlgHom.toRingHom)
        rfl z s).trans (s2e_complex_open_top_section_evaluate X V s z)
  have hp : Point.map E.hom xV = Point.map E.hom yV := by
    apply (ComplexPoint.affineSpecEquiv A).injective
    ext s
    rw [hev xV s, hev yV s, hxV, hyV]
    exact h s
  have hpV : xV = yV := by
    have he := congrArg (Point.map E.inv) hp
    change (xV ≫ E.hom) ≫ E.inv = (yV ≫ E.hom) ≫ E.inv at he
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he
  exact hxV.symm.trans ((congrArg (Point.map (ComplexPoint.openInclusion X V)) hpV).trans hyV)

#print axioms s2e_affine_open_points_ext
end HodgeLean.Foundations.Program
