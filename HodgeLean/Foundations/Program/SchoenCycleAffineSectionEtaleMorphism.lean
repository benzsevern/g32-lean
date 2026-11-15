import HodgeLean.Foundations.Program.SchoenCycleOpenTopSectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleAffineOpenSpecIso

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An etale extension of the actual affine section algebra defines an etale map to the original scheme, with exactly those section values at complex points.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8; EGA IV, 17.11.1. -/
theorem s2e_affine_section_etale_morphism
    (B : Over (Spec ↧ℂ)) (U : B.left.Opens) (hU : IsAffineOpen U)
    (T : Type) [CommRing T] [Algebra ℂ T] :
    letI := s2e_step1_sectionAlgebra B U
    ∀ G : Γ(B.left, U) →ₐ[ℂ] T, G.toRingHom.Etale →
    ∃ f : Over.mk (ComplexPoint.affineSpecStructureMap T) ⟶ B,
      Etale f.left ∧
      ∀ (z : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap T))) (a : Γ(B.left, U)),
        Point.evaluate U a (Point.map f z) = ComplexPoint.affineSpecEquiv T z (G a) := by
  letI := s2e_step1_sectionAlgebra B U
  intro G hG
  let Y := ComplexPoint.openScheme B U
  letI := s2e_step1_sectionAlgebra Y ⊤
  let A := Γ(B.left, U)
  let E := s2e_complex_affine_open_spec_iso B U hU
  let φ : Over.mk (ComplexPoint.affineSpecStructureMap T) ⟶
      Over.mk (ComplexPoint.affineSpecStructureMap A) :=
    Over.homMk (Spec.map (CommRingCat.ofHom G.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap G)
  haveI : Etale φ.left := by
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hG
  haveI : IsIso E.inv.left := by
    change IsIso ((Over.forget _).map E.inv)
    infer_instance
  haveI : Etale (ComplexPoint.openInclusion B U).left := by
    change Etale U.ι
    infer_instance
  let f := φ ≫ E.inv ≫ ComplexPoint.openInclusion B U
  haveI : Etale f.left := by
    change Etale (φ.left ≫ E.inv.left ≫ (ComplexPoint.openInclusion B U).left)
    infer_instance
  refine ⟨f, inferInstance, ?_⟩
  intro z a
  let w := Point.map E.inv (Point.map φ z)
  have he := s2e_spec_coordinate_evaluation Y A E.hom
    (CommRingCat.ofHom (s2e_complex_open_top_section_equiv B U).toAlgHom.toRingHom) rfl w a
  have hz : Point.map E.hom w = Point.map φ z := by
    change (Point.map φ z ≫ E.inv) ≫ E.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    Point.evaluate U a (Point.map f z) =
        Point.evaluate U a (Point.map (ComplexPoint.openInclusion B U) w) := rfl
    _ = Point.evaluate ⊤ (s2e_complex_open_top_section_equiv B U a) w :=
      (s2e_complex_open_top_section_evaluate B U a w).symm
    _ = ComplexPoint.affineSpecEquiv A (Point.map E.hom w) a := he.symm
    _ = ComplexPoint.affineSpecEquiv T z (G a) := by
      rw [hz]
      exact congrArg (fun k : A →ₐ[ℂ] ℂ => k a)
        (ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap G z)

#print axioms s2e_affine_section_etale_morphism
end HodgeLean.Foundations.Program
