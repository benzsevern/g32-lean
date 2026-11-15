import HodgeLean.Foundations.Program.SchoenCycleSectionDefinedAffineMap
import HodgeLean.Foundations.Program.SchoenCycleOpenTopSectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleComplexSectionRestriction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- On the actual basic open of an invariant function, the original open scheme maps to the localized subalgebra spectrum with every original subalgebra value retained.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_localized_subalgebra_morphism
    (X : Over (Spec ↧ℂ)) (W : X.left.Opens) (hW : IsAffineOpen W) :
    letI := s2e_step1_sectionAlgebra X W
    ∀ (S : Subalgebra ℂ Γ(X.left, W)) (g : S),
      let V := X.left.basicOpen g.val
      let Y := ComplexPoint.openScheme X V
      ∃ f : Y ⟶ Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g)),
        (∀ s : S, f.left.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away g))).inv
            (algebraMap S (Localization.Away g) s)) =
          V.topIso.inv ((X.left.presheaf.map (homOfLE (X.left.basicOpen_le g.val)).op).hom s.val)) ∧
        ∀ (z : ComplexPoint Y) (s : S),
          ComplexPoint.affineSpecEquiv (Localization.Away g) (Point.map f z)
            (algebraMap S (Localization.Away g) s) =
          Point.evaluate W s.val (Point.map (ComplexPoint.openInclusion X V) z) := by
  dsimp only
  letI := s2e_step1_sectionAlgebra X W
  intro S g
  let V := X.left.basicOpen g.val
  let Y := ComplexPoint.openScheme X V
  letI := s2e_step1_sectionAlgebra X V
  letI := s2e_step1_sectionAlgebra Y ⊤
  let C := Γ(X.left, W)
  let D := Γ(X.left, V)
  letI : Algebra C D := (X.left.presheaf.map (homOfLE (X.left.basicOpen_le g.val)).op).hom.toAlgebra
  letI : IsLocalization.Away g.val D := hW.isLocalization_basicOpen g.val
  let r := (s2e_complex_section_restriction X W V (X.left.basicOpen_le g.val)).comp S.val
  have hr : IsUnit (r g) := IsLocalization.Away.algebraMap_isUnit (S := D) g.val
  let L : Localization.Away g →ₐ[ℂ] D := IsLocalization.Away.liftAlgHom g hr
  let G := (s2e_complex_open_top_section_equiv X V).toAlgHom.comp L
  let f := s2e_section_defined_affine_map Y (Localization.Away g) G
  have hglobal (s : S) : f.left.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away g))).inv
        (algebraMap S (Localization.Away g) s)) =
      V.topIso.inv ((X.left.presheaf.map (homOfLE (X.left.basicOpen_le g.val)).op).hom s.val) := by
    have he := congrArg (fun m : CommRingCat.of (Localization.Away g) ⟶ Γ(Y.left, ⊤) =>
      m.hom (algebraMap S (Localization.Away g) s))
      (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom G.toRingHom))
    change f.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away g))).inv
      (algebraMap S (Localization.Away g) s)) = G (algebraMap S (Localization.Away g) s) at he
    rw [he]
    change V.topIso.inv (L (algebraMap S (Localization.Away g) s)) = V.topIso.inv (r s)
    rw [show L (algebraMap S (Localization.Away g) s) = r s from IsLocalization.Away.lift_eq g hr s]
  refine ⟨f, hglobal, ?_⟩
  intro z s
  have hz : Point.map (ComplexPoint.openInclusion X V) z ∈ Point.overOpen V :=
    (ComplexPoint.openEquiv X V z).property
  calc
    ComplexPoint.affineSpecEquiv (Localization.Away g) (Point.map f z)
        (algebraMap S (Localization.Away g) s) =
        Point.evaluate ⊤ (G (algebraMap S (Localization.Away g) s)) z :=
      s2e_spec_coordinate_evaluation Y _ f (CommRingCat.ofHom G.toRingHom) rfl z _
    _ = Point.evaluate V (L (algebraMap S (Localization.Away g) s))
        (Point.map (ComplexPoint.openInclusion X V) z) :=
      s2e_complex_open_top_section_evaluate X V _ z
    _ = Point.evaluate V (r s) (Point.map (ComplexPoint.openInclusion X V) z) := by
      rw [show L (algebraMap S (Localization.Away g) s) = r s from
        IsLocalization.Away.lift_eq g hr s]
    _ = _ := (Point.evaluate_res (X.left.basicOpen_le g.val) s.val
      (Point.map (ComplexPoint.openInclusion X V) z) hz).symm

#print axioms s2e_localized_subalgebra_morphism
end HodgeLean.Foundations.Program
