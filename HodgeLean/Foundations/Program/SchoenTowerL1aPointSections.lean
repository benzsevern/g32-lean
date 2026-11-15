import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenTowerL1aRationalKernels
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace

/-! # Actual section evaluation and point kernels

Global section evaluation at the retained complex point is its actual
section pullback followed by the coefficient-ring identification.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual ring homomorphism evaluating global sections at a complex point.
Source: Hartshorne, Algebraic Geometry, II.2, section pullback along a rational point. -/
def s2v_l1a_pointSectionEvaluation
    (Z : Over (Spec ↧ℂ)) (p : ComplexPoint Z) : Γ(Z.left, ⊤) →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp p.left.appTop.hom

/-- The actual evaluation homomorphism agrees with retained point evaluation.
Source: Hartshorne, Algebraic Geometry, II.2, evaluation of sections at rational points. -/
theorem s2v_l1a_pointSectionEvaluation_apply
    (Z : Over (Spec ↧ℂ)) (p : ComplexPoint Z) (s : Γ(Z.left, ⊤)) :
    s2v_l1a_pointSectionEvaluation Z p s = Point.evaluate ⊤ s p :=
  (ComplexPoint.evaluate_top_eq_appTop s p).symm

/-- Evaluation of global sections at an actual complex point is surjective.
Source: Hartshorne, Algebraic Geometry, II.2, constants and rational point evaluation. -/
theorem s2v_l1a_pointSectionEvaluation_surjective
    (Z : Over (Spec ↧ℂ)) (p : ComplexPoint Z) :
    Function.Surjective (s2v_l1a_pointSectionEvaluation Z p) := by
  have hcomp : Z.hom.appTop ≫ p.left.appTop = 𝟙 Γ(Spec (CommRingCat.of ℂ), ⊤) := by
    rw [← Scheme.Hom.comp_appTop, Over.w]
    exact Scheme.Hom.id_appTop
  intro c
  refine ⟨Z.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c), ?_⟩
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
    ((Z.hom.appTop ≫ p.left.appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c
  rw [hcomp]
  exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply c

/-- The actual kernel of evaluation at a retained complex point is maximal.
Source: Hartshorne, Algebraic Geometry, II.2, rational points and maximal ideals. -/
theorem s2v_l1a_pointSectionEvaluation_maximal
    (Z : Over (Spec ↧ℂ)) (p : ComplexPoint Z) :
    (RingHom.ker (s2v_l1a_pointSectionEvaluation Z p)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (s2v_l1a_pointSectionEvaluation_surjective Z p)

/-- On an actual affine scheme, the point ideal on global sections is the evaluation kernel.
Source: Hartshorne, Algebraic Geometry, II.2, ideal sheaves of rational points. -/
theorem s2v_l1a_pointSectionEvaluation_kernel
    (Z : Over (Spec ↧ℂ)) [IsAffine Z.left] (p : ComplexPoint Z) :
    RingHom.ker (s2v_l1a_pointSectionEvaluation Z p) =
      (p.left.ker).ideal ⟨⊤, isAffineOpen_top _⟩ := by
  rw [Scheme.Hom.ker_apply]
  exact RingHom.ker_equiv_comp p.left.appTop.hom
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Distinct retained complex points of an affine scheme have distinct actual evaluation kernels.
Source: Hartshorne, Algebraic Geometry, II.2, the affine scheme and rational point correspondence. -/
theorem s2v_l1a_pointSectionEvaluation_kernel_injective
    (Z : Over (Spec ↧ℂ)) [IsAffine Z.left] :
    Function.Injective (fun p : ComplexPoint Z =>
      RingHom.ker (s2v_l1a_pointSectionEvaluation Z p)) := by
  let c : ℂ →+* Γ(Z.left, ⊤) := Z.hom.appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hsplit (p : ComplexPoint Z) :
      (s2v_l1a_pointSectionEvaluation Z p).comp c = RingHom.id ℂ := by
    have hcomp : Z.hom.appTop ≫ p.left.appTop = 𝟙 Γ(Spec (CommRingCat.of ℂ), ⊤) := by
      rw [← Scheme.Hom.comp_appTop, Over.w]
      exact Scheme.Hom.id_appTop
    apply RingHom.ext
    intro k
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
      ((Z.hom.appTop ≫ p.left.appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom k)) = k
    rw [hcomp]
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply k
  intro p q hpq
  have heq := s2v_l1a_rational_evaluations_eq_of_kernel_eq c
    (s2v_l1a_pointSectionEvaluation Z p) (s2v_l1a_pointSectionEvaluation Z q)
    (hsplit p) (hsplit q) hpq
  apply Over.OverMorphism.ext
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective
  exact DFunLike.congr_fun heq s

/-- Actual global section evaluation commutes with the retained morphism of complex schemes.
Source: Hartshorne, Algebraic Geometry, II.2, functoriality of section pullback. -/
theorem s2v_l1a_pointSectionEvaluation_map
    {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) (p : ComplexPoint X) :
    s2v_l1a_pointSectionEvaluation Y (Point.map f p) =
      (s2v_l1a_pointSectionEvaluation X p).comp f.left.appTop.hom := by
  apply RingHom.ext
  intro s
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
    ((p.left ≫ f.left).appTop.hom s) = _
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- Evaluation of an actual constant section recovers its retained complex value.
Source: Hartshorne, Algebraic Geometry, II.2, rational point evaluation of constants. -/
theorem s2v_l1a_pointSectionEvaluation_constant
    (Z : Over (Spec ↧ℂ)) (p : ComplexPoint Z) (c : ℂ) :
    s2v_l1a_pointSectionEvaluation Z p
      (Z.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
    ((Z.hom.appTop ≫ p.left.appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c
  rw [← Scheme.Hom.comp_appTop, Over.w]
  exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply c

end HodgeLean.Foundations.Program
