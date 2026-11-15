import HodgeLean.Foundations.Program.SchoenSelectedGeometryReducedImage
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveSubscheme

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology TopologicalSpace
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A projective algebraic carrier of an embedded space gives a reduced projective model
with the same complex-point topology.
Source: the reduced induced subscheme and the analytic topology of algebraic closed immersions. -/
theorem s0_reduced_model_of_projective_carrier
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    {C : Type} [TopologicalSpace C]
    (f : C → ComplexPoint X) (he : IsClosedEmbedding f)
    (Z : Set X.left) (hZ : IsClosed Z)
    (hcar : range f = (Point.underlying : ComplexPoint X → X.left) ⁻¹' Z) :
    ∃ Y : Over (Spec ↧ℂ), ∃ (_ : IsReduced Y.left) (_ : IsProjective Y.hom),
      ∃ i : Y ⟶ X, IsClosedImmersion i.left ∧ range i.left = Z ∧
        ∃ e : C ≃ₜ ComplexPoint Y, ∀ x, Point.map i (e x) = f x := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZ⟩ : Closeds X.left)
  let Y : Over (Spec ↧ℂ) := Over.mk (I.subschemeι ≫ X.hom)
  let i : Y ⟶ X := Over.homMk I.subschemeι rfl
  letI : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  letI : IsReduced Y.left := s0_vanishing_subscheme_reduced X.left ⟨Z, hZ⟩
  letI : IsProjective Y.hom := s0_projective_comp_closedImmersion I.subschemeι X.hom
  have hi := isClosedEmbedding_map_of_closedImmersion i
  have hri : range i.left = Z := by
    change range I.subschemeι = Z
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hr : range (Point.map i) = range f := by
    rw [range_map_of_closedImmersion, hri]
    exact hcar.symm
  let e : C ≃ₜ ComplexPoint Y := he.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr hr.symm).trans hi.isEmbedding.toHomeomorph.symm)
  refine ⟨Y, inferInstance, inferInstance, i, inferInstance, hri, e, ?_⟩
  intro x
  exact congrArg Subtype.val (hi.isEmbedding.toHomeomorph.apply_symm_apply
    ((Homeomorph.setCongr hr.symm) (he.isEmbedding.toHomeomorph x)))

#print axioms s0_reduced_model_of_projective_carrier
end HodgeLean.Foundations.Program
