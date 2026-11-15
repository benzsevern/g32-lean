import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveChartOver
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveIntegral
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A standard projective-line patch is an affine line over the complex numbers. -/
def s0_projective_line_patch_iso (i : Fin 2) :
    Over.mk ((s0_complex_projective_cover 1).f i ≫ ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)) ≅
      Over.mk (affineSpecStructureMap (MvPolynomial (Fin 1) ℂ)) := by
  letI : Algebra (ULift.{0} ℤ) ℂ :=
    ((Int.castRingHom ℂ).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom).toAlgebra
  let J := {j : Fin 2 // j ≠ i}
  have hc : Fintype.card J = Fintype.card (Fin 1) := by
    simp [J, Fintype.card_subtype_compl]
  let E : MvPolynomial J ℂ ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
    MvPolynomial.renameEquiv ℂ (Fintype.equivOfCardEq hc)
  let e₁ : (s0_complex_projective_cover 1).X i ≅
      Spec ↧(MvPolynomial J ℂ) :=
    (pullback.congrHom rfl (Subsingleton.elim _ _)) ≪≫ s0_projective_chart_fiber_iso ℂ i
  let e₂ := Scheme.Spec.mapIso E.toRingEquiv.symm.toCommRingCatIso.op
  refine Over.isoMk (e₁ ≪≫ e₂) ?_
  have hE : e₂.hom ≫ affineSpecStructureMap (MvPolynomial (Fin 1) ℂ) =
      affineSpecStructureMap (MvPolynomial J ℂ) := by
    change Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ _ = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact E.symm.commutes c
  change (e₁.hom ≫ e₂.hom) ≫ affineSpecStructureMap (MvPolynomial (Fin 1) ℂ) = _
  rw [Category.assoc]
  erw [hE]
  dsimp only [e₁, Iso.trans_hom]
  rw [Category.assoc, s0_projective_chart_fiber_iso_over]
  simp only [s0_complex_projective_cover, Scheme.Pullback.openCoverOfRight_f,
    Over.mk_hom, ProjectiveSpace.toBase, pullback.congrHom_hom,
    pullback.map, pullback.lift_fst, Category.comp_id]

#print axioms s0_projective_line_patch_iso
end HodgeLean.Foundations.Program
