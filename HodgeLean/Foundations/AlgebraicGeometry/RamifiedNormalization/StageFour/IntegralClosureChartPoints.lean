import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual normalization chart retains the default original integral-closure scalar structure and its coefficient evaluations. -/
theorem integral_closure_chart_point_homeomorph
    {A L : Type} [CommRing A] [Field L] [Algebra ℂ A]
    [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (X : Over (Spec ↧ℂ)) (p : X ⟶ Over.mk (ComplexPoint.affineSpecStructureMap A))
    (E : X.left ≅ Spec ↧(integralClosure A L))
    (hbase : E.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))) = p.left) :
    ∃ H : ComplexPoint X ≃ₜ (integralClosure A L →ₐ[ℂ] ℂ),
      (∀ x, (H x).toRingHom = Spec.homEquivRingHom (x.left ≫ E.hom)) ∧
      ∀ x, (H x).comp (IsScalarTower.toAlgHom ℂ A (integralClosure A L)) =
        ComplexPoint.affineSpecEquiv A (Point.map p x) := by
  have hStruct : Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))) ≫
      ComplexPoint.affineSpecStructureMap A =
      ComplexPoint.affineSpecStructureMap (integralClosure A L) :=
    ComplexPoint.specMap_comp_affineSpecStructureMap (IsScalarTower.toAlgHom ℂ A (integralClosure A L))
  have heover : E.hom ≫ ComplexPoint.affineSpecStructureMap (integralClosure A L) = X.hom := by
    rw [← hStruct, ← Category.assoc, hbase]
    exact p.w
  let EO : X ≅ Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) := Over.isoMk E heover
  let H := (Point.isoMapHomeomorph EO).trans (ComplexPoint.affineSpecHomeomorph (integralClosure A L))
  have hH (x : ComplexPoint X) : (H x).toRingHom = Spec.homEquivRingHom (x.left ≫ E.hom) := rfl
  refine ⟨H, hH, ?_⟩
  intro x
  apply AlgHom.toRingHom_injective
  change (H x).toRingHom.comp (algebraMap A (integralClosure A L)) = _
  rw [hH]
  have hs : (x.left ≫ E.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))) =
      (Point.map p x).left := by rw [Category.assoc, hbase]; rfl
  have h := congrArg (fun f : Spec ↧ℂ ⟶ Spec ↧A => (Spec.preimage f).hom) hs
  simp only [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp] at h
  exact h

end AlgebraicGeometry.RamifiedNormalization.StageFour
