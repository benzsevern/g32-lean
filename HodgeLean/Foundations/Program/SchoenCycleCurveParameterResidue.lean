import HodgeLean.Foundations.Program.SchoenCycleCurveParameters

/-! # Residue vanishing of actual native curve parameters -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The chosen actual curve parameter has zero scalar residue at its point.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_curvePointParameter_residue
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] (p : ComplexPoint X) :
    p.stalkHom.hom (s2e_curvePointParameter X p) = 0 := by
  have hsurj : Function.Surjective p.stalkHom.hom := by
    intro c
    exact ⟨HodgeLean.Foundations.Curves.stalkC p.underlying c,
      s2e_complex_point_stalk_constants X p c⟩
  have hker := IsLocalRing.ker_eq_maximalIdeal p.stalkHom.hom hsurj
  change s2e_curvePointParameter X p ∈ RingHom.ker p.stalkHom.hom
  rw [hker, s2e_curvePointParameter_maximalIdeal]
  exact Ideal.subset_span rfl

/-- Pullback to the base stalk of the actual point kills its regular parameter.
Source: Mathlib, AlgebraicGeometry.stalkClosedPointIso and
AlgebraicGeometry.Scheme.stalkClosedPointTo. -/
theorem s2e_curvePointParameter_point_stalkMap_zero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] (p : ComplexPoint X) :
    p.left.stalkMap (IsLocalRing.closedPoint ℂ) (s2e_curvePointParameter X p) = 0 := by
  apply (ConcreteCategory.bijective_of_isIso
    (stalkClosedPointIso (CommRingCat.of ℂ)).hom).1
  change (Scheme.stalkClosedPointTo p.left).hom (s2e_curvePointParameter X p) = _
  have h := s2e_curvePointParameter_residue X p
  change (Scheme.stalkClosedPointTo p.left).hom (s2e_curvePointParameter X p) = 0 at h
  simpa only [map_zero] using h

end HodgeLean.Foundations.Program
