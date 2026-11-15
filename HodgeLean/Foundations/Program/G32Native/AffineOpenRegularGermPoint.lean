import HodgeLean.Foundations.Program.G32Native.AffineOpenPointFactorization
import HodgeLean.Foundations.Program.G32Native.AnalyticPointDerivation

/-! # The original regular germ point on an ambient affine open -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- Evaluation of the original regular germ map gives the canonical affine
factorization of the same original ambient point. -/
theorem affineOpenRegularGerm_point (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p : ComplexPoint W)
    (U : W.left.Opens) (hU : IsAffineOpen U) (hp : p ∈ Point.overOpen U) :
    Spec.map (CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp
      (s2e_regularSection_nativeAnalyticGerm W d p U hp))) ≫ hU.fromSpec = p.left := by
  have he : CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp
      (s2e_regularSection_nativeAnalyticGerm W d p U hp)) =
      U.topIso.inv ≫ (liftToOpen W U p hp).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := by
    ext r
    change s2e_nativeAnalyticGerm_value d
      (s2e_regularSection_nativeAnalyticGerm W d p U hp r) = _
    rw [s2e_regularSection_nativeAnalyticGerm_value]
    exact (affineOpenPoint_sectionValue W U p hp r).symm
  rw [he]
  exact affineOpenPoint_factorization W U hU p hp

#print axioms affineOpenRegularGerm_point
end HodgeLean.Foundations.Program.G32Native
