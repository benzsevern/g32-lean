import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralClosureChartPoints
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientFibre

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Restricting the actual normalization chart to fixed original coefficients retains exactly the integral evaluation fibre. -/
theorem integral_closure_chart_coefficient_fibre_homeomorph
    {R A L : Type} [CommRing R] [CommRing A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (f : R →ₐ[ℂ] A) (φ : R →ₐ[ℂ] ℂ)
    (X : Over (Spec ↧ℂ)) (p : X ⟶ Over.mk (ComplexPoint.affineSpecStructureMap A))
    (E : X.left ≅ Spec ↧(integralClosure A L))
    (hbase : E.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))) = p.left) :
    ∃ H : {x : ComplexPoint X //
        ComplexPoint.affineSpecComplexPointMap f (Point.map p x) =
          (ComplexPoint.affineSpecEquiv R).symm φ} ≃ₜ integralCoefficientFibre (L := L) f φ,
      ∀ x, (H x).val.toRingHom = Spec.homEquivRingHom (x.val.left ≫ E.hom) := by
  obtain ⟨H, hH, hcoeff⟩ := integral_closure_chart_point_homeomorph X p E hbase
  have hiff (x : ComplexPoint X) :
      (ComplexPoint.affineSpecComplexPointMap f (Point.map p x) =
        (ComplexPoint.affineSpecEquiv R).symm φ) ↔
      ∀ r, (H x) (algebraMap A (integralClosure A L) (f r)) = φ r := by
    rw [← (ComplexPoint.affineSpecEquiv R).injective.eq_iff,
      ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap, Equiv.apply_symm_apply]
    rw [← hcoeff x]
    constructor
    · intro he r
      exact DFunLike.congr_fun he r
    · intro hr
      apply AlgHom.ext
      exact hr
  exact ⟨H.subtype hiff, fun x => hH x.val⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
