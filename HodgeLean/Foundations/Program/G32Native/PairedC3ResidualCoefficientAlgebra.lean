import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualCoefficientScheme
import HodgeLean.Foundations.Program.G32Native.PairedC3SpecRestrictionAlgebra

/-! # Complex coefficients on the actual residual base and chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The quotient coefficient homomorphism is complex linear for the
algebras induced by the original structure morphisms. -/
def pairedC3ResidualCoefficientAlgHom
    (X Y : Over (Spec ↧ℂ)) (p : Y ⟶ X) (M : X.left.IdealSheafData)
    (U : X.left.affineOpens) (V : Y.left.affineOpens)
    (hV : V.1 ≤ p.left ⁻¹ᵁ U.1) :
    let pA := M.subschemeCover.f U ≫ M.subschemeι ≫ X.hom
    let pB := (M.comap p.left).subschemeCover.f V ≫
      (M.comap p.left).subschemeι ≫ Y.hom
    letI := pairedC3SpecAlgebra pA
    letI := pairedC3SpecAlgebra pB
    (Γ(X.left, U) ⧸ M.ideal U) →ₐ[ℂ]
      (Γ(Y.left, V) ⧸ (M.comap p.left).ideal V) := by
  refine pairedC3SpecRestrictionAlgHom _ _
    (pairedC3AffineResidualCoefficient p.left M U V hV) ?_
  have h := congrArg (fun q => q ≫ X.hom)
    (pairedC3_residual_coefficient_scheme p.left M U V hV)
  simpa only [Category.assoc, Over.w p] using h

/-- Smoothness of the original residual base restricts to its actual
quotient spectrum, with the induced complex algebra. -/
theorem pairedC3_residual_coefficient_base_smooth
    (X : Over (Spec ↧ℂ)) (M : X.left.IdealSheafData)
    (U : X.left.affineOpens) (hs : Smooth (M.subschemeι ≫ X.hom)) :
    let pA := M.subschemeCover.f U ≫ M.subschemeι ≫ X.hom
    letI := pairedC3SpecAlgebra pA
    Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (Γ(X.left, U) ⧸ M.ideal U)))) := by
  letI := pairedC3SpecAlgebra (M.subschemeCover.f U ≫ M.subschemeι ≫ X.hom)
  change Smooth (ComplexPoint.affineSpecStructureMap _)
  rw [pairedC3_spec_algebra_structure_map]
  letI := hs
  change Smooth (M.subschemeCover.f U ≫ (M.subschemeι ≫ X.hom))
  infer_instance

#print axioms pairedC3ResidualCoefficientAlgHom
#print axioms pairedC3_residual_coefficient_base_smooth
end HodgeLean.Foundations.Program.G32Native
