import HodgeLean.Foundations.Program.G32Native.PairedC3SpecRestrictionAlgebra
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualRestrictionScheme

/-! # Complex restriction on the original residual quotient charts -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- The original quotient restriction is complex linear for the original
residual chart structure maps. The base equation follows from the actual
residual scheme transition. -/
def pairedC3ResidualRestrictionAlgHom
    (X : Over (Spec ↧ℂ)) (I : X.left.IdealSheafData)
    (V W : X.left.affineOpens) (hWV : W.1 ≤ V.1) :
    let pV := I.subschemeCover.f V ≫ I.subschemeι ≫ X.hom
    let pW := I.subschemeCover.f W ≫ I.subschemeι ≫ X.hom
    letI := pairedC3SpecAlgebra pV
    letI := pairedC3SpecAlgebra pW
    (Γ(X.left, V) ⧸ I.ideal V) →ₐ[ℂ] (Γ(X.left, W) ⧸ I.ideal W) :=
  pairedC3SpecRestrictionAlgHom _ _ (pairedC3AffineResidualRestriction I V W hWV)
    (by rw [← Category.assoc, pairedC3_residual_restriction_scheme])

/-- The actual projective chart maps restrict along the original residual
quotient maps, with the original complex structure on both opens. -/
theorem pairedC3_residual_projective_restriction
    (X : Over (Spec ↧ℂ)) (I : X.left.IdealSheafData)
    (V W : X.left.affineOpens) (hWV : W.1 ≤ V.1)
    (i : Fin 2) (t : Γ(X.left, V) ⧸ I.ideal V) :
    let pV := I.subschemeCover.f V ≫ I.subschemeι ≫ X.hom
    let pW := I.subschemeCover.f W ≫ I.subschemeι ≫ X.hom
    letI := pairedC3SpecAlgebra pV
    letI := pairedC3SpecAlgebra pW
    Spec.map (CommRingCat.ofHom (pairedC3AffineResidualRestriction I V W hWV)) ≫
      (projectiveLineChart i t).left =
        (projectiveLineChart i (pairedC3AffineResidualRestriction I V W hWV t)).left := by
  letI := pairedC3SpecAlgebra (I.subschemeCover.f V ≫ I.subschemeι ≫ X.hom)
  letI := pairedC3SpecAlgebra (I.subschemeCover.f W ≫ I.subschemeι ≫ X.hom)
  dsimp only
  exact pairedC3_projective_chart_restriction
    (pairedC3ResidualRestrictionAlgHom X I V W hWV) i t

#print axioms pairedC3ResidualRestrictionAlgHom
#print axioms pairedC3_residual_projective_restriction
end HodgeLean.Foundations.Program.G32Native
