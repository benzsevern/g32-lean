import HodgeLean.Foundations.AbelianQuotient.Defs
import HodgeLean.Foundations.GeometricIntegralitySchemes
import HodgeLean.Foundations.SegreProjectiveProofs

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- The scheme product, with its product abelian variety structure. -/
def product (A B : Variety) : Variety where
  X := MonoidalCategory.tensorObj A.X B.X
  group := GrpObj.tensorObj.instTensorObj (G := A.X) (H := B.X)
  commutative := CategoryTheory.instIsCommMonObjTensorObj (M := A.X) (N := B.X)
  integral := isIntegral_pullback_of_isAlgClosed ℂ A.X.left B.X.left A.X.hom B.X.hom
  smooth := by
    change Smooth (Limits.pullback.fst A.X.hom B.X.hom ≫ A.X.hom)
    infer_instance
  projective := by
    change IsProjective (Limits.pullback.fst A.X.hom B.X.hom ≫ A.X.hom)
    exact spec_g3c_isProjective_pullback_aux A.X.hom B.X.hom

end HodgeLean.Foundations.AbelianQuotient
