import HodgeLean.Foundations.RationalHomologyManifold.BoundaryImageSoftness
import HodgeLean.Foundations.RationalHomologyManifold.SoftSheafTransport
import HodgeLean.Foundations.DolbeaultCurve3

/-! Softness of the actual truncation cokernel in the supported subdivision model.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual boundary cokernel in positive orientation degree is soft.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.10 and VI.12; quotients of soft boundary and chain sheaves.
HC no distance; AV milestone no distance.
-/
theorem subdivision_boundary_cokernel_isSoft (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X (n + 1)) :
    IsSoft (cokernel ((subdivisionLimitSheafComplex X).d (n + 2) (n + 1))) := by
  let f := (subdivisionLimitSheafComplex X).d (n + 2) (n + 1)
  let S := ShortComplex.mk (image.ι f) (cokernel.π (image.ι f)) (cokernel.condition (image.ι f))
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (image.ι f) }
  have hq : IsSoft (cokernel (image.ι f)) := spec_isSoft_of_shortExact hS
    (subdivision_boundary_image_isSoft X t n o) (subdivisionLimitSheaf_isSoft X (n + 1))
  let e : cokernel f ≅ cokernel (image.ι f) :=
    (cokernelIsoOfEq (image.fac f)).symm ≪≫ cokernelEpiComp (factorThruImage f) (image.ι f)
  exact isSoft_of_sheaf_iso e.symm hq

#print axioms subdivision_boundary_cokernel_isSoft
end HodgeLean.Foundations.RationalHomologyManifold
