import HodgeLean.Foundations.Program.SchoenPolynomialScalarProj

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual polynomial Proj isomorphism to projective space over its coefficient spectrum. -/
def s2_polynomialProjectiveSpaceIso (R ι : Type) [CommRing R] :
    Proj (homogeneousSubmodule ι R) ≅ ProjectiveSpace ι (Spec (.of R)) := by
  let f := s2_polynomialIntegralCoordinates R ι
  let hf := s2_polynomialIntegralCoordinates_irrelevant R ι
  letI := s2_polynomialRelativeProj_isIso R ι
  let c := Spec.map (ProjectiveSpace.degreeZeroEquiv ι R).symm.toCommRingCatIso.hom
  haveI : IsIso c := by
    dsimp only [c]
    exact (isIso_SpecMap_iff).mpr (ProjectiveSpace.degreeZeroEquiv ι R).symm.bijective
  let e : pullback (terminal.from (Spec (.of (homogeneousSubmodule ι R 0))))
      (terminal.from (Proj (homogeneousSubmodule ι (ULift.{0} ℤ)))) ⟶
      ProjectiveSpace ι (Spec (.of R)) :=
    pullback.map _ _ _ _ c (𝟙 _) (𝟙 _) (by simp) (by simp)
  haveI : IsIso e := by dsimp only [e]; infer_instance
  exact asIso (b54_relativeProj f hf ≫ e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The polynomial Proj comparison preserves the actual coefficient structure morphism. -/
theorem s2_polynomialProjectiveSpaceIso_toBase (R ι : Type) [CommRing R] :
    (s2_polynomialProjectiveSpaceIso R ι).hom ≫
      ProjectiveSpace.toBase ι (Spec (.of R)) =
    Proj.toSpecZero (homogeneousSubmodule ι R) ≫
      Spec.map (ProjectiveSpace.degreeZeroEquiv ι R).symm.toCommRingCatIso.hom := by
  simp only [s2_polynomialProjectiveSpaceIso, asIso_hom, ProjectiveSpace.toBase,
    Category.assoc, pullback.map, pullback.lift_fst, b54_relativeProj,
    pullback.lift_fst_assoc, Category.comp_id]

end HodgeLean.Foundations.Program
