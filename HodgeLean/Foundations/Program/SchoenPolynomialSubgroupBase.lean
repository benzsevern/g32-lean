import HodgeLean.Foundations.Program.SchoenPolynomialSubgroupFiniteType

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual polynomial subgroup Proj comparison preserves the identified coefficient spectrum. -/
theorem s2_polynomialSubgroupProj_toCoefficient (R ι : Type) [CommRing R] :
    let 𝒢 := homogeneousSubmodule ι R
    letI := s2_submoduleGradingAsSubgroups 𝒢
    (s2_submoduleGradingProjIso 𝒢).hom ≫ Proj.toSpecZero 𝒢 ≫
        Spec.map (ProjectiveSpace.degreeZeroEquiv ι R).symm.toCommRingCatIso.hom =
      Proj.toSpecZero (s2_submoduleGradedPieces 𝒢) ≫
        Spec.map (s2_polynomialSubgroupDegreeZeroEquiv R ι).symm.toCommRingCatIso.hom := by
  letI := s2_submoduleGradingAsSubgroups (homogeneousSubmodule ι R)
  dsimp only
  rw [← Category.assoc, s2_submoduleGradingProjIso_toSpecZero, Category.assoc,
    ← Spec.map_comp]
  rfl

end HodgeLean.Foundations.Program
