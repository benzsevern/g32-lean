import HodgeLean.Foundations.Program.SchoenSubmoduleGradingBase
import HodgeLean.Foundations.Program.SchoenPolynomialProjectiveSpace
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial AlgebraicGeometry
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual polynomial subgroup degree zero identifies with the coefficient ring. -/
def s2_polynomialSubgroupDegreeZeroEquiv (R ι : Type) [CommRing R] :
    letI := s2_submoduleGradingAsSubgroups (homogeneousSubmodule ι R)
    s2_submoduleGradedPieces (homogeneousSubmodule ι R) 0 ≃+* R := by
  letI := s2_submoduleGradingAsSubgroups (homogeneousSubmodule ι R)
  exact (s2_submoduleDegreeZeroEquiv (homogeneousSubmodule ι R)).symm.trans
    (ProjectiveSpace.degreeZeroEquiv ι R)

/-- Polynomials in finitely many variables are of finite type over their actual subgroup degree zero. -/
theorem s2_polynomialSubgroup_finiteType (R ι : Type) [CommRing R] [Finite ι] :
    letI := s2_submoduleGradingAsSubgroups (homogeneousSubmodule ι R)
    Algebra.FiniteType (s2_submoduleGradedPieces (homogeneousSubmodule ι R) 0)
      (MvPolynomial ι R) := by
  letI := s2_submoduleGradingAsSubgroups (homogeneousSubmodule ι R)
  let c := (s2_polynomialSubgroupDegreeZeroEquiv R ι).symm.toRingHom
  rw [← RingHom.finiteType_algebraMap]
  apply RingHom.FiniteType.of_comp_finiteType (f := c)
  have hc : (algebraMap (s2_submoduleGradedPieces (homogeneousSubmodule ι R) 0)
      (MvPolynomial ι R)).comp c = algebraMap R (MvPolynomial ι R) := by
    apply RingHom.ext
    intro r
    rfl
  rw [hc]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- Noetherian coefficients give noetherian actual polynomial subgroup degree zero. -/
theorem s2_polynomialSubgroup_degreeZero_noetherian (R ι : Type) [CommRing R]
    [IsNoetherianRing R] :
    letI := s2_submoduleGradingAsSubgroups (homogeneousSubmodule ι R)
    IsNoetherianRing (s2_submoduleGradedPieces (homogeneousSubmodule ι R) 0) := by
  letI := s2_submoduleGradingAsSubgroups (homogeneousSubmodule ι R)
  exact isNoetherianRing_of_surjective R _
    (s2_polynomialSubgroupDegreeZeroEquiv R ι).symm.toRingHom
    (s2_polynomialSubgroupDegreeZeroEquiv R ι).symm.surjective

end HodgeLean.Foundations.Program
