import HodgeLean.Foundations.Program.SchoenPolynomialScalarProjCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial HomogeneousLocalization CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Polynomial integral coordinates satisfy the actual irrelevant-ideal bound. -/
theorem s2_polynomialIntegralCoordinates_irrelevant (R ι : Type) [CommRing R] :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι (ULift.{0} ℤ))).map
        (s2_polynomialIntegralCoordinates R ι) := by
  apply (b54_polynomial_irrelevant_le_variables ι R).trans
  rw [Ideal.span_le, Set.range_subset_iff]
  intro i
  rw [← s2_polynomialIntegralCoordinates_X R ι i]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _
    zero_lt_one (isHomogeneous_X _ i))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar extension identifies polynomial Proj with the actual relative product over integer Proj. -/
theorem s2_polynomialRelativeProj_isIso (R ι : Type) [CommRing R] :
    IsIso (b54_relativeProj (s2_polynomialIntegralCoordinates R ι)
      (s2_polynomialIntegralCoordinates_irrelevant R ι)) := by
  let f := s2_polynomialIntegralCoordinates R ι
  let hf := s2_polynomialIntegralCoordinates_irrelevant R ι
  let G := homogeneousSubmodule ι (ULift.{0} ℤ)
  let H := homogeneousSubmodule ι R
  let 𝒰 := Proj.affineOpenCoverOfIrrelevantLESpan G X (isHomogeneous_X _)
    (fun _ => zero_lt_one) (b54_polynomial_irrelevant_le_variables _ _)
  apply IsZariskiLocalAtTarget.of_openCover (P := .isomorphisms _)
    (b54_productOpenCover (Spec (.of (H 0))) 𝒰.openCover)
  intro i
  have h := (b54_relativeProj_chart_isPullback f hf (isHomogeneous_X _ i)
    zero_lt_one).flip
  haveI := s2_polynomialRelativeProjChart_isIso R ι i
  change IsIso (pullback.snd (b54_relativeProj f hf)
    (b54_productChart (Spec (.of (H 0)))
      (Proj.awayι G (X i) (isHomogeneous_X _ i) zero_lt_one)))
  rw [← h.isoPullback_inv_snd]
  infer_instance

end HodgeLean.Foundations.Program
