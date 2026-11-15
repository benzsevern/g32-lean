import HodgeLean.Foundations.Program.G32Native.PairedConormalCoordinateFractionEvaluation

/-! # The coordinate fraction coefficient is the original regular coordinate ratio -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open ProjSpaceCech
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual coordinate coefficient agrees with the original regular ratio
on every coordinate intersection, retaining the numerator and denominator indices. -/
theorem paired_twist_coordinateFraction_coefficient_section
    (R : Type) [CommRing R] (n : ℕ)
    (I : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ I)
    (j : Fin (n + 1)) :
    (show Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      ProjSpace.coordinateIntersection R n I) from
        ProjSpace.twistingFractionCoefficientEquiv R n 1 i hi
          (GradedModule.sec.mk _ I (paired_twist_coordinateFraction R n I j))) =
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
        (homOfLE (ProjSpace.coordinateIntersection_le_standardOpen R n hi)).op
          (ProjSpace.coordinateRatioSection R n i j) := by
  apply Subtype.ext
  funext x
  have : x.val.asHomogeneousIdeal.toIdeal.IsPrime :=
    (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      from x.val).isPrime
  apply HomogeneousLocalization.val_injective
  erw [paired_twist_coordinateFraction_coefficient_val]
  change Localization.mk (S := x.val.asHomogeneousIdeal.toIdeal.primeCompl)
      (MvPolynomial.X j) ⟨MvPolynomial.X i, _⟩ =
    Localization.mk (S := x.val.asHomogeneousIdeal.toIdeal.primeCompl)
      (MvPolynomial.X j) ⟨(MvPolynomial.X i) ^ 1, _⟩
  congr 1
  exact Subtype.ext (pow_one _).symm

end HodgeLean.Foundations.Program.G32Native
