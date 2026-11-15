import HodgeLean.Foundations.Program.G32Native.PairedConormalCoordinateFraction

/-! # Actual evaluation of the original degree-one coordinate fractions -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open ProjSpaceCech
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

variable (R : Type) [CommRing R] (n : ℕ)

/-- The coordinate frame adds exactly the original coordinate variable to the denominator. -/
theorem paired_twist_coordinateFraction_shift_denominator
    (I : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ I)
    (j : Fin (n + 1)) :
    (∏ l : Fin (n + 1), (MvPolynomial.X l : MvPolynomial (Fin (n + 1)) R) ^
      (GradedModule.coordinateDenominatorFrac (GradedModule.free R n) 1 i hi
        (paired_twist_coordinateFraction R n I j)).denExp l) = MvPolynomial.X i := by
  classical
  simp_rw [paired_twist_coordinateFraction_shift_denExp]
  rw [Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, pow_one]
  · intro l _ hli
    rw [Pi.single_eq_of_ne hli, pow_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The actual coefficient section has numerator `X j` and denominator `X i`
at every original projective point of the coordinate intersection. -/
theorem paired_twist_coordinateFraction_coefficient_val
    (I : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ I)
    (j : Fin (n + 1)) (x : ProjSpace.coordinateIntersection R n I) :
    let P : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := x.val
    let : P.asHomogeneousIdeal.toIdeal.IsPrime := P.isPrime
    ((ProjSpace.twistingFractionCoefficientEquiv R n 1 i hi
      (GradedModule.sec.mk _ I (paired_twist_coordinateFraction R n I j))).val x).val =
      Localization.mk (S := P.asHomogeneousIdeal.toIdeal.primeCompl) (MvPolynomial.X j)
        ⟨MvPolynomial.X i, ProjSpace.coordinateIntersection_le_standardOpen R n hi x.property⟩ := by
  intro P hP
  rw [ProjSpace.twistingFractionCoefficientEquiv_apply,
    GradedModule.coordinateShiftEquiv_apply_mk]
  have he := ProjSpace.unitFreeFractionEquiv_apply_mk_val R n I ⟨i, hi⟩
    (GradedModule.coordinateDenominatorFrac (GradedModule.free R n) 1 i hi
      (paired_twist_coordinateFraction R n I j)) x
  simpa only [paired_twist_coordinateFraction_shift_num,
    paired_twist_coordinateFraction_shift_denominator] using he

end HodgeLean.Foundations.Program.G32Native
