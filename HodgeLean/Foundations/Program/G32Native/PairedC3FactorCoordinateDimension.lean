import HodgeLean.Foundations.Program.G32Native.PairedC3FactorCoordinateNormalization

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Normalize the coordinate factor with a separately named ambient dimension. -/
theorem paired_c3_factor_coordinate_normalization_of_dimension {k n m : ℕ}
    (hm : n + 1 = m)
    (i : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) ⟶
      ProjectiveSpace (Fin m) (Spec ↧ℂ))
    (C : PairedC3ProjectiveFactorCoordinates k n _ i)
    (j : Fin (k + 1) ↪ Fin m) :
    ∃ e : ProjectiveSpace (Fin m) (Spec ↧ℂ) ≅ ProjectiveSpace (Fin m) (Spec ↧ℂ),
      i ≫ e.hom = (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).inv ≫
        pairedC3PolynomialCoordinateInclusion (A := ℂ) j ≫
        (s2_polynomialProjectiveSpaceIso ℂ (Fin m)).hom := by
  subst m
  exact paired_c3_factor_coordinate_normalization i C j

#print axioms paired_c3_factor_coordinate_normalization_of_dimension
end HodgeLean.Foundations.Program.G32Native
