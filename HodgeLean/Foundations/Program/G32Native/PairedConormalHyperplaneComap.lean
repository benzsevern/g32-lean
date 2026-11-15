import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialOpens
import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeHyperplaneForms
import HodgeLean.Foundations.Program.SchoenCycleProjectiveAffineIdeals
import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs

/-! # The actual hyperplane ideal under the specified polynomial projective comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original reduced hyperplane ideal pulls back to the actual native coordinate-zero ideal. -/
theorem conormal_polynomial_hyperplane_comap (k : ℕ) :
    (s2e_hyperplaneIdeal k).comap
      (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom =
      conormalNativeHyperplaneIdeal ℂ k := by
  rw [s2e_hyperplaneIdeal, s2e_open_comap_vanishingIdeal]
  unfold conormalNativeHyperplaneIdeal
  congr 1
  apply Closeds.ext
  ext x
  change x ∉ ((s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom ⁻¹ᵁ
      projectiveSpaceBasicOpen k (X 0)) ↔ x ∉ ProjSpace.standardOpen ℂ k 0
  rw [conormal_polynomialProjectiveSpaceIso_preimage_coordinate]

end HodgeLean.Foundations.Program.G32Native
