import HodgeLean.Foundations.Program.G32Native.PairedC3MarkedPointFactorization
import HodgeLean.Foundations.Program.SchoenCycleS3LinearPoints

/-! # Section coordinates with the original projective source -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A section-space description of the actual inclusion, evaluated on the
original source vectors. Only the ambient space changes coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(ii). -/
structure PairedC3ProjectiveFactorCoordinates (k n : ℕ) (Y : Scheme)
    (i : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) ⟶ Y) where
  targetSpace : Type
  [targetAdd : AddCommGroup targetSpace]
  [targetModule : Module ℂ targetSpace]
  [targetFinite : Module.Finite ℂ targetSpace]
  targetDimension : Module.finrank ℂ targetSpace = n + 1
  ambient : ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) ≅ Y
  embedding : (Fin (k + 1) → ℂ) →ₗ[ℂ] targetSpace
  embedding_injective : Function.Injective embedding
  point_formula : ∀ (v : Fin (k + 1) → ℂ) (hv : v ≠ 0),
    (vectorToComplexPoint v hv).left ≫ i =
      (s2e_finiteDimensionalProjectivePointEquiv n targetDimension
        (Projectivization.mk ℂ (embedding v)
          (fun h => hv (embedding_injective (h.trans (map_zero embedding).symm))))).left ≫ ambient.hom

end HodgeLean.Foundations.Program.G32Native
