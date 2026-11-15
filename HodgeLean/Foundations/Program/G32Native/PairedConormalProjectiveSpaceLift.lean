import HodgeLean.Foundations.Program.G32Native.PairedConormalProjectiveLiftGeneral
import HodgeLean.Foundations.Program.SchoenPolynomialProjectiveSpace

/-! # Global unit lifts on the supplied projective-space scheme -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The polynomial comparison transports lifting to the original projective-space scheme. -/
theorem conormal_projectiveSpace_unit_lift
    (R : Type) [CommRing R] (k : ℕ)
    (S : ShortComplex (ProjectiveSpace (Fin (k + 1)) (Spec (.of R))).Modules)
    (hs : S.ShortExact) [S.X₂.IsQuasicoherent]
    (J : Type) [Finite J] (ef : S.X₁ ≅ SheafOfModules.free J)
    (u : SheafOfModules.unit
      (ProjectiveSpace (Fin (k + 1)) (Spec (.of R))).ringCatSheaf ⟶ S.X₃) :
    ∃ l : SheafOfModules.unit
      (ProjectiveSpace (Fin (k + 1)) (Spec (.of R))).ringCatSheaf ⟶ S.X₂,
      l ≫ S.g = u := by
  exact conormal_projective_unit_lift R k
    (s2_polynomialProjectiveSpaceIso R (Fin (k + 1))) S hs J ef u

end HodgeLean.Foundations.Program.G32Native
