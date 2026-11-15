import HodgeLean.Ported.Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership

/-! Normalized coordinate functions on affine blow-up charts. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The regular function represented by the ratio of two ideal generators. -/
def g32l4_blowUp_coordinate {R : Type} [CommRing R] (I : Ideal R) (a b : I) :
    Γ(Spec (.of (affineBlowUpAlgebra I a)), ⊤) :=
  (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).inv.hom
    (affineBlowUpAlgebra.ratio I a b)

/-- Multiplication by the exceptional generator recovers the original ideal section. -/
theorem g32l4_blowUp_coordinate_mul {R : Type} [CommRing R] (I : Ideal R) (a b : I) :
    affineBlowUp.chartGenerator I a * g32l4_blowUp_coordinate I a b =
      (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).inv.hom
        (algebraMap R (affineBlowUpAlgebra I a) b) := by
  rw [g32l4_blowUp_coordinate, ← map_mul, ← algebraMap_eq_mul_ratio]

end HodgeLean.Foundations.Program
