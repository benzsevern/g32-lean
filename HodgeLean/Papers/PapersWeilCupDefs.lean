import HodgeLean.Papers.PapersLefschetzGeneral

/-! # Cup closure restricted to the Pohlmann--Weil algebra -/

noncomputable section
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters NumberField

namespace HodgeLean.Papers

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]
variable {L : Type*} [Field L] [Algebra ℚ L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

/-- Algebraic classes that lie in the pulled-Weil cup algebra multiply to algebraic classes.
Source: PW v0.3, Theorem 4.2, proof, paragraph "Conclusion"; Fulton, *Intersection Theory*,
2nd ed., Chapter 8 and Corollary 19.2. -/
def papw_PWCupClosed (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) : Prop :=
  ∀ {p q : ℕ} (h : 2 * p + 2 * q = 2 * (p + q))
    (a : HQ Y (2 * p)) (b : HQ Y (2 * q)),
    a ∈ algebraicCycleClassSpan Y p →
    a ∈ f1_pulledWeilCupSpan A θ u d hu hW P (algebraicCycleClassSpan Y 1) p →
    b ∈ algebraicCycleClassSpan Y q →
    b ∈ f1_pulledWeilCupSpan A θ u d hu hW P (algebraicCycleClassSpan Y 1) q →
    (cupProductOf Y).cup h a b ∈ algebraicCycleClassSpan Y (p + q)

example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) (h : papw_PWCupClosed A θ u d hu hW P) :
    papw_PWCupClosed A θ u d hu hW P := h

/-- Full multiplicativity of cycle classes implies multiplicativity restricted to the PW algebra. -/
theorem papw_PWCupClosed_of_hC9 (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) (hC9 : CycleClassMultiplicative (cupProductOf Y)) :
    papw_PWCupClosed A θ u d hu hW P := by
  intro p q h a b ha _ hb _
  exact hC9.mem h a b ha hb

end HodgeLean.Papers
