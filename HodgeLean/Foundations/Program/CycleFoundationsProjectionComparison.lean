import HodgeLean.Foundations.Program.CycleFoundationsProjectionEvaluation
import HodgeLean.Foundations.Program.CycleFoundationsTrace
import HodgeLean.Foundations.Program.CompensationAssemblyCrossExt
import HodgeLean.Foundations.Program.CompensationAssemblySurfaceComparison

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] cupProductOf homPullback
namespace HodgeLean.Foundations.Program

variable (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cfd_traceProjection_cross_off
    (d : ℕ) (hY : TopologicalSpace.dim Y.left = d) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (i j n : ℕ) (hij : i + j = n + 2 * d) (hi : i ≠ n)
    (a : HQ A i) (b : HQ Y j) :
    cfd_traceProjection A Y d hY I n
      (HQ.castEquiv (A ⊗ Y) hij (cq_cross A Y i j a b)) = 0 := by
  simp only [cfd_traceProjection, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [cq_cross_singular_product_cast,
    cfd_fibreTrace_cross_ne A Y d hY I i j n hij hi]
  exact (cupComparison A n).symm.toLinearMap.map_zero

theorem cfd_projection_eq_traceProjection
    (d : ℕ) (hY : TopologicalSpace.dim Y.left = d) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (n : ℕ) : cfd_projection A Y d I n = cfd_traceProjection A Y d hY I n := by
  apply cq_cross_linear_ext A Y (n + 2 * d)
  intro i j hij a b
  by_cases hj : j = 2 * d
  · subst j
    have hi : i = n := by omega
    subst i
    rw [HQ.castEquiv_apply_self, cfd_traceProjection_cross]
    exact cfd_projection_cross_evaluation A Y d hY I n a b
  · rw [cfd_traceProjection_cross_off A Y d hY I i j n hij (by omega)]
    have hc : HQ.castEquiv (A ⊗ Y) hij (cq_cross A Y i j a b) =
        (cupProductOf (A ⊗ Y)).cup hij
          (homPullback (fst A Y) i a) (homPullback (snd A Y) j b) := by
      unfold cq_cross
      exact CupProduct.castEquiv_cup _ rfl hij _ _
    rw [hc]
    exact cfd_projection_cross_off_evaluation A Y d I n i j hij hj a b

end HodgeLean.Foundations.Program
