import HodgeLean.Foundations.Program.CompensationAssemblyCrossExt
import HodgeLean.Foundations.Program.CompensationAssemblySurfaceWeights

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

variable (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cq_cross_singular_product_cast (i j m : ℕ) (h : i + j = m)
    (a : HQ A i) (b : HQ Y j) :
    cohomologyHomeomorphEquiv (HodgeLean.Foundations.complexPointProdHomeomorph A Y) m
      (cupComparison (A ⊗ Y) m (HQ.castEquiv (A ⊗ Y) h (cq_cross A Y i j a b))) =
      cup (TopCat.of (ComplexPoint A × ComplexPoint Y)) h
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) (cupComparison A i a))
        (cohomologyMap ℚ j (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (cupComparison Y j b)) := by
  subst m
  simpa only [HQ.castEquiv_apply_self] using cq_cross_singular_product A Y i j a b

theorem cq_surfaceProjection_cross_ne
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (i j n : ℕ) (hij : i + j = n + 4) (hi : i ≠ n)
    (a : HQ A i) (b : HQ Y j) :
    cq_surfaceProjection A Y hY I n
      (HQ.castEquiv (A ⊗ Y) hij (cq_cross A Y i j a b)) = 0 := by
  simp only [cq_surfaceProjection, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [cq_cross_singular_product_cast,
    cq_surfaceTrace_cross_ne A Y hY I i j n hij hi]
  exact (cupComparison A n).symm.toLinearMap.map_zero

theorem cq_projectionMap_eq_surfaceProjection
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1)
    (heA : ∀ a, e (a, 0) = homPullback (fst A Y) 1 a)
    (heY : ∀ b, e (0, b) = homPullback (snd A Y) 1 b) :
    cq_projectionMap A Y I e = cq_surfaceProjection A Y hY I 6 := by
  apply cq_cross_linear_ext A Y 10
  intro i j hij a b
  by_cases hj : j = 4
  · subst j
    have hi : i = 6 := by omega
    subst i
    rw [HQ.castEquiv_apply_self, cq_projectionMap_cross A Y I e heA heY,
      cq_surfaceProjection_cross]
  · rw [cq_projectionMap_cross_ne A Y I e heA heY i j hij hj]
    exact (cq_surfaceProjection_cross_ne A Y hY I i j 6 hij (by omega) a b).symm

end HodgeLean.Foundations.Program
