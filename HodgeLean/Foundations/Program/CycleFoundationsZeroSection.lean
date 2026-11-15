import HodgeLean.Foundations.Program.CycleFoundationsShear
import HodgeLean.Foundations.Program.CycleFoundationsIntegration
import HodgeLean.Foundations.Program.CycleFoundationsProjectionEvaluation
import HodgeLean.Foundations.Program.CycleFoundationsProjectionSpan
import HodgeLean.Adapters.AbelianHomPullbackDegrees
import HodgeLean.Adapters.KleimanProduct
import HodgeLean.Foundations.Program.CompensationAssemblyPullback

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] cupProductOf algebraicCycleClassSpan homPullback
namespace HodgeLean.Foundations.Program

variable (A B : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]

theorem cfd_constant_pullback_positive (n : ℕ) (hn : n ≠ 0) :
    homPullback (1 : B ⟶ A) n = 0 := by
  have h := spec_homPullback_zpow_degree (1 : B ⟶ A) 0 n
  rw [zpow_zero, Int.cast_zero, zero_pow hn, zero_smul] at h
  exact h

theorem cfd_top_class (d : ℕ) (hA : TopologicalSpace.dim A.left = d)
    (I : HQ A (2 * d) ≃ₗ[ℚ] ℚ) :
    ∃ t : HQ A (2 * d), t ∈ cfd_cycleSpan A d ∧ I t = 1 := by
  classical
  letI : SmoothOfRelativeDimension d A.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (X := A.left) (f := A.hom)
    rwa [hA] at h
  letI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨x, _, hx⟩ := isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := A.left))
  have hxc : Order.coheight x = d :=
    SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed (f := A.hom) x hx
  let v : HQ A (2 * d) := cycleComponentSheafClass A x hxc
  obtain ⟨w, hw⟩ := j5c_exists_complexFundamentalClass A d
  have hv : v ≠ 0 := cycleComponentSheafClass_ne_zero_of_fundamentalClass A d x hxc w hw
  have hIv : I v ≠ 0 := fun h => hv (I.injective (h.trans I.map_zero.symm))
  have hmem : v ∈ cfd_cycleSpan A d := by
    change v ∈ algebraicCycleClassSpan A d
    have hle : Submodule.span ℚ ({cycleComponentSheafClass A x hxc} :
        Set (HQ A (2 * d))) ≤ algebraicCycleClassSpan A d := by
      unfold algebraicCycleClassSpan
      exact le_sSup ⟨x, hxc, rfl⟩
    exact hle (Submodule.subset_span (Set.mem_singleton _))
  refine ⟨(I v)⁻¹ • v, Submodule.smul_mem _ _ hmem, ?_⟩
  rw [I.map_smul]
  exact inv_mul_cancel₀ hIv

end HodgeLean.Foundations.Program
