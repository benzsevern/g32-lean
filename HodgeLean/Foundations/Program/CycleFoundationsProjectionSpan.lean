import HodgeLean.Foundations.Program.CycleFoundationsProjectionSupport

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

variable (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cfd_projection_prime_mem
    (d s q : ℕ) (hY : TopologicalSpace.dim Y.left = d)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (h : 2 * s = 2 * q + 2 * d)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s) :
    cfd_projection A Y d I (2 * q)
      (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx)) ∈
      cfd_cycleSpan A q := by
  classical
  rw [cfd_projection_eq_traceProjection A Y d hY I (2 * q)]
  by_cases himage : Order.coheight ((fst A Y).left x) = q
  · obtain ⟨r, hr⟩ := cfd_traceProjection_prime_multiple A Y d s q hY I h x hx himage
    rw [hr]
    refine Submodule.smul_mem _ r ?_
    change cycleComponentSheafClass A ((fst A Y).left x) himage ∈ algebraicCycleClassSpan A q
    have hle : Submodule.span ℚ ({cycleComponentSheafClass A ((fst A Y).left x) himage} :
        Set (HQ A (2 * q))) ≤ algebraicCycleClassSpan A q := by
      unfold algebraicCycleClassSpan
      exact le_sSup ⟨(fst A Y).left x, himage, rfl⟩
    exact hle (Submodule.subset_span (Set.mem_singleton _))
  · rw [cfd_traceProjection_prime_zero A Y d s q hY I h x hx himage]
    exact Submodule.zero_mem _

theorem cfd_projection_span_map_le
    (d s q : ℕ) (hY : TopologicalSpace.dim Y.left = d)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (h : 2 * s = 2 * q + 2 * d) :
    (cfd_cycleSpan (A ⊗ Y) s).map
        ((cfd_projection A Y d I (2 * q)).comp (HQ.castEquiv (A ⊗ Y) h).toLinearMap) ≤
      cfd_cycleSpan A q := by
  apply Submodule.map_le_iff_le_comap.mpr
  change algebraicCycleClassSpan (A ⊗ Y) s ≤ _
  rw [algebraicCycleClassSpan]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  exact cfd_projection_prime_mem A Y d s q hY I h x hx

end HodgeLean.Foundations.Program
