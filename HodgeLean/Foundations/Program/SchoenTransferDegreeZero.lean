import HodgeLean.Adapters.TorusCohomology
import HodgeLean.Foundations.Program.SchoenTransferDefs
import HodgeLean.Foundations.Program.CycleFoundations
import HodgeLean.Adapters.DegreeZeroUnconditional

/-! Algebraic correspondence retraction in degree zero and algebraicity at the top. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] cupProductOf homPullback algebraicCycleClassSpan
namespace HodgeLean.Foundations.Program

theorem s4_degree_zero_correspondence
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g : ℕ) (hdim : TopologicalSpace.dim A.left = g)
    (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ)
    (L : HQ A 0 →ₗ[ℚ] HQ A (2 * g)) (hL : Function.Injective L) :
    ∃ ξ : HQ (A ⊗ A) 0, ξ ∈ cfd_cycleSpan (A ⊗ A) 0 ∧
      ∀ x : HQ A 0, cfd_corrAction A A g I 0 g 0 (by omega) ξ (L x) = x := by
  let u := cupUnit A
  let c : ℚ := I (L u)
  have hu : u ≠ 0 := cupProductOf_unit_ne_zero A
  have hLu : L u ≠ 0 := fun h => hu (hL (h.trans L.map_zero.symm))
  have hc : c ≠ 0 := fun h => hLu (I.injective (h.trans I.map_zero.symm))
  let ξ := c⁻¹ • homPullback (fst A A) 0 u
  refine ⟨ξ, ?_, ?_⟩
  · change ξ ∈ algebraicCycleClassSpan (A ⊗ A) 0
    rw [algebraicCycleClassSpan_zero_eq_top_unconditional]
    trivial
  · have hunit : cfd_corrAction A A g I 0 g 0 (by omega) ξ (L u) = u := by
      change cfd_projection A A g I 0
        ((cupProductOf (A ⊗ A)).cup rfl
          (c⁻¹ • homPullback (fst A A) 0 u) (homPullback (snd A A) (2 * g) (L u))) = u
      rw [map_smul, LinearMap.smul_apply, map_smul,
        cfd_projection_cross A A g hdim I 0 u (L u)]
      change c⁻¹ • (c • u) = u
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    intro x
    obtain ⟨r, hr⟩ := (cupProductOf_zeroEquiv A).surjective x
    change r • u = x at hr
    rw [← hr, L.map_smul, map_smul, hunit]

theorem s4_inverse_lefschetz_zero
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g : ℕ) (hdim : TopologicalSpace.dim A.left = g)
    (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ) (pol : HQ A 2)
    (hη : HodgeLean.Foundations.Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf A) pol)) :
    ∃ ξ : HQ (A ⊗ A) 0, ξ ∈ cfd_cycleSpan (A ⊗ A) 0 ∧
      ∀ x : HQ A 0, cfd_corrAction A A g I 0 g 0 (by omega) ξ
        (lefschetzPow A (cupProductOf A) pol g (by omega) x) = x := by
  have hL := (hardLefschetz_abelian A hη).bijective
    (k := 0) (m := 2 * g) (by omega) (by omega)
  have hinj : Function.Injective
      (lefschetzPow A (cupProductOf A) pol g (show 0 + 2 * g = 2 * g by omega)) := by
    simpa only [hdim, Nat.sub_zero] using hL.1
  exact s4_degree_zero_correspondence A g hdim I _ hinj


theorem s4_top_degree_mem_cycleSpan
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (d : ℕ) (hdim : TopologicalSpace.dim A.left = d) (x : HQ A (2 * d)) :
    x ∈ cfd_cycleSpan A d := by
  change x ∈ algebraicCycleClassSpan A d
  letI : SmoothOfRelativeDimension d A.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (X := A.left) (f := A.hom)
    rwa [hdim] at h
  letI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨z, _, hz⟩ := isClosed_univ.exists_closed_singleton
    (Set.univ_nonempty (α := A.left))
  have hzc : Order.coheight z = d :=
    SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed (f := A.hom) z hz
  obtain ⟨w, hw⟩ := j5c_exists_complexFundamentalClass A d
  have hne := cycleComponentSheafClass_ne_zero_of_fundamentalClass A d z hzc w hw
  have hr := j5d_finrank_HQ_top complexPointsPreconnected A d
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero'
    (cycleComponentSheafClass A z hzc) hne).mp hr x
  apply Submodule.smul_mem _ c
  unfold algebraicCycleClassSpan
  apply le_sSup (s := {Submodule.span ℚ {cycleComponentSheafClass A y hy} |
    (y : A.left) (hy : Order.coheight y = d)})
  · exact ⟨z, hzc, rfl⟩
  · exact Submodule.subset_span (Set.mem_singleton _)

end HodgeLean.Foundations.Program
