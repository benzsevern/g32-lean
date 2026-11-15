import HodgeLean.Foundations.Program.CycleFoundationsDefs
import HodgeLean.Foundations.Program.CycleFoundationsIntegration
import HodgeLean.Foundations.Program.CycleFoundationsCoordinates
import HodgeLean.Foundations.Program.CycleFoundationsProjectionEvaluation
import HodgeLean.Foundations.Program.CycleFoundationsProjectionSpan
import HodgeLean.Foundations.Program.CycleFoundationsFiniteCohomology
import HodgeLean.Adapters.KleimanProduct
import HodgeLean.Foundations.Program.CompensationAssemblyPullback

/-! Proof obligations for the cycle foundation stage. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] cupProductOf algebraicCycleClassSpan homPullback
namespace HodgeLean.Foundations.Program
theorem cfd_projection_span_aux (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (s q : ℕ) (h : 2 * s = 2 * q + 2 * d)
    (x : HQ (A ⊗ B) (2 * s)) (hx : x ∈ cfd_cycleSpan (A ⊗ B) s) :
    cfd_projection A B d I (2 * q) (HQ.castEquiv (A ⊗ B) h x) ∈
      cfd_cycleSpan A q := by
  exact cfd_projection_span_map_le A B d s q hB I h
    (Submodule.mem_map_of_mem hx)

theorem cfd_correspondence_span_aux (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (c p q : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (ξ : HQ (A ⊗ B) (2 * c)) (hξ : ξ ∈ cfd_cycleSpan (A ⊗ B) c)
    (x : HQ B (2 * p)) (hx : x ∈ cfd_cycleSpan B p) :
    cfd_corrAction A B d I c p q h ξ x ∈ cfd_cycleSpan A q := by
  letI : Smooth (snd A B).left := by
    change Smooth (Limits.pullback.snd A.hom B.hom)
    infer_instance
  have hpb : homPullback (snd A B) (2 * p) x ∈ cfd_cycleSpan (A ⊗ B) p :=
    cq_smooth_pullback_span_core (snd A B) p (Submodule.mem_map_of_mem hx)
  have hm := hc9k_cycleClassMultiplicative (A ⊗ B)
  have hc : (cupProductOf (A ⊗ B)).cup
      (show 2 * c + 2 * p = 2 * (c + p) by omega)
      ξ (homPullback (snd A B) (2 * p) x) ∈ cfd_cycleSpan (A ⊗ B) (c + p) := by
    exact hm.mem _ _ _ hξ hpb
  have ht := cfd_projection_span_aux A B d hB I (c + p) q
    (by omega) _ hc
  simpa only [cfd_corrAction, LinearMap.comp_apply, CupProduct.castEquiv_cup] using ht

end HodgeLean.Foundations.Program
