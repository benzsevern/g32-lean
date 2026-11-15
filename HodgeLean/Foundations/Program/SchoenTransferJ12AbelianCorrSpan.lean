import HodgeLean.Foundations.Program.SchoenTransferJ12CorrespondenceAction
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionSpan
import HodgeLean.Foundations.Program.CompensationAssemblyPullback
import HodgeLean.Adapters.KleimanProduct

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The specified correspondence action preserves cycle spans when its two actual factors are abelian.
Source: abelian cycle-class multiplication, smooth projection pullback and proper fibre projection. -/
theorem s4_selected_abelian_corr_span
    (A B : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (c p q : ℕ) (h : 2 * c + 2 * p = 2 * d + 2 * q)
    (ξ : HQ (A ⊗ B) (2 * c)) (hξ : ξ ∈ cfd_cycleSpan (A ⊗ B) c)
    (x : HQ B (2 * p)) (hx : x ∈ cfd_cycleSpan B p) :
    s4_selected_corr_action A B d I c (2 * p) (2 * q) h ξ x ∈ cfd_cycleSpan A q := by
  letI : Smooth (snd A B).left := by
    change Smooth (CategoryTheory.Limits.pullback.snd A.hom B.hom)
    infer_instance
  have hpb := cq_smooth_pullback_span_core (snd A B) p (Submodule.mem_map_of_mem hx)
  have hc : (cupProductOf (A ⊗ B)).cup (by omega : 2 * c + 2 * p = 2 * (c + p))
      ξ (homPullback (snd A B) (2 * p) x) ∈ cfd_cycleSpan (A ⊗ B) (c + p) := by
    change _ ∈ algebraicCycleClassSpan (A ⊗ B) (c + p)
    exact (hc9k_cycleClassMultiplicative (A ⊗ B)).mem_of_eq (p := c) (q := p) (r := c + p)
      (by omega) _ _ hξ hpb
  have hp := s4_selected_projection_span A B d (c + p) q hB I
    (by omega : 2 * (c + p) = 2 * d + 2 * q) (Submodule.mem_map_of_mem hc)
  simpa only [s4_selected_corr_action, LinearMap.comp_apply, LinearEquiv.coe_coe,
    CupProduct.castEquiv_cup] using hp

#print axioms s4_selected_abelian_corr_span
end HodgeLean.Foundations.Program
