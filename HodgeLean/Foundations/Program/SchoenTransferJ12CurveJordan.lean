import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedDivisor
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionSpan
import HodgeLean.Adapters.KleimanProduct

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The fibre-integral Jordan operation on degree-two classes, with the two pure terms removed. -/
def s4_selected_curve_jordan
    (A Y : Over (Spec ↧ℂ)) [GrpObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (p q : HQ A 2) : HQ A 2 :=
  (2 : ℚ)⁻¹ •
    (s4_selected_projection A Y 1 2 I
      (homPullback (s4_selected_curve_add_map A Y f) 4 ((cupProductOf A).cup rfl p q)) -
      I (homPullback f 2 p) • q - I (homPullback f 2 q) • p)

/-- The fibre-integral Jordan operation preserves actual algebraic divisor classes. -/
theorem s4_selected_curve_jordan_mem
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ)
    (p q : HQ A 2) (hp : p ∈ cfd_cycleSpan A 1) (hq : q ∈ cfd_cycleSpan A 1) :
    s4_selected_curve_jordan A Y f I p q ∈ cfd_cycleSpan A 1 := by
  letI : Smooth (s4_selected_curve_add_map A Y f).left :=
    s4_selected_curve_add_smooth A Y f
  have hpq : (cupProductOf A).cup rfl p q ∈ cfd_cycleSpan A 2 :=
    (hc9k_cycleClassMultiplicative A).mem_of_eq (p := 1) (q := 1) (r := 2) rfl p q hp hq
  have hadd := cq_smooth_pullback_span_core (s4_selected_curve_add_map A Y f) 2
    (Submodule.mem_map_of_mem hpq)
  have hproj := s4_selected_projection_span A Y 1 2 1 hdim I (by norm_num)
    (Submodule.mem_map_of_mem hadd)
  change s4_selected_projection A Y 1 2 I
    (homPullback (s4_selected_curve_add_map A Y f) 4 ((cupProductOf A).cup rfl p q)) ∈
      cfd_cycleSpan A 1 at hproj
  exact Submodule.smul_mem _ _
    (Submodule.sub_mem _ (Submodule.sub_mem _ hproj (Submodule.smul_mem _ _ hq))
      (Submodule.smul_mem _ _ hp))

#print axioms s4_selected_curve_jordan_mem
end HodgeLean.Foundations.Program
