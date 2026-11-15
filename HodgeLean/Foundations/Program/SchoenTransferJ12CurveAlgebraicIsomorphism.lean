import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedInvertible
import HodgeLean.Foundations.Program.MilneFactorsHodgeSemisimple
import HodgeLean.Foundations.ChowProjective

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection cfd_cycleSpan

/-- A degree-one curve identification has an algebraic divisor whose action is an isomorphism. -/
theorem s4_selected_curve_algebraic_isomorphism
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (f : Y ⟶ A) (hf : Function.Bijective (homPullback f 1))
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) :
    ∃ κ : HQ (A ⊗ Y) 2, κ ∈ cfd_cycleSpan (A ⊗ Y) 1 ∧
      Function.Bijective (s4_selected_corr_action A Y 1 I 1 1 1 (by norm_num) κ) := by
  obtain ⟨pol, hP⟩ := m1_exists_positive_polarization A
  have hpol : pol ∈ cfd_cycleSpan A 1 := by
    unfold cfd_cycleSpan
    exact chowG_lefschetzOneOne_abelian A (p1_mem_hdg A hP)
  have hbij := s4_selected_curve_mixed_action_bijective A Y hdim f hf I
    (polarizationVec (torusCohomology_cupProductOf A) pol) (p1_isNondegenerate A hP)
  rw [cupWedgeMap_polarizationVec] at hbij
  exact ⟨s4_selected_curve_mixed_divisor A Y f pol,
    s4_selected_curve_mixed_divisor_mem A Y hdim f pol hpol, hbij⟩

#print axioms s4_selected_curve_algebraic_isomorphism
end HodgeLean.Foundations.Program
