import HodgeLean.Foundations.Program.SchoenTransferJ12CurveIdentityDivisor
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveAlgebraicIsomorphism

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- A curve identification in H1 supplies an algebraic divisor inducing the actual identity operator. -/
theorem s4_selected_curve_identity_divisor_of_bijective
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (f : Y ⟶ A) (hf : Function.Bijective (homPullback f 1))
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) :
    ∃ q : HQ A 2, q ∈ cfd_cycleSpan A 1 ∧
      s4_selected_curve_divisor_operator A Y f I q = LinearMap.id := by
  obtain ⟨p, hp⟩ := m1_exists_positive_polarization A
  have halg : p ∈ cfd_cycleSpan A 1 := by
    unfold cfd_cycleSpan
    exact chowG_lefschetzOneOne_abelian A (p1_mem_hdg A hp)
  have hbij := s4_selected_curve_mixed_action_bijective A Y hdim f hf I
    (polarizationVec (torusCohomology_cupProductOf A) p) (p1_isNondegenerate A hp)
  rw [cupWedgeMap_polarizationVec] at hbij
  apply s4_selected_curve_identity_divisor_of_injective_operator A Y hdim f I p halg
  exact hbij.injective.comp hf.injective

#print axioms s4_selected_curve_identity_divisor_of_bijective
end HodgeLean.Foundations.Program
