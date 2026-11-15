import HodgeLean.Foundations.Program.SchoenTransferJ12CurveAbelFactorData
import HodgeLean.Foundations.AbelianQuotient.H1Helpers
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveBijectiveDivisor
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedRetractionData

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- Injective curve pullback supplies actual mixed divisor retraction data.
Source: actual Abel factorization, the identity divisor and the algebraized cross adjoint. -/
theorem s4_selected_curve_geometric_retraction_data
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (f : Y ⟶ A) (hf : Function.Injective (homPullback f 1))
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) :
    ∃ pol : HQ A 2, pol ∈ cfd_cycleSpan A 1 ∧
      ∃ g : Y ⟶ A, ∃ c : ℕ, 0 < c ∧
        ∀ v : HQ A 1,
          s4_selected_corr_action A Y 1 I 1 1 1 (by omega)
            (s4_selected_curve_mixed_divisor A Y g pol) (homPullback f 1 v) = (c : ℚ) • v := by
  obtain ⟨B, hGroup, hComm, hInt, hSmooth, hProjective,
    j, π, s, N, hj, hπ, hs, hN, hfac, hsec⟩ :=
      s4_selected_curve_abel_factor_data Y A hdim f hf
  letI := hGroup
  letI := hComm
  letI := hInt
  letI := hSmooth
  letI := hProjective
  letI := hs
  let BA : AbelianQuotient.Variety := ⟨B, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩
  let AA : AbelianQuotient.Variety := ⟨A, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩
  let πA : AbelianQuotient.Hom BA AA := ⟨π, hπ⟩
  let sA : AbelianQuotient.Hom AA BA := ⟨s, hs⟩
  have hsec' : sA.hom ≫ πA.hom = (AbelianQuotient.multiplication AA N).hom := by
    simpa only [AbelianQuotient.multiplication, Int.cast_natCast] using hsec
  have hH1 := AbelianQuotient.multiplication_section_pullback πA sA N hsec'
  obtain ⟨qB, hqB, hDqB⟩ := s4_selected_curve_identity_divisor_of_bijective B Y hdim j hj I
  exact s4_selected_curve_mixed_retraction_data A B Y hdim I f j π s N hN
    hfac hH1 qB hqB hDqB

#print axioms s4_selected_curve_geometric_retraction_data
end HodgeLean.Foundations.Program
