import HodgeLean.Adapters.AbelianPowerActualInstances
import HodgeLean.Foundations.Program.G32Native.G32PaperFinalC3Supplied
import HodgeLean.Foundations.Program.G32Native.G32PaperFinalC3
import HodgeLean.Papers.CupWiring
import HodgeLean.Adapters.CycleClassPullbackSpan
import HodgeLean.Foundations.Program.G32Native.TypeIIIRealizedLemma81
import HodgeLean.Foundations.Program.G32Native.TypeIIIPaperPowers
import HodgeLean.Foundations.Program.G32Native.ResidueJointRemainingInputsOfC3
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedRemainingTheoremA
noncomputable section
set_option linter.unusedVariables false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
attribute [local instance 100] LieRing.ofAssociativeRing
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.WeilPower
open AlgebraicTopology.Singular
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program
open TypeIIIPaper in
/-- Corollary 8.2 powers with the selected C3 construction. -/
theorem g32_final_corollary82_second_c3_supplied_actual (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2)
    (hMember : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)
    (P : GeneralPELMember A W pol hMember) :
    ∀ r : ℕ, 0 < r → ∀ q : ℕ,
      Hdg^q(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) q := by
  intro r hr
  exact g32_final_corollary82_second_c3_supplied A W pol hMember P
    (g3_power A r) r hr (g3_powerData A r)

#print axioms g32_final_corollary82_second_c3_supplied_actual

/-- Theorem B with the selected C3 numerical construction. -/
theorem g32_c3_final_theoremB_actual (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    {L : Type*} [Field L] [Algebra ℚ L]
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hM : letI := (finiteBetti_abelian A).finite 1
      IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
        (f1_weilAction A θ u 3 hu) pol)
    : ∀ r q : ℕ, Hdg^q(g3_power A r; ℚ) ≤
        algebraicCycleClassSpan (g3_power A r) q := by
  intro r
  exact g32_c3_final_theoremB A θ u hu hL pol hη hRos hGk hM (g3_powerData A r)

#print axioms g32_c3_final_theoremB_actual

end HodgeLean.Foundations.Program
