import HodgeLean.Foundations.Abdulali.TypeIIIPowersAssembly
import HodgeLean.Foundations.Program.G32Native.G32PaperFinalC3
import HodgeLean.Papers.CupWiring
import HodgeLean.Adapters.CycleClassPullbackSpan
import HodgeLean.Foundations.Program.G32Native.TypeIIIRealizedLemma81
import HodgeLean.Foundations.Program.G32Native.TypeIIIPaperPowers
import HodgeLean.Foundations.Program.G32Native.ResidueJointRemainingInputsOfC3
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedRemainingTheoremA
noncomputable section
set_option linter.unusedVariables false
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
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful
  b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3
  G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7
  G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11
  G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15
  G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19
  G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27
  G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22
  G32JointBase.inst23 G32JointBase.inst24 G32JointComponent.hQ
  G32JointPositiveData.integralW G32JointPositiveData.projectiveW


open TypeIIIPaper in
/-- Corollary 8.2 powers with the selected C3 construction. -/
theorem g32_final_corollary82_second_c3_supplied (A : Over (Spec ↧ℂ))
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
    ∀ (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
      [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
      (r : ℕ), 0 < r → AbelianPowerData A Y r →
      ∀ q : ℕ, Hdg^q(Y; ℚ) ≤ algebraicCycleClassSpan Y q := by
  exact g32_c3_final_corollary82_second A W pol hMember P
    (HodgeLean.Foundations.Abdulali.typeIII_powers_assembly A W pol hMember)

#print axioms g32_final_corollary82_second_c3_supplied

end HodgeLean.Foundations.Program
