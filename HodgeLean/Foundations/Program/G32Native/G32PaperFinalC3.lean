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


/-- Selected Theorem A with the selected C3 numerical construction. -/
theorem g32_c3_final_theoremA (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) :
    G32TheoremAStatement A W pol := by
  apply ResidueSelected.g32a_theoremA_selected_remaining_geometric_inputs A W pol
  exact ResidueSelected.jointRemainingInputs_of_c3 _ _ _

#print axioms g32_c3_final_theoremA

/-- Theorem B with the selected C3 numerical construction. -/
theorem g32_c3_final_theoremB (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    {L : Type*} [Field L] [Algebra ℚ L]
    {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
    [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ} (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (P : AbelianPowerData A Y r) :
    ∀ q : ℕ, Hdg^q(Y; ℚ) ≤ algebraicCycleClassSpan Y q := by
  exact cupw_papw_skelg32_theoremB A θ u hu hL pol hη hRos hGk hM
    (g32_c3_final_theoremA A (f1_weilAction A θ u 3 hu) pol) P
    (ccm6_hPull P θ)

#print axioms g32_c3_final_theoremB

/-- Corollary 8.2 first clause with the selected C3 construction. -/
theorem g32_c3_final_corollary82_first (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (pol : HQ A 2) (Q : G32Native.TypeIIISixfoldData A pol)
    (hdisc : (Q.discriminantUnit : ℚˣ ⧸ HodgeLean.Foundations.HermitianForm.normSubgroup (QuadraticAlgebra ℚ (-3) 0)) =
      classNegTwo) :
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
        (G32Native.typeIIIWeilAction Q)
        (G32Native.typeIII_member_of_discriminant Q hdisc).isWeilType := by
  exact g32_c3_final_theoremA A (G32Native.typeIIIWeilAction Q) pol
    (G32Native.typeIII_member_of_discriminant Q hdisc)

#print axioms g32_c3_final_corollary82_first

open TypeIIIPaper in
/-- Corollary 8.2 powers with the selected C3 construction. -/
theorem g32_c3_final_corollary82_second (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2)
    (hMember : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)
    (P : GeneralPELMember A W pol hMember)
    (hPowers : ∀ (P : GeneralPELMember A W pol hMember),
      (∀ x : HQ A (2 * 3), x ∈ quaternionicSpan A (weilSix A W pol hMember) →
        x ∈ algebraicCycleClassSpan A 3) →
      ∀ (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
        [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
        (r : ℕ), 0 < r → AbelianPowerData A Y r →
        ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p) :
    ∀ (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
      [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
      (r : ℕ), 0 < r → AbelianPowerData A Y r →
      ∀ q : ℕ, Hdg^q(Y; ℚ) ≤ algebraicCycleClassSpan Y q := by
  intro Y _ _ _ _ _ r hr power
  exact TypeIIIPaper.powers_of_weil_algebraic A W pol hMember P hPowers
    (g32_c3_final_theoremA A W pol hMember) Y r hr power

#print axioms g32_c3_final_corollary82_second
end HodgeLean.Foundations.Program
