import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedRemainingSupplier
import HodgeLean.Foundations.Program.G32Native.G32SelectedTheoremASchoenSpec

noncomputable section
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program
namespace ResidueSelected
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected



theorem g32a_theoremA_selected_remaining_geometric_inputs (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) :
    let f := fun k : Fin 12 ↦ Classical.choose (rou_b65b_isolating_boxes k)
    let p := Function.extend b65b_boxIndex f 0
    let hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0 := by
        intro k
        have hinj : Function.Injective b65b_boxIndex := by decide
        dsimp only [p]
        rw [hinj.extend_apply]
        exact (Classical.choose_spec (rou_b65b_isolating_boxes k)).1
    let g := Classical.choose (b65z_schlesinger_identification p hp)
    let hg := Classical.choose_spec (b65z_schlesinger_identification p hp)
    let D := Classical.choose hg.2
    let B := Classical.choice (b65z_prym_family (b65z_centre p) g hg.1 D).1
    ∀ (I : G32RemainingGeometricInputs D hg.1 B), G32TheoremAStatement A W pol := by
  intro f p hp g hg D B I
  exact g32a_theoremA_selected_schoen_spec A W pol
    (jointSelected_remaining_hS D hg.1 B I)

end ResidueSelected
end HodgeLean.Foundations.Program
