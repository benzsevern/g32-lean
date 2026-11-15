import HodgeLean.Foundations.Program.G32Native.G32SelectedTheoremASchoenMilneSpec
import HodgeLean.Foundations.Program.MilneIntegration

noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected



theorem g32a_theoremA_selected_schoen_spec (A : Over (Spec ↧ℂ))
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
    let X := fun t : b6t_polydisc (b65z_centre p) ↦
      Classical.choose (g32y_cover_spec D t hg.1 B)
    ∀ (hS : ∀ t, g32p_SchoenSupplier (X t)), G32TheoremAStatement A W pol := by
  intro f p hp g hg D B X hS
  exact g32a_theoremA_selected_schoen_milne_spec A W pol hS
    (fun t => m3_milne_invariance (X t).J (X t).pol (X t).pol_nondeg (X t).pol_pos)

end HodgeLean.Foundations.Program
