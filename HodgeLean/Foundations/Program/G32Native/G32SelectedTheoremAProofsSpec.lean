import HodgeLean.Foundations.Program.SelectedCodifferential
import HodgeLean.Foundations.Program.G32Native.G32SelectedProp46Spec
import HodgeLean.Foundations.Program.RoucheRootCount
import HodgeLean.Foundations.Program.UniversalFamilyCover
import HodgeLean.Papers.QuasiInverseDerive

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


theorem g32a_theoremA_selected_aux_spec (A : Over (Spec ↧ℂ))
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
    ∀ (hS : ∀ t, g32p_SchoenSupplier (X t))
      (hM : ∀ t, g32p_MilneInvariance (X t).J (X t).pol
        (X t).pol_nondeg (X t).pol_pos)
    (hComparison : ∃ (S : Fin 51 → g32p_Supplier) (χc : ∀ i, (S i).H →* ℂˣ)
      (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G),
      (∀ j, Simple (τ j) ∧ Simple (τbar j) ∧ ¬ g32p_SelfDual (τ j) ∧
        (∀ g, (τbar j).character g = star ((τ j).character g)) ∧ 0 < g32p_cwMult (τ j)) ∧
      (∀ j, Simple (θ j) ∧ g32p_Quaternionic (θ j) ∧ 0 < g32p_cwMult (θ j)) ∧
      (∀ j k, j ≠ k → IsEmpty (τ j ≅ τ k) ∧ IsEmpty (τ j ≅ τbar k)) ∧
      (∀ j k : Fin 4, j ≠ k → IsEmpty (θ j ≅ θ k)) ∧
      Nonempty (τ 2 ≅ g32p_rho) ∧
      (∀ σ : FDRep ℂ g32p_G, Simple σ → 0 < g32p_cwMult σ →
        (¬ g32p_SelfDual σ → ∃ j, Nonempty (σ ≅ τ j) ∨ Nonempty (σ ≅ τbar j)) ∧
        (g32p_Quaternionic σ → ∃ j, Nonempty (σ ≅ θ j))) ∧
      ∀ i : Fin 51,
        (∀ h, ((χc i h : ℂˣ) : ℂ) =
          g32p_root (S i).m ^ (Multiplicative.toAdd ((S i).χ h)).val) ∧
        (∃ r ∈ g32WitnessTable, r.i = i.val + 1 ∧ r.m = (S i).m ∧
          r.orderH = Nat.card (S i).H ∧ (g32p_exponents (S i)).Perm (expandExps r.exps)) ∧
        ∃ v ∈ g32VectorTable, v.i = i.val + 1 ∧
          papersA τ τbar θ (S i).H (χc i) = g32SparseVec v.coords),
    G32TheoremAStatement A W pol := by
  intro f p hp g hg D B X hS hM hComparison
  let O := Classical.choice (b65p_outputs p hp)
  let hLocal := (b65z_prym_family (b65z_centre p) g hg.1 D).2 B
  let P := Classical.choose hLocal
  have hP : b65z_IsLocalPrym D B P := Classical.choose_spec hLocal
  let F := Classical.choose b60c_family
  have hF : F.univ = b60b_univ := Classical.choose_spec b60c_family
  exact b65z_theoremA_of_qinv_codiff p O hp B P hP F hF
    (g32h46_prop46_spec D hg.1 B P hP hS hM hComparison)
    qderiv_qinv_premise A W pol

end HodgeLean.Foundations.Program
