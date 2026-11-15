import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedP3aClasses
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedZeroSignedProjective
import HodgeLean.Foundations.Program.G32Native.JointZeroPairNative
import HodgeLean.Foundations.Program.G32Native.JointPositivePairExports
import HodgeLean.Foundations.Program.G32Native.SelectedAlternativeBoundarySelected

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Papers HodgeLean.Foundations
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
namespace ResidueSelected
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

attribute [local instance] G32JointOrientedPositiveData.integralW G32JointOrientedPositiveData.projectiveW

/-- Supply both alternatives for every admissible supplier of the migrated cover. -/
theorem jointSelected_remaining_hS {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c)))
    (I : G32RemainingGeometricInputs D hg B) :
    let X := fun t : b6t_polydisc c => Classical.choose (g32y_cover_spec D t hg B)
    ∀ t, g32p_SchoenSupplier (X t) := by
  apply selectedAlternative_hS D hg B
  · intro t S hA hEmpty
    let R := Classical.choose (jointSelectedPrefix_spec D t hg B S hA)
    obtain ⟨U⟩ := jointSelectedZeroGeometry_exists R hEmpty
    obtain ⟨cls, hc⟩ := jointSelectedZeroClass_exists R U
    have hSigned := jointSelectedZeroSigned_projective D hg B I R U cls hc
    exact jointZeroPairNative_of_signed R hA hEmpty U cls hc hSigned
  · intro t S hA hNe
    let R := Classical.choose (jointSelectedPrefix_spec D t hg B S hA)
    let P := jointSelectedOrientedPositiveData (@g32l4_paired_blowup_regularity_aux) R hNe
    have hnum := I.paired_self_intersection t S hA hNe
    let degree := Classical.choose hnum
    have hdegree := Classical.choose_spec hnum
    let V := Classical.choice (jointSelectedBasis_exists R P.T P.W P.eFinal P.f P.A.toG32JointTracePackage P.C.toG32JointComponent P.c
      P.hf P.hc degree hdegree)
    obtain ⟨E⟩ := jointPositivePairExports_of_data R P.T P.W P.eFinal P.f P.A.toG32JointTracePackage P.C.toG32JointComponent P.c
      V P.hf (jointSelectedP3aClasses R P V)
    exact g32t14_positive_native (Classical.choose (g32y_cover_spec D t hg B)).J
      (Classical.choose (g32y_cover_spec D t hg B)).aut S hA hNe E

#print axioms jointSelected_remaining_hS
end ResidueSelected
end HodgeLean.Foundations.Program
