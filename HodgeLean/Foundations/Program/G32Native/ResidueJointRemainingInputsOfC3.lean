import HodgeLean.Foundations.Program.G32Native.ResidueJointRemainingGeometricInputs
import HodgeLean.Foundations.Program.G32Native.PairedC3NumericalAssembly
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanNormalField
open HodgeLean.Foundations.TubularEuler HodgeLean.Foundations.BundleThom
open scoped Manifold ContDiff

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Papers HodgeLean.Foundations
open scoped BigOperators TensorProduct CategoryTheory.MonObj
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
  G32JointComponent.h_T20_slice_immersion
  G32JointPositiveData.integralW G32JointPositiveData.projectiveW

attribute [local instance] G32JointOrientedPositiveData.integralW
  G32JointOrientedPositiveData.projectiveW

/-- The selected C3 construction supplies both remaining geometric fields.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Lee, Introduction to Smooth Manifolds, second edition, Theorem 6.24. -/
theorem jointRemainingInputs_of_c3
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) :
    G32RemainingGeometricInputs D hg B := by
  have hNormalField : by_elab return (← Lean.getConstInfo
      ``HodgeLean.Foundations.BundleThom.joint_projective_selfRestriction_eq_bundleEuler).type.bindingDomain! := by
    intro Q W hQ hQft hQqc hQs hWft hWqc hWs inc hi k V v hv j hjc hj hdimQ hdimV
    intro hD metric n emb hemb
    exact retained_euclidean_normal_field_aux inc k v j hj hD metric n emb hemb
  refine { retained_euclidean_normal_field := hNormalField, paired_self_intersection := ?_ }
  intro t S hA hNe
  let R := Classical.choose (jointSelectedPrefix_spec D t hg B S hA)
  let P := jointSelectedOrientedPositiveData (@g32l4_paired_blowup_regularity_aux) R hNe
  have hr : 0 < R.r := by
    have hc := Fintype.card_congr R.σ
    simp only [Fintype.card_fin] at hc
    have hn : 0 < (g32p_exponents S).length := List.length_pos_iff.mpr hNe
    omega
  exact jointSelected_numerical_of_c3 hNormalField R P hr

#print axioms jointRemainingInputs_of_c3
end ResidueSelected
end HodgeLean.Foundations.Program
