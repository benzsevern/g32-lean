import HodgeLean.Foundations.Program.G32Native.PairedC3RetainedLastBlowupNumerical
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedUnionGeometry
import HodgeLean.Foundations.Program.G32Native.PairedC3RetainedLciNumerical
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateNormalization
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedMarkedRuling
import HodgeLean.Foundations.Program.G32Native.PairedC3RulingIdealTransport
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedLastLciComparison
import HodgeLean.Foundations.Program.G32Native.PairedC3PenultimateFrameWitness
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNComponentNoncontainment
import HodgeLean.Foundations.Program.G32Native.PairedC3RulingPointWitness
noncomputable section
set_option maxRecDepth 4000
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
namespace ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24
attribute [local instance] G32JointComponent.h_T20_slice_immersion
attribute [local instance] G32JointComponent.hQ

/-- The selected C3 geometry supplies the numerical functional.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem jointSelected_numerical_of_c3
    (hNormalField : by_elab return (← Lean.getConstInfo
      ``HodgeLean.Foundations.BundleThom.joint_projective_selfRestriction_eq_bundleEuler).type.bindingDomain!)
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (hr : 0 < R.r) :
    ∃ degree : Cohomology ℚ (TopCat.of (ComplexPoint P.C.Q)) (2 * R.P.k) →ₗ[ℚ] ℚ,
      degree (s2e_normalEuler P.C.ι R.P.k P.c) ≠ 0 := by
  let i : Fin R.r := ⟨R.r - 1, by omega⟩
  have hi : i.val + 1 = R.r := by dsimp [i]; omega
  obtain ⟨e₀⟩ := G32Native.paired_c3_penultimate_frame_witness R P i hi
  obtain ⟨σ, p, sq, hframes, hn, restriction, g, hsm, sq₂⟩ :=
    paired_c3_selected_final_union_geometry R P i hi
  let I := (P.C.slices i.castSucc).left.ker.comap σ
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let M := K.comap σ ⊔ I
  letI := P.C.sliceImmersion i.castSucc
  obtain ⟨C, hdimC, c₀, hc₀, g', hsm', sq₂'⟩ :=
    G32Native.paired_ruling_point_witness P.C.ℓ M g hsm sq₂
  letI := hdimC
  letI := hc₀
  letI := hsm'
  exact jointSelected_numerical_of_retained_lci_frames hNormalField R P M hn
    (P.C.slices i.castSucc).left σ p sq hframes e₀ C c₀ g' sq₂'
    (P.C.residue.indices i) restriction

#print axioms jointSelected_numerical_of_c3
end ResidueSelected
end HodgeLean.Foundations.Program
