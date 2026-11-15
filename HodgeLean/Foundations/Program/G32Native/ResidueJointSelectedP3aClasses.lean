import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedOrientedPositiveData
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedP3aGeometry
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedPrefixChecks
import HodgeLean.Foundations.Program.G32Native.JointSelectedPositiveData
import HodgeLean.Foundations.Program.G32Native.JointSelectedBasis

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
  G32JointPositiveData.integralW G32JointPositiveData.projectiveW

attribute [local instance] G32JointOrientedPositiveData.integralW G32JointOrientedPositiveData.projectiveW
open HodgeLean.Foundations.QuotientDuality

/-- Supply the literal T22–T23 class rows from the retained orientations and T13 basis. -/
theorem jointSelectedP3aClasses
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (V : G32JointBasis R P.T P.W P.eFinal P.f P.A.toG32JointTracePackage
      P.C.toG32JointComponent P.c) :
    ∀ j,
      let cyc := s2e_rationalOrbitCycle P.C.ι
        (P.eFinal.inv ≫ P.T.d (Fin.last R.r) ≫ P.eFinal.hom) S.m (V.coeffs j)
      (∀ x ∈ cyc.support, Order.coheight x = R.P.k) ∧
      (∀ x ∈ (a1p_pushforward (P.eFinal.inv ≫ P.f (Fin.last R.r)).left cyc).support,
        Order.coheight x = R.P.k) ∧
      ∃ cr, a3b4_IsCycleClass P.W.hom cyc R.P.k cr ∧
      ∃ c₀, a3b4_IsCycleClass R.W₀.hom
        (a1p_pushforward (P.eFinal.inv ≫ P.f (Fin.last R.r)).left cyc) R.P.k c₀ ∧
        P.A.G (s2e_classToAbsolute P.W cyc R.P.k cr) = V.v j ∧
        s2e_classToAbsolute R.W₀
          (a1p_pushforward (P.eFinal.inv ≫ P.f (Fin.last R.r)).left cyc) R.P.k c₀ = V.v j := by
  letI := P.C.hQ
  letI := P.integralW
  letI := P.projectiveW
  letI := P.C.h_T20_component_immersion
  letI : IsProper ((P.eFinal.inv ≫ P.f (Fin.last R.r)).left ≫ R.W₀.hom) := by
    rw [Over.w]
    infer_instance
  letI : IsProper (P.eFinal.inv ≫ P.f (Fin.last R.r)).left :=
    IsProper.of_comp _ R.W₀.hom
  obtain ⟨hdim, hdim₀, ⟨U, hU, hsm⟩, hcodim, hdegree⟩ :=
    jointSelectedP3aGeometry R P.T P.W P.eFinal P.f P.hf P.C
  have hp : Function.Bijective (properCyclePairing (a3b4_an P.W.hom) R.P.k P.A.cW) := by
    change Function.Bijective (s2e_middlePairing _ R.P.k
      (orientationIntegral _ (2*(2*R.P.k)) P.A.cW))
    rw [← P.A.trace_final]
    exact P.A.h_T15_final
  have hp₀ : Function.Bijective (properCyclePairing (a3b4_an R.W₀.hom) R.P.k P.A.c₀) := by
    change Function.Bijective (s2e_middlePairing _ R.P.k
      (orientationIntegral _ (2*(2*R.P.k)) P.A.c₀))
    rw [← P.A.trace_initial]
    exact P.A.h_T15_initial
  apply G32Native.selected_tower_p3a_classes aut S R.P P.eFinal
    (P.T.d (Fin.last R.r)) (P.f (Fin.last R.r)) (P.T.horder (Fin.last R.r))
    P.C.ι U hU hsm hcodim hdegree hdim hdim₀
    P.A.o P.A.cW P.A.ho P.A.hchart hp.1
    P.A.o₀ P.A.c₀ P.A.ho₀ P.A.hchart₀ hp₀ P.A.G
    ?_ P.c P.hc V.coeffs V.v V.hinverse
  intro x u
  change s2e_middlePairing _ R.P.k (orientationIntegral _ _ P.A.c₀) (P.A.G x) u =
    s2e_middlePairing _ R.P.k (orientationIntegral _ _ P.A.cW) x _
  rw [← P.A.trace_initial, ← P.A.trace_final]
  exact P.A.h_T18_adjoint x u

#print axioms jointSelectedP3aClasses
end ResidueSelected
end HodgeLean.Foundations.Program
