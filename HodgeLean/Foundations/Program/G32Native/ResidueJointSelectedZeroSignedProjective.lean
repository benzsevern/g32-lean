import HodgeLean.Foundations.Program.G32Native.ResidueJointRemainingGeometricInputs
import HodgeLean.Foundations.Program.G32Native.CanonicalNormalEulerComparison
import HodgeLean.Foundations.Program.G32Native.JointSelectedZeroClass
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelProducer
import HodgeLean.Foundations.Program.G32Native.CanonicalSignedEuler

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Bundle
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.BundleThom
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


attribute [local instance] G32JointZeroGeometry.integralQ
  G32JointZeroGeometry.projectiveQ G32JointZeroGeometry.smoothQ

/-- Combine U10 and Thom transport with projective normal germs on the actual component. -/
theorem jointSelectedZeroSigned_projective {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c)))
    (I : G32RemainingGeometricInputs D hg B)
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (U : G32JointZeroGeometry R)
    (cls : s2e_supportedClass R.W₀ (s2e_componentCycle U.ι ℚ) R.P.k)
    (hc : a3b4_IsCycleClass R.W₀.hom (s2e_componentCycle U.ι ℚ) R.P.k cls) :
    ∃ hH : (IsIntegral
      (s2c_subscheme U.Q ((s2e_hyperplaneIdeal R.P.k).comap U.eQ.hom.left)).left),
      letI := hH
      ∃ cH : (s2e_supportedClass U.Q
      (s2e_componentCycle (s2c_subschemeι U.Q ((s2e_hyperplaneIdeal R.P.k).comap U.eQ.hom.left)) ℚ) 1), (a3b4_IsCycleClass U.Q.hom
      (s2e_componentCycle (s2c_subschemeι U.Q ((s2e_hyperplaneIdeal R.P.k).comap U.eQ.hom.left)) ℚ) 1 cH) ∧ (s2e_normalEuler U.ι R.P.k cls = (-1 : ℚ) ^ R.P.k •
      s2e_hyperplanePower (TopCat.of (ComplexPoint U.Q))
        (s2e_classToAbsolute U.Q (s2e_componentCycle (s2c_subschemeι U.Q
          ((s2e_hyperplaneIdeal R.P.k).comap U.eQ.hom.left)) ℚ) 1 cH) R.P.k) := by
  letI := U.smoothZ
  letI := U.smoothB
  letI := U.smoothW
  letI : Smooth U.Q.hom := SmoothOfRelativeDimension.smooth R.P.k U.Q.hom
  letI := U.immersion
  letI := U.immersionℓ
  letI := U.etale
  letI : SmoothOfRelativeDimension (R.P.k + R.P.k) ((𝟙 R.W₀.left) ≫ R.W₀.hom) := by
    simpa only [Category.id_comp] using U.smoothW
  let G := U.geometry
  letI : IsIntegral G.Q.left := U.integralQ
  letI : CompactSpace (ComplexPoint G.Q) := by
    change CompactSpace (ComplexPoint U.Q)
    infer_instance
  letI : T2Space (ComplexPoint G.Q) := by
    change T2Space (ComplexPoint U.Q)
    infer_instance
  let N := G32Native.canonicalNormalIdentification G
  let C : G32Native.CoefficientNormalIdentification G := {
    fibre := N.fibre
    continuous_forward := N.continuous_forward
    continuous_inverse := N.continuous_inverse }
  have hSelf := HodgeLean.Foundations.BundleThom.joint_projective_selfRestriction_eq_bundleEuler
    I.retained_euclidean_normal_field U.ι R.P.k cls hc
    R.W₀.left (𝟙 R.W₀.left) U.ι.left (Category.comp_id U.ι.left)
  have hSelf' : s2e_normalEuler U.ι R.P.k cls =
      i1_normalBundleEuler U.ι.left R.P.k R.W₀.hom (Over.w U.ι) := by
    simpa only [Category.id_comp] using hSelf
  have hComparison := G32Native.canonicalNormalEuler_comparison G C cls hSelf'
  exact G32Native.canonicalSignedEuler_selected R.P R.h R.hh R.hselected
    U.eQ U.ι cls hc hComparison

#print axioms jointSelectedZeroSigned_projective
end ResidueSelected
end HodgeLean.Foundations.Program
