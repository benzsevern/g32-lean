import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRestrictions
import HodgeLean.Foundations.Program.SchoenCycleC2TowerDimensionHelpers

/-! # The smooth dimension of the actual retained ambient tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24



/-- Every actual retained ambient stage is smooth of relative dimension 2k.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2;
Hartshorne, Algebraic Geometry, III.10. -/
theorem paired_c3_selected_ambient_relative_dimension
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin (R.r + 1)) :
    SmoothOfRelativeDimension (2 * R.P.k) (P.T.B i).hom := by
  have hdim := s2e_retained_tower_dimension R.Z R.B₀ R.hdimZ (R.h + 1) R.r
    R.γ R.hγsurj P.T.B P.T.e₀ P.T.b P.T.D P.T.hcartier P.T.hblowup i
  have h := (inferInstance : SmoothOfRelativeDimension
    (TopologicalSpace.dim (P.T.B i).left) (P.T.B i).hom)
  simpa only [hdim, R.hselected] using h

#print axioms paired_c3_selected_ambient_relative_dimension
end HodgeLean.Foundations.Program.ResidueSelected
