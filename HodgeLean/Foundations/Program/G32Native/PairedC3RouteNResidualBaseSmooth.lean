import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRestrictions
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualBaseSmooth
import HodgeLean.Foundations.Program.G32Native.PairedC3QuotientRulingCharts

/-! # The actual normalized local maps for the selected ruling -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

attribute [local instance] G32JointSlicedComponent.sliceImmersion
open HodgeLean.Foundations.Program.G32Native



open AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual residual base at any retained step is smooth, using the
original reduced residue-hyperplane restriction.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv,vi);
Hartshorne, Algebraic Geometry, II.8. -/
theorem pairedC3_route_n_residual_base_smooth
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    Smooth ((K ⊔ (P.C.slices i.castSucc).left.ker).subschemeι ≫
      (P.T.B i.castSucc).hom) := by
  letI := P.C.sliceImmersion i.castSucc
  dsimp only
  apply pairedC3_residual_base_smooth R.P.k R.P.act.cyc_positive
    (P.C.slices i.castSucc) _ (P.C.residue.indices i)
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
  rw [Scheme.IdealSheafData.comap_sup, hp.1, hp.2, sup_idem]

#print axioms pairedC3_route_n_residual_base_smooth
end HodgeLean.Foundations.Program.ResidueSelected
