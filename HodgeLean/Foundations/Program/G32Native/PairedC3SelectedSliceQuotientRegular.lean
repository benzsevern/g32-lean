import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedNormalizationUnit
import HodgeLean.Foundations.Program.G32Native.PairedC3SliceQuotientRegular

/-! # Slice cancellation for the selected ruling overlaps -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

attribute [local instance] G32JointSlicedComponent.sliceImmersion

/-- Both chosen branch generators cancel on the original selected slice
quotient on every nonempty affine slice neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv,vi);
Hartshorne, Algebraic Geometry, II.3 and II.6. -/
theorem pairedC3_selected_slice_quotient_regular
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (U : (P.T.B i.castSucc).left.affineOpens)
    [Nonempty ((P.C.slices i.castSucc).left ⁻¹ᵁ U.1)]
    (u v : Γ((P.T.B i.castSucc).left, U))
    (hu : (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal U = Ideal.span {u})
    (hv : (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {v}) :
    IsRegular (Ideal.Quotient.mk ((P.C.slices i.castSucc).left.ker.ideal U) u) ∧
      IsRegular (Ideal.Quotient.mk ((P.C.slices i.castSucc).left.ker.ideal U) v) := by
  letI : IsIntegral (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i (by rfl)
  constructor
  · apply G32Native.pairedC3_slice_quotient_branch_regular
      (P.C.slices i.castSucc).left _ ?_ U u hu
    rw [hp.1]
    exact G32Native.paired_c3_residue_support_proper R.P.k (P.C.residue.indices i)
  · apply G32Native.pairedC3_slice_quotient_branch_regular
      (P.C.slices i.castSucc).left _ ?_ U v hv
    rw [hp.2]
    exact G32Native.paired_c3_residue_support_proper R.P.k (P.C.residue.indices i)

#print axioms pairedC3_selected_slice_quotient_regular
end HodgeLean.Foundations.Program.ResidueSelected
