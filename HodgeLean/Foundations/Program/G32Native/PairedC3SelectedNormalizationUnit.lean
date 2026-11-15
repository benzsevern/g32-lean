import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedOrientedPositiveData
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineNormalizationUnit
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRestrictions
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidueSupport
import HodgeLean.Adapters.IntersectionProductScaf

/-! # Normalization coefficients on the actual selected slice -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

attribute [local instance] G32JointSlicedComponent.sliceImmersion

/-- The two original branch equations in any selected affine neighbourhood
have a variable normalization coefficient invertible on the actual slice.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4;
Hartshorne, Algebraic Geometry, II.3 and II.6. -/
theorem pairedC3_selected_affine_normalization_unit
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (U : (P.T.B i.castSucc).left.affineOpens)
    [Nonempty ((P.C.slices i.castSucc).left ⁻¹ᵁ U.1)]
    (u v : Γ((P.T.B i.castSucc).left, U))
    (hu : (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal U = Ideal.span {u})
    (hv : (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {v}) :
    ∃ α : Γ((P.T.B i.castSucc).left, U),
      ((P.C.slices i.castSucc).left.app U.1).hom (v - α * u) = 0 ∧
        IsUnit (((P.C.slices i.castSucc).left.app U.1).hom α) ∧
        IsUnit (Ideal.Quotient.mk
          (((P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
            P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩) ⊔
            (P.C.slices i.castSucc).left.ker).ideal U) α) := by
  letI : IsIntegral (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i (by rfl)
  apply G32Native.pairedC3_affine_residual_normalization_unit
    (P.C.slices i.castSucc).left
    (P.T.D i.castSucc ⟨2 * i.val, by omega⟩)
    (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩)
    ((P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩) ⊔
      (P.C.slices i.castSucc).left.ker)
    (hp.1.trans hp.2.symm) _ le_sup_right U u v hu hv
  rw [hp.1]
  exact G32Native.paired_c3_residue_support_proper R.P.k (P.C.residue.indices i)

#print axioms pairedC3_selected_affine_normalization_unit
end HodgeLean.Foundations.Program.ResidueSelected
