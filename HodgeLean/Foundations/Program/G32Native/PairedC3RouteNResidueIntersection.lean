import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRestrictions
import HodgeLean.Foundations.Program.G32Native.PairedResidualIntersectionIdentification

/-! # The actual retained intersection is the specified residue hyperplane -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- The actual total-transform residual intersection has the specified
reduced hyperplane scheme structure and retains its original immersion.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.7.13. -/
theorem paired_c3_route_n_residue_intersection
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    letI := P.C.sliceImmersion i.succ
    let E := (P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (P.T.b i).left
    let I := (P.C.slices i.castSucc).left.ker.comap (P.T.b i).left
    let H := s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)
    ∃ e : (residualIntersection (P.C.slices i.succ) (E ⊔ I)).left ≅ H.subscheme,
      e.hom ≫ H.subschemeι =
        (residualIntersectionFirst (P.C.slices i.succ) (E ⊔ I)).left := by
  letI := P.C.sliceImmersion i.succ
  apply (FibreB.residual_intersection_subscheme_iff _ _ _).mpr
  exact paired_c3_selected_residual_restriction R P i

#print axioms paired_c3_route_n_residue_intersection
end HodgeLean.Foundations.Program.G32Native
