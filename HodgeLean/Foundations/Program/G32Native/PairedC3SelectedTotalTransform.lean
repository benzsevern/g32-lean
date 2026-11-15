import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedUnionNeighborhood
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedOffCentre
import HodgeLean.Foundations.Program.G32Native.PairedC3GlobalUnion
import HodgeLean.Foundations.Program.G32Native.PairedC3ClosedPointCover
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedReesCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidueSupport

/-! # Actual total-transform identities on the two selected last charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- The last selected blowup has the scheme-theoretic total transform
union with its actual reduced next slice. No adapted slice generators
are required for this ideal identity.
Source: Hartshorne, Algebraic Geometry, II.7.13;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem pairedC3_selected_last_total_transform
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r) :
    let σ := (P.T.b i).left
    let I := (P.C.slices i.castSucc).left.ker.comap σ
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    I = (P.C.slices i.succ).left.ker ⊓ (K.comap σ ⊔ I) := by
  dsimp only
  letI : IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k+1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  letI := P.C.sliceImmersion i.castSucc
  obtain ⟨e, he, _⟩ := paired_c3_selected_off_centre_iso R P i
  rw [P.C.sliceStrict i]
  apply G32Native.paired_c3_global_union (P.C.slices i.castSucc).left (P.T.b i).left
    (P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩)
    _ (fun _ => Iff.rfl) e he
  intro y hs hk
  obtain ⟨V, hy, hV⟩ := paired_c3_selected_residual_union_neighborhood R P i hi y hs hk
  refine ⟨V, hy, ?_⟩
  rwa [← P.C.sliceStrict i]

#print axioms pairedC3_selected_last_total_transform
end HodgeLean.Foundations.Program.ResidueSelected
