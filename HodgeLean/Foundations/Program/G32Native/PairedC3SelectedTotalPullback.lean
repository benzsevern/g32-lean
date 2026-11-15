import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedTotalTransform
import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupTotalTransform
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

/-- The last-step ideal identity expressed with the retained final
component; the morphism is obtained from the actual last blowup by index
transport.
Source: Hartshorne, Algebraic Geometry, II.7.13;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem pairedC3_selected_final_total_transform
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r) :
    ∃ σ : (P.T.B (Fin.last R.r)).left ⟶ (P.T.B i.castSucc).left,
      let I := (P.C.slices i.castSucc).left.ker.comap σ
      let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
      I = P.C.ℓ.left.ker ⊓ (K.comap σ ⊔ I) := by
  have hsucc : i.succ = Fin.last R.r := Fin.ext (by simpa using hi)
  have h : ∃ σ : (P.T.B i.succ).left ⟶ (P.T.B i.castSucc).left,
      let I := (P.C.slices i.castSucc).left.ker.comap σ
      let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
      I = (P.C.slices i.succ).left.ker ⊓ (K.comap σ ⊔ I) :=
    ⟨(P.T.b i).left, pairedC3_selected_last_total_transform R P i hi⟩
  rw [hsucc, P.C.sliceLast] at h
  exact h

#print axioms pairedC3_selected_final_total_transform
/-- The actual residual union is the scheme-theoretic inverse image of
the penultimate slice, giving the cartesian square consumed by the
last-blowup conormal comparison.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
theorem pairedC3_selected_final_total_pullback
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r) :
    ∃ σ : (P.T.B (Fin.last R.r)).left ⟶ (P.T.B i.castSucc).left,
      let I := (P.C.slices i.castSucc).left.ker.comap σ
      let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
      let Jres := K.comap σ ⊔ I
      ∃ p : (G32Native.residualUnion P.C.ℓ Jres).left ⟶
          (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).left,
        CategoryTheory.IsPullback p (G32Native.residualUnionι P.C.ℓ Jres).left
          (P.C.slices i.castSucc).left σ := by
  obtain ⟨σ, hI⟩ := pairedC3_selected_final_total_transform R P i hi
  refine ⟨σ, ?_⟩
  letI := P.C.sliceImmersion i.castSucc
  letI := P.C.h_T20_slice_immersion
  exact G32Native.paired_last_total_transform_pullback P.C.ℓ _
    (P.C.slices i.castSucc).left σ hI

#print axioms pairedC3_selected_final_total_pullback
end HodgeLean.Foundations.Program.ResidueSelected
