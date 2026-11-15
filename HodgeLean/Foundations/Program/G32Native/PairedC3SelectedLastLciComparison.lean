import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedFrameAssembly
import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupLciFrames

/-! # Selected frames in the last-blowup comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- The selected total-transform frames make the last-blowup conormal
comparison invertible for every supplied penultimate frame.
Source: Hartshorne, Algebraic Geometry, II.3, II.5 and II.8;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_selected_last_lci_comparison
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
        ∃ sq : CategoryTheory.IsPullback p (G32Native.residualUnionι P.C.ℓ Jres).left
          (P.C.slices i.castSucc).left σ,
        ∀ e₀ : s2c_conormal (P.C.slices i.castSucc).left ≅
          (SheafOfModules.free
            (R := (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1))
              (Spec ↧ℂ))).left.ringCatSheaf) (Fin R.P.k) :
            (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1))
              (Spec ↧ℂ))).left.Modules),
          IsIso (Conormal.comparisonMap (P.C.slices i.castSucc).left
            (G32Native.residualUnionι P.C.ℓ Jres).left σ p
            sq.w) := by
  letI := P.C.sliceImmersion i.castSucc
  letI := P.C.h_T20_slice_immersion
  obtain ⟨σ, p, sq, hT⟩ := paired_c3_selected_final_union_frames R P i hi
  refine ⟨σ, p, sq, ?_⟩
  intro e₀
  exact G32Native.paired_last_lci_comparison_of_frames
    (P.C.slices i.castSucc).left _ σ p sq R.P.k e₀ hT

#print axioms paired_c3_selected_last_lci_comparison
end HodgeLean.Foundations.Program.ResidueSelected
