import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedResidual
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualBaseSmooth

/-! # The smooth base on the actual selected tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
namespace ResidueSelected
attribute [local instance] G32JointSlicedComponent.sliceImmersion
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24
attribute [local instance] G32JointComponent.hQ

/-- The paired centre cuts the retained hyperplane already on the penultimate
slice, before taking its inverse image in the last blow-up.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv,vi). -/
theorem pairedC3_selected_penultimate_restriction
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ))
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (C : G32JointSlicedComponent R T W eFinal) (i : Fin R.r) :
    let K := T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    K.comap (C.slices i.castSucc).left =
      s2e_s2b_residueIdeal R.P.k (C.residue.indices i) := by
  dsimp only
  have h := pairedC3_selected_residual_restriction R T W eFinal C i
  dsimp only at h
  have hfac : (C.slices i.succ).left ≫ (T.b i).left =
      (C.slices i.castSucc).left := congrArg Over.Hom.left (C.sliceComp i)
  rw [G32Native.pairedC3_residual_restriction (C.slices i.succ) (T.b i).left
    (C.slices i.castSucc).left (𝟙 _) (by simpa only [Category.id_comp] using hfac),
    ← Scheme.IdealSheafData.comap_comp, hfac] at h
  exact h

/-- The actual base D of the residual component is smooth over the ground
field, using the retained hyperplane rather than a dimension count.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv,vi);
Hartshorne, Algebraic Geometry, II.8. -/
theorem pairedC3_selected_residual_base_smooth
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ))
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (C : G32JointSlicedComponent R T W eFinal) (i : Fin R.r) :
    let K := T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    Smooth ((K ⊔ (C.slices i.castSucc).left.ker).subschemeι ≫
      (T.B i.castSucc).hom) := by
  dsimp only
  exact G32Native.pairedC3_residual_base_smooth R.P.k R.P.act.cyc_positive
    (C.slices i.castSucc) _ (C.residue.indices i)
    (pairedC3_selected_penultimate_restriction R T W eFinal C i)

#print axioms pairedC3_selected_residual_base_smooth

/-- The selected marked intersection has a standard hyperplane model over
the explicitly changed projective coordinates.
Source: Hartshorne, Algebraic Geometry, II.2; Schoen,
Compositio Mathematica 65 (1988), Lemma 2.3(iv,vi). -/
theorem pairedC3_selected_normalized_intersection
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ))
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (C : G32JointSlicedComponent R T W eFinal) (i : Fin R.r) :
    let K := T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let Jres := K.comap (T.b i).left ⊔
      (C.slices i.castSucc).left.ker.comap (T.b i).left
    ∃ e : (G32Native.residualIntersection (C.slices i.succ) Jres).left ≅
        (s2e_hyperplaneIdeal R.P.k).subscheme,
      e.hom ≫ (s2e_hyperplaneIdeal R.P.k).subschemeι =
        (G32Native.residualIntersectionFirst (C.slices i.succ) Jres).left ≫
          (s2e_linearProjectiveOverIso
            (G32Native.pairedC3CoordinateSwap R.P.k (C.residue.indices i))).hom.left := by
  dsimp only
  exact G32Native.pairedC3_normalized_intersection R.P.k (C.slices i.succ) _
    (C.residue.indices i) (pairedC3_selected_residual_restriction R T W eFinal C i)

#print axioms pairedC3_selected_normalized_intersection

#print axioms pairedC3_selected_penultimate_restriction
end ResidueSelected
end HodgeLean.Foundations.Program
