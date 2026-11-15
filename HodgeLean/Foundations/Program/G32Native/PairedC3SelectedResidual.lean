import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualMarked
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedSlicedComponent
import HodgeLean.Foundations.Program.SchoenCycleS3LinksProofs

/-! # The marked residual ideal on the retained selected tower -/
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

/-- The C3 ideal on the selected tower cuts precisely the stored residue
hyperplane at its own pair, with the existing slice coordinates retained.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv,vi),
proof of Lemma 2.4, and Sublemma 2.7. -/
theorem pairedC3_selected_residual_restriction
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ))
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (C : G32JointSlicedComponent R T W eFinal) (i : Fin R.r) :
    let K := T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let σ := (T.b i).left
    let i₀ := (C.slices i.castSucc).left
    (K.comap σ ⊔ i₀.ker.comap σ).comap (C.slices i.succ).left =
      s2e_s2b_residueIdeal R.P.k (C.residue.indices i) := by
  dsimp only
  have hprev := s2e_chain_unprocessed_pair_transverse_aux R.P.k R.r i.val
    (by omega) C.residue.indices
    (fun t : Fin (i.val + 1) => T.B ⟨t.val, by omega⟩)
    (fun t : Fin i.val => T.b ⟨t.val, by omega⟩)
    (fun t : Fin (i.val + 1) => T.D ⟨t.val, by omega⟩)
    (fun t s => T.htransform ⟨t.val, by omega⟩ s)
    (fun t => T.hcartier ⟨t.val, by omega⟩)
    (fun t : Fin (i.val + 1) => C.slices ⟨t.val, by omega⟩)
    (fun t => C.sliceComp ⟨t.val, by omega⟩)
    C.residueIdeals i (by rfl)
  have hfac : (C.slices i.succ).left ≫ (T.b i).left =
      (C.slices i.castSucc).left := congrArg Over.Hom.left (C.sliceComp i)
  rw [G32Native.pairedC3_residual_restriction (C.slices i.succ) (T.b i).left
    (C.slices i.castSucc).left (𝟙 _) (by simpa only [Category.id_comp] using hfac),
    ← Scheme.IdealSheafData.comap_comp, hfac, Scheme.IdealSheafData.comap_sup]
  have h₁ : (T.D i.castSucc ⟨2 * i.val, by omega⟩).comap
      (C.slices i.castSucc).left = s2e_s2b_residueIdeal R.P.k (C.residue.indices i) :=
    hprev.1
  have h₂ : (T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap
      (C.slices i.castSucc).left = s2e_s2b_residueIdeal R.P.k (C.residue.indices i) :=
    hprev.2
  rw [h₁, h₂, sup_idem]

/-- The actual residual intersection has an isomorphism to the retained
pair's hyperplane over the existing slice, without changing its coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv,vi)
and Sublemma 2.7. -/
theorem pairedC3_selected_marked_intersection
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ))
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (C : G32JointSlicedComponent R T W eFinal) (i : Fin R.r) :
    let K := T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let σ := (T.b i).left
    let i₀ := (C.slices i.castSucc).left
    let Jres := K.comap σ ⊔ i₀.ker.comap σ
    ∃ e : (G32Native.residualIntersection (C.slices i.succ) Jres).left ≅
        (s2e_s2b_residueIdeal R.P.k (C.residue.indices i)).subscheme,
      e.hom ≫ (s2e_s2b_residueIdeal R.P.k (C.residue.indices i)).subschemeι =
        (G32Native.residualIntersectionFirst (C.slices i.succ) Jres).left := by
  dsimp only
  apply (G32Native.residual_intersection_subscheme_iff _ _ _).mpr
  exact pairedC3_selected_residual_restriction R T W eFinal C i

#print axioms pairedC3_selected_marked_intersection

/-- The retained selected coordinates supply the numerical caller's fixed
hyperplane inclusion exactly when the chosen pair has stored coordinate zero.
Source: Hartshorne, Algebraic Geometry, II.2; Schoen, Compositio Mathematica
65 (1988), Lemma 2.3(iv,vi) and Sublemma 2.7. -/
theorem pairedC3_selected_fixed_marked_intersection_iff
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ))
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (C : G32JointSlicedComponent R T W eFinal) (i : Fin R.r) :
    let K := T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let σ := (T.b i).left
    let i₀ := (C.slices i.castSucc).left
    let Jres := K.comap σ ⊔ i₀.ker.comap σ
    (∃ e : (G32Native.residualIntersection (C.slices i.succ) Jres).left ≅
        (s2e_hyperplaneIdeal R.P.k).subscheme,
      e.hom ≫ (s2e_hyperplaneIdeal R.P.k).subschemeι =
        (G32Native.residualIntersectionFirst (C.slices i.succ) Jres).left) ↔
      C.residue.indices i = 0 := by
  dsimp only
  rw [G32Native.residual_intersection_subscheme_iff,
    pairedC3_selected_residual_restriction R T W eFinal C i]
  change s2e_s2b_residueIdeal R.P.k (C.residue.indices i) =
    s2e_s2b_residueIdeal R.P.k 0 ↔ C.residue.indices i = 0
  exact (G32Native.paired_coordinate_residue_injective R.P.k).eq_iff

#print axioms pairedC3_selected_fixed_marked_intersection_iff

#print axioms pairedC3_selected_residual_restriction
end ResidueSelected
end HodgeLean.Foundations.Program
