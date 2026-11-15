import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedOrientedPositiveData
import HodgeLean.Foundations.Program.SchoenCycleS3LinksProofs

/-! # Reduced residue restrictions on the retained paired tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- Both unprocessed branches cut the actual retained reduced residue
hyperplane, as ideal sheaves, at every step of the selected tower.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4 and
Sublemma 2.7. -/
theorem paired_c3_selected_unprocessed_restrictions
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin (R.r + 1)) (j : Fin R.r) (hij : i.val ≤ j.val) :
    (P.T.D i ⟨2 * j.val, by omega⟩).comap (P.C.slices i).left =
        s2e_s2b_residueIdeal R.P.k (P.C.residue.indices j) ∧
    (P.T.D i ⟨2 * j.val + 1, by omega⟩).comap (P.C.slices i).left =
        s2e_s2b_residueIdeal R.P.k (P.C.residue.indices j) := by
  have h := s2e_chain_unprocessed_pair_transverse_aux R.P.k R.r i.val (by omega)
    P.C.residue.indices
    (fun t : Fin (i.val + 1) => P.T.B ⟨t.val, by omega⟩)
    (fun t : Fin i.val => P.T.b ⟨t.val, by omega⟩)
    (fun t : Fin (i.val + 1) => P.T.D ⟨t.val, by omega⟩)
    (fun t s => P.T.htransform ⟨t.val, by omega⟩ s)
    (fun t => P.T.hcartier ⟨t.val, by omega⟩)
    (fun t => P.C.slices ⟨t.val, by omega⟩)
    (by intro t; exact P.C.sliceComp ⟨t.val, by omega⟩)
    P.C.residueIdeals j hij
  simpa only [Fin.val_last, Fin.eta] using h

/-- The residue ideal retained by the slice export is radical.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4;
the residue hyperplane is taken with its reduced scheme structure. -/
theorem paired_c3_residue_ideal_radical (k : ℕ) (j : Fin (k + 1)) :
    (s2e_s2b_residueIdeal k j).radical = s2e_s2b_residueIdeal k j := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.radical_ideal, s2e_s2b_residueIdeal,
    Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact (PrimeSpectrum.isRadical_vanishingIdeal _).radical

#print axioms paired_c3_residue_ideal_radical

/-- The exceptional ideal plus the pulled-back penultimate component cuts
exactly the retained residue hyperplane on the next slice.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.7.13. -/
theorem paired_c3_selected_residual_restriction
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let E := (P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (P.T.b i).left
    let I := (P.C.slices i.castSucc).left.ker.comap (P.T.b i).left
    (E ⊔ I).comap (P.C.slices i.succ).left =
      s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i) := by
  dsimp only
  rw [Scheme.IdealSheafData.comap_sup,
    ← Scheme.IdealSheafData.comap_comp, ← Over.comp_left, P.C.sliceComp,
    ← Scheme.IdealSheafData.comap_comp, ← Over.comp_left, P.C.sliceComp]
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i (by rfl)
  rw [Scheme.IdealSheafData.comap_sup, hp.1, hp.2, sup_idem]
  have hz : (P.C.slices i.castSucc).left.ker.comap
      (P.C.slices i.castSucc).left = ⊥ := by
    apply eq_bot_iff.mpr
    apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
    rw [Scheme.IdealSheafData.map_bot]
  rw [hz, sup_bot_eq]

#print axioms paired_c3_selected_residual_restriction
#print axioms paired_c3_selected_unprocessed_restrictions
end HodgeLean.Foundations.Program.ResidueSelected
