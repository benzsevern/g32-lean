import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.NormalizationHelpers
import HodgeLean.Foundations.Program.SchoenTowerDefs

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
open AlgebraicGeometry.RamifiedNormalization.StageThree
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Restriction to an actual open model gives an open inclusion of the same original-field normalization, with both original squares retained. -/
theorem normalization_open_restriction
    {L : Type} [Field L] (X Y : Over (Spec ↧ℂ))
    (u : Y ⟶ X) [IsOpenImmersion u.left]
    (f : Spec ↧L ⟶ X.left) [QuasiCompact f] [QuasiSeparated f]
    (g : Spec ↧L ⟶ Y.left) [QuasiCompact g] [QuasiSeparated g]
    (hg : g ≫ u.left = f) :
    ∃ J : s2b_normalizationOver Y g ⟶ s2b_normalizationOver X f,
      IsOpenImmersion J.left ∧
      J ≫ s2b_normalizationMap X f = s2b_normalizationMap Y g ≫ u ∧
      g.toNormalization ≫ J.left = f.toNormalization ∧
      Set.range J.left = f.fromNormalization ⁻¹' Set.range u.left := by
  let p := pullback.snd f u.left
  have hp : pullback.fst f u.left ≫ g = p := by
    apply (cancel_mono u.left).mp
    rw [Category.assoc, hg, pullback.condition]
  haveI : IsIso (pullback.fst f u.left) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Hom.opensRange_pullbackFst]
    apply top_unique
    intro z _
    change f z ∈ u.left.opensRange
    rw [← hg, Scheme.Hom.comp_apply]
    exact ⟨g z, rfl⟩
  let e := asIso (pullback.fst f u.left)
  have H : e.hom ≫ g = p ≫ (Iso.refl Y.left).hom := by
    simpa only [e, asIso_hom, Iso.refl_hom, Category.comp_id] using hp
  let C := normalizationCongr p g e (Iso.refl Y.left) H
  let P := asIso (f.normalizationPullback u.left)
  have hPb : P.hom ≫ pullback.snd f.fromNormalization u.left = p.fromNormalization := by
    dsimp only [P, asIso_hom]
    exact f.normalizationPullback_snd u.left
  have hPp : p.toNormalization ≫ P.hom ≫ pullback.fst f.fromNormalization u.left =
      e.hom ≫ f.toNormalization := by
    dsimp only [P, asIso_hom, e]
    exact f.toNormalization_normalizationPullback_fst u.left
  let E := C.symm ≪≫ P
  let j := E.hom ≫ pullback.fst f.fromNormalization u.left
  have hCb : C.hom ≫ g.fromNormalization = p.fromNormalization := by
    simpa only [Iso.refl_hom, Category.comp_id] using
      normalizationCongr_base p g e (Iso.refl Y.left) H
  have hbase : j ≫ f.fromNormalization = g.fromNormalization ≫ u.left := by
    dsimp only [j, E, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.hom,
      hPb, ← hCb]
    simp only [← Category.assoc, C.inv_hom_id, Category.id_comp]
  let J : s2b_normalizationOver Y g ⟶ s2b_normalizationOver X f := Over.homMk j (by
    change j ≫ (f.fromNormalization ≫ X.hom) = g.fromNormalization ≫ Y.hom
    rw [← Category.assoc, hbase, Category.assoc, u.w])
  have hsurj : Function.Surjective E.hom := by
    intro z
    exact ⟨E.inv z, congrArg (fun k : pullback f.fromNormalization u.left ⟶
      pullback f.fromNormalization u.left => k z) E.inv_hom_id⟩
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · change IsOpenImmersion (E.hom ≫ pullback.fst f.fromNormalization u.left)
    infer_instance
  · apply Over.OverMorphism.ext
    exact hbase
  · have hCp : p.toNormalization ≫ C.hom = e.hom ≫ g.toNormalization := by
      simpa only [Iso.refl_hom, Category.comp_id] using
        normalizationCongr_point p g e (Iso.refl Y.left) H
    have hpoint : g.toNormalization ≫ C.inv = e.inv ≫ p.toNormalization := by
      apply (cancel_mono C.hom).mp
      simp only [Category.assoc, C.inv_hom_id, Category.comp_id]
      rw [hCp]
      simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]
    change g.toNormalization ≫ (C.inv ≫ P.hom) ≫ pullback.fst f.fromNormalization u.left = _
    calc
      g.toNormalization ≫ (C.inv ≫ P.hom) ≫ pullback.fst f.fromNormalization u.left =
          (g.toNormalization ≫ C.inv) ≫ (P.hom ≫ pullback.fst f.fromNormalization u.left) := by
            simp only [Category.assoc]
      _ = (e.inv ≫ p.toNormalization) ≫ (P.hom ≫ pullback.fst f.fromNormalization u.left) :=
        congrArg (fun z => z ≫ (P.hom ≫ pullback.fst f.fromNormalization u.left)) hpoint
      _ = e.inv ≫ (p.toNormalization ≫ P.hom ≫ pullback.fst f.fromNormalization u.left) :=
        Category.assoc _ _ _
      _ = e.inv ≫ (e.hom ≫ f.toNormalization) := congrArg (fun z => e.inv ≫ z) hPp
      _ = f.toNormalization := by simp only [e.inv_hom_id_assoc]
  · change Set.range ((pullback.fst f.fromNormalization u.left) ∘ E.hom) = _
    rw [Set.range_comp, hsurj.range_eq, Set.image_univ]
    exact IsOpenImmersion.range_pullbackFst u.left f.fromNormalization

end AlgebraicGeometry.RamifiedNormalization.StageFour
