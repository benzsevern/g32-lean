import HodgeLean.Foundations.Program.SchoenTowerCoverSheaf
import HodgeLean.Foundations.Program.SchoenExceptionalProper

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

def s2v_coverStalkEvaluation {X E : TopCat} (f : X ⟶ E) (y : E) :
    (s2c_coverPresheaf f).stalk y ⟶ AddCommGrpCat.of ({x : X // f x = y} → ℂ) :=
  colimit.desc ((OpenNhds.inclusion y).op ⋙ s2c_coverPresheaf f)
    { pt := _
      ι := {
        app := fun U => AddCommGrpCat.ofHom {
          toFun := fun s x => s ⟨x.val, by rw [x.property]; exact U.unop.2⟩
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
        naturality := fun U V i => by
          ext s x
          rfl } }

theorem s2v_coverStalkEvaluation_germ {X E : TopCat} (f : X ⟶ E) (y : E)
    (U : Opens E) (hy : y ∈ U) (s : LocallyConstant {x : X // f x ∈ U} ℂ)
    (x : {x : X // f x = y}) :
    s2v_coverStalkEvaluation f y ((s2c_coverPresheaf f).germ U y hy s) x =
      s ⟨x.val, by rw [x.property]; exact hy⟩ := by
  change (((s2c_coverPresheaf f).germ U y hy) ≫ s2v_coverStalkEvaluation f y) s x = _
  unfold s2v_coverStalkEvaluation
  rw [show (s2c_coverPresheaf f).germ U y hy =
    colimit.ι ((OpenNhds.inclusion y).op ⋙ s2c_coverPresheaf f)
      (op (⟨U, hy⟩ : OpenNhds y)) from rfl, colimit.ι_desc]
  rfl

theorem s2v_coverStalkEvaluation_injective {X E : TopCat}
    (f : X ⟶ E) (hf : IsProperMap f) (y : E) :
    Function.Injective (s2v_coverStalkEvaluation f y) := by
  apply (injective_iff_map_eq_zero (s2v_coverStalkEvaluation f y).hom).mpr
  intro a ha
  obtain ⟨U, hyU, s, rfl⟩ := (s2c_coverPresheaf f).exists_germ_eq a
  change LocallyConstant {x : X // f x ∈ U} ℂ at s
  have hs (x : {x : X // f x = y}) :
      s ⟨x.val, by rw [x.property]; exact hyU⟩ = 0 := by
    have hx := congrFun ha x
    change s2v_coverStalkEvaluation f y ((s2c_coverPresheaf f).germ U y hyU s) x = 0 at hx
    rw [s2v_coverStalkEvaluation_germ] at hx
    exact hx
  let O : Set X := Subtype.val '' {z : {x : X // f x ∈ U} | s z = 0}
  have hO : IsOpen O :=
    (U.isOpen.preimage f.hom.continuous).isOpenEmbedding_subtypeVal.isOpenMap _
      (s.isLocallyConstant.isOpen_fiber 0)
  have hOy : {x : X | f x = y} ⊆ O := by
    intro x hx
    exact ⟨⟨x, by rw [hx]; exact hyU⟩, hs ⟨x, hx⟩, rfl⟩
  obtain ⟨W, hW, hyW, hWO⟩ := s3_fibre_neighborhood f hf y O hO hOy
  let V : Opens E := ⟨W, hW⟩ ⊓ U
  have hyV : y ∈ V := ⟨hyW, hyU⟩
  have hVU : V ≤ U := inf_le_right
  have he : (s2c_coverPresheaf f).map (homOfLE hVU).op s = 0 := by
    apply LocallyConstant.ext
    intro x
    obtain ⟨z, hz, hzx⟩ := hWO x.property.1
    change s ⟨x.val, x.property.2⟩ = 0
    have hzx' : z = ⟨x.val, x.property.2⟩ := Subtype.ext hzx
    exact hzx' ▸ hz
  calc
    (s2c_coverPresheaf f).germ U y hyU s =
        (s2c_coverPresheaf f).germ V y hyV
          ((s2c_coverPresheaf f).map (homOfLE hVU).op s) :=
      ((s2c_coverPresheaf f).germ_res_apply (homOfLE hVU) y hyV s).symm
    _ = 0 := by rw [he, map_zero]

theorem s2v_coverStalkEvaluation_scalar {X E : TopCat} (f : X ⟶ E)
    (y : E) (c : ℂ) (v : (s2c_coverPresheaf f).stalk y)
    (x : {x : X // f x = y}) :
    s2v_coverStalkEvaluation f y
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (s2c_coverPresheafScalar f c) v) x = c * s2v_coverStalkEvaluation f y v x := by
  obtain ⟨U, hy, s, rfl⟩ := (s2c_coverPresheaf f).exists_germ_eq v
  change LocallyConstant {x : X // f x ∈ U} ℂ at s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    s2v_coverStalkEvaluation_germ, s2v_coverStalkEvaluation_germ]
  rfl

theorem s2v_coverStalkEvaluation_deck {X E : TopCat} (f : X ⟶ E)
    (d : X ⟶ X) (hd : d ≫ f = f) (y : E)
    (v : (s2c_coverPresheaf f).stalk y) (x : {x : X // f x = y}) :
    s2v_coverStalkEvaluation f y
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (s2c_coverPresheafDeck f d hd) v) x =
      s2v_coverStalkEvaluation f y v
        ⟨d x.val, (congrArg (fun g : X ⟶ E => g x.val) hd).trans x.property⟩ := by
  obtain ⟨U, hy, s, rfl⟩ := (s2c_coverPresheaf f).exists_germ_eq v
  change LocallyConstant {x : X // f x ∈ U} ℂ at s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    s2v_coverStalkEvaluation_germ, s2v_coverStalkEvaluation_germ]
  rfl

end HodgeLean.Foundations.Program
