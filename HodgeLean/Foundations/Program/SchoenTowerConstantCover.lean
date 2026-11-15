import HodgeLean.Foundations.Program.SchoenTowerCoverStalk
import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.Constant

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

def s2v_constantToIdentityCoverPresheaf (X : TopCat.{0}) :
    TopCat.Presheaf.const X (AddCommGrpCat.of ℂ) ⟶ s2c_coverPresheaf (𝟙 X) where
  app U := AddCommGrpCat.ofHom {
    toFun := fun a => LocallyConstant.const _ a
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  naturality := fun U V i => by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    rfl

theorem s2v_constantToIdentityCoverPresheaf_stalk_injective
    (X : TopCat.{0}) (x : X) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
      (s2v_constantToIdentityCoverPresheaf X)) := by
  let P := TopCat.Presheaf.const X (AddCommGrpCat.of ℂ)
  let Q := s2c_coverPresheaf (𝟙 X)
  let η := s2v_constantToIdentityCoverPresheaf X
  apply (injective_iff_map_eq_zero
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map η).hom).mpr
  intro v hv
  obtain ⟨U, hxU, a, rfl⟩ := P.exists_germ_eq v
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hv
  have hh : Q.germ U x hxU (η.app (op U) a) = Q.germ U x hxU 0 := by
    simpa only [map_zero] using hv
  obtain ⟨V, hxV, i, j, he⟩ := Q.germ_eq x hxU hxU _ _ hh
  have ha := congrArg (fun s : LocallyConstant {z : X // (𝟙 X) z ∈ V} ℂ =>
    s ⟨x, hxV⟩) he
  change a = 0 at ha
  rw [ha, map_zero]

theorem s2v_constantToIdentityCoverPresheaf_stalk_surjective
    (X : TopCat.{0}) (x : X) :
    Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
      (s2v_constantToIdentityCoverPresheaf X)) := by
  let P := TopCat.Presheaf.const X (AddCommGrpCat.of ℂ)
  let Q := s2c_coverPresheaf (𝟙 X)
  let η := s2v_constantToIdentityCoverPresheaf X
  intro v
  obtain ⟨U, hxU, s, rfl⟩ := Q.exists_germ_eq v
  change LocallyConstant U ℂ at s
  let a := s ⟨x, hxU⟩
  let O : Set X := Subtype.val '' {z : U | s z = a}
  have hO : IsOpen O := U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _
    (s.isLocallyConstant.isOpen_fiber a)
  let V : Opens X := ⟨O, hO⟩
  have hxV : x ∈ V := ⟨⟨x, hxU⟩, rfl, rfl⟩
  have hVU : V ≤ U := by
    rintro z ⟨w, hw, rfl⟩
    exact w.property
  have he : Q.map (homOfLE hVU).op s = η.app (op V) a := by
    apply LocallyConstant.ext
    intro z
    obtain ⟨w, hw, hwz⟩ := z.property
    change s ⟨z.val, hVU z.property⟩ = a
    have hwz' : w = ⟨z.val, hVU z.property⟩ := Subtype.ext hwz
    exact hwz' ▸ hw
  refine ⟨P.germ V x hxV a, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ← he]
  exact Q.germ_res_apply (homOfLE hVU) x hxV s

theorem s2v_constantToIdentityCoverSheaf_isIso (X : TopCat.{0}) :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map
      (s2v_constantToIdentityCoverPresheaf X)) := by
  let J := Opens.grothendieckTopology X
  let P := TopCat.Presheaf.const X (AddCommGrpCat.of ℂ)
  let Q := s2c_coverPresheaf (𝟙 X)
  let η := s2v_constantToIdentityCoverPresheaf X
  let μ := (presheafToSheaf J AddCommGrpCat.{0}).map η
  haveI (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map μ.hom) := by
    let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x
    let α := T.map (toSheafify J P)
    let β := T.map (toSheafify J Q)
    haveI : IsIso α := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{0} P
    haveI : IsIso β := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{0} Q
    haveI : IsIso (T.map η) := (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨s2v_constantToIdentityCoverPresheaf_stalk_injective X x,
        s2v_constantToIdentityCoverPresheaf_stalk_surjective X x⟩
    have hc : α ≫ T.map μ.hom = T.map η ≫ β := by
      rw [← T.map_comp, ← T.map_comp]
      exact congrArg T.map (toSheafify_naturality J η).symm
    haveI : IsIso (α ≫ T.map μ.hom) := by rw [hc]; infer_instance
    exact IsIso.of_isIso_comp_left α _
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso μ

def s2v_constantIdentityCoverIso (X : TopCat.{0}) :
    (TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ) ≅
      (⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩ :
        TopCat.Sheaf AddCommGrpCat.{0} X) := by
  let J := Opens.grothendieckTopology X
  letI := s2v_constantToIdentityCoverSheaf_isIso X
  exact asIso ((presheafToSheaf J AddCommGrpCat.{0}).map
      (s2v_constantToIdentityCoverPresheaf X)) ≪≫
    asIso ((sheafificationAdjunction J AddCommGrpCat.{0}).counit.app
      ⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩)

def s2v_coverSheaf_pushforwardConstantIso {X E : TopCat.{0}} (f : X ⟶ E) :
    s2c_coverSheaf f ≅ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj
      ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ)) := by
  let L : TopCat.Sheaf AddCommGrpCat.{0} X :=
    ⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
  exact asIso ((sheafificationAdjunction (Opens.grothendieckTopology E)
    AddCommGrpCat.{0}).counit.app (P.obj L)) ≪≫
      P.mapIso (s2v_constantIdentityCoverIso X).symm

end HodgeLean.Foundations.Program
