module

public import HodgeLean.Foundations.Program.SchoenExceptionalSections
public import Mathlib.Algebra.Category.Grp.Zero

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite TopCat.Presheaf
open scoped AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s3_fibre_section_map_res {X Y : TopCat} (p : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat X) (y : Y) (U V : Opens Y)
    (hyU : y ∈ U) (hyV : y ∈ V) (hUV : U ≤ V) :
    F.obj.map ((Opens.map p).map (homOfLE hUV)).op ≫
      s3_fibre_section_map p F y U hyU = s3_fibre_section_map p F y V hyV := by
  ext s
  apply TopCat.Presheaf.section_ext
    ((TopCat.Sheaf.pullback AddCommGrpCat (s3_fibreInclusion p y)).obj F) ⊤
  intro x _
  rw [ConcreteCategory.comp_apply, s3_fibre_section_map_germ, s3_fibre_section_map_germ]
  congr 1
  exact F.presheaf.germ_res_apply ((Opens.map p).map (homOfLE hUV)) x.1 _ s

def s3_proper_stalk_to_sections {X Y : TopCat} (p : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat X) (y : Y) :
    (p _* F.presheaf).stalk y ⟶
      ((TopCat.Sheaf.pullback AddCommGrpCat (s3_fibreInclusion p y)).obj F).obj.obj (op ⊤) :=
  colimit.desc ((OpenNhds.inclusion y).op ⋙ (p _* F.presheaf))
    { pt := _
      ι := {
        app := fun U => s3_fibre_section_map p F y U.unop.1 U.unop.2
        naturality := fun U V f => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          exact s3_fibre_section_map_res p F y V.unop.1 U.unop.1 V.unop.2 U.unop.2
            f.unop.le } }

theorem s3_proper_stalk_to_sections_germ {X Y : TopCat} (p : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat X) (y : Y) (U : Opens Y) (hyU : y ∈ U) :
    (p _* F.presheaf).germ U y hyU ≫ s3_proper_stalk_to_sections p F y =
      s3_fibre_section_map p F y U hyU := by
  exact colimit.ι_desc _ _

theorem s3_proper_stalk_to_sections_bijective {X Y : TopCat}
    [T2Space X] [LocallyCompactSpace X] (p : X ⟶ Y) (hp : IsProperMap p)
    (F : TopCat.Sheaf AddCommGrpCat X) (y : Y) :
    Function.Bijective (s3_proper_stalk_to_sections p F y) := by
  constructor
  · intro a b hab
    obtain ⟨U, hyU, s, rfl⟩ := (p _* F.presheaf).exists_germ_eq a
    obtain ⟨V, hyV, t, rfl⟩ := (p _* F.presheaf).exists_germ_eq b
    have he : s3_fibre_section_map p F y U hyU s = s3_fibre_section_map p F y V hyV t := by
      simpa only [← ConcreteCategory.comp_apply, s3_proper_stalk_to_sections_germ] using hab
    obtain ⟨W, hyW, hWU, hWV, hst⟩ := s3_fibre_section_eq_near p hp F y U V hyU hyV s t he
    calc
      _ = (p _* F.presheaf).germ W y hyW
          ((p _* F.presheaf).map (homOfLE hWU).op s) :=
        ((p _* F.presheaf).germ_res_apply (homOfLE hWU) y hyW s).symm
      _ = (p _* F.presheaf).germ W y hyW
          ((p _* F.presheaf).map (homOfLE hWV).op t) := congrArg _ hst
      _ = _ := (p _* F.presheaf).germ_res_apply (homOfLE hWV) y hyW t
  · intro t
    obtain ⟨V, hyV, s, hs⟩ := s3_fibre_section_extend p hp F y t
    refine ⟨(p _* F.presheaf).germ V y hyV s, ?_⟩
    simpa only [← ConcreteCategory.comp_apply, s3_proper_stalk_to_sections_germ] using hs


def s3_proper_stalk_sections_iso {X Y : TopCat} [T2Space X] [LocallyCompactSpace X]
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X) (y : Y) :
    (p _* F.presheaf).stalk y ≅
      ((TopCat.Sheaf.pullback AddCommGrpCat (s3_fibreInclusion p y)).obj F).obj.obj (op ⊤) := by
  haveI : IsIso (s3_proper_stalk_to_sections p F y) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (s3_proper_stalk_to_sections_bijective p hp F y)
  exact asIso (s3_proper_stalk_to_sections p F y)

theorem s3_proper_pushforward_isZero {X Y : TopCat} [T2Space X] [LocallyCompactSpace X]
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X)
    (hF : ∀ y : Y, Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pullback AddCommGrpCat (s3_fibreInclusion p y)).obj F) 0)) :
    IsZero ((TopCat.Sheaf.pushforward AddCommGrpCat p).obj F) := by
  apply TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _ |>.mpr
  intro y
  let H := (TopCat.Sheaf.pullback AddCommGrpCat (s3_fibreInclusion p y)).obj F
  let : Subsingleton (CategoryTheory.Sheaf.H H 0) := hF y
  let : AddCommGroup (CategoryTheory.Sheaf.H H 0) := TopCat.Sheaf.extAddCommGroup
  let e := CategoryTheory.Sheaf.H.equiv₀ H isTerminalTop
  let : Subsingleton (H.obj.obj (op (⊤ : Opens {x : X // p x = y}))) :=
    e.symm.injective.subsingleton
  let : Subsingleton ((p _* F.presheaf).stalk y) :=
    (s3_proper_stalk_to_sections_bijective p hp F y).1.subsingleton
  change IsZero ((p _* F.presheaf).stalk y)
  exact AddCommGrpCat.isZero_of_subsingleton _

end HodgeLean.Foundations.Program
