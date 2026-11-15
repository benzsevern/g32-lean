module

public import HodgeLean.Foundations.Program.SchoenExceptionalBaseChangeZero
public import Mathlib.CategoryTheory.Whiskering

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry
namespace HodgeLean.Foundations.Program

def s3_pullback_section_trans {X Y : TopCat.{0}} (i : X ⟶ Y) :
    TopCat.Sheaf.forget AddCommGrpCat.{0} Y ⟶
      TopCat.Sheaf.pullback AddCommGrpCat.{0} i ⋙ TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
        TopCat.Presheaf.pushforward AddCommGrpCat.{0} i :=
  Functor.whiskerLeft (TopCat.Sheaf.forget AddCommGrpCat.{0} Y)
      (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} i).unit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (TopCat.Sheaf.forget AddCommGrpCat.{0} Y ⋙
          TopCat.Presheaf.pullback AddCommGrpCat.{0} i)
          (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{0}).unit ≫
        Functor.whiskerRight (TopCat.Sheaf.pullbackIso AddCommGrpCat.{0} i).inv
          (TopCat.Sheaf.forget AddCommGrpCat.{0} X))
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} i)

theorem s3_pullback_section_trans_app {X Y : TopCat.{0}} (i : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{0} Y) :
    (s3_pullback_section_trans i).app F = s3_pullback_section_map i F := rfl

theorem s3_pullback_section_naturality {X Y : TopCat.{0}} (i : X ⟶ Y)
    {F G : TopCat.Sheaf AddCommGrpCat.{0} Y} (φ : F ⟶ G) :
    φ.hom ≫ s3_pullback_section_map i G = s3_pullback_section_map i F ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} i).map
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} i).map φ).hom :=
  (s3_pullback_section_trans i).naturality φ


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s3_fibre_section_map_naturality {X Y : TopCat.{0}} (p : X ⟶ Y)
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (φ : F ⟶ G)
    (y : Y) (V : Opens Y) (hyV : y ∈ V) :
    φ.hom.app (op ((Opens.map p).obj V)) ≫ s3_fibre_section_map p G y V hyV =
      s3_fibre_section_map p F y V hyV ≫
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (s3_fibreInclusion p y)).map φ).hom.app (op ⊤) := by
  let i := s3_fibreInclusion p y
  let r : (⊤ : Opens {x : X // p x = y}) ⟶
      (Opens.map i).obj ((Opens.map p).obj V) := homOfLE
        (fun x _ => show p x.1 ∈ V from x.2.symm ▸ hyV)
  let ψ := ((TopCat.Sheaf.pullback AddCommGrpCat.{0} i).map φ).hom
  have e := congrArg (fun α => α.app (op ((Opens.map p).obj V)))
    (s3_pullback_section_naturality i φ)
  change φ.hom.app (op ((Opens.map p).obj V)) ≫
    (s3_pullback_section_map i G).app (op ((Opens.map p).obj V)) =
    (s3_pullback_section_map i F).app (op ((Opens.map p).obj V)) ≫
      ψ.app (op ((Opens.map i).obj ((Opens.map p).obj V))) at e
  change φ.hom.app _ ≫ ((s3_pullback_section_map i G).app _ ≫
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} i).obj G).obj.map r.op) =
    ((s3_pullback_section_map i F).app _ ≫
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} i).obj F).obj.map r.op) ≫ ψ.app (op ⊤)
  rw [← Category.assoc, e, Category.assoc, ← ψ.naturality r.op, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem s3_proper_stalk_to_sections_naturality {X Y : TopCat.{0}} (p : X ⟶ Y)
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (φ : F ⟶ G) (y : Y) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).map φ).hom ≫
        s3_proper_stalk_to_sections p G y =
      s3_proper_stalk_to_sections p F y ≫
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (s3_fibreInclusion p y)).map φ).hom.app (op ⊤) := by
  apply TopCat.Presheaf.stalk_hom_ext (p _* F.presheaf)
  intro U hyU
  rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  change φ.hom.app (op ((Opens.map p).obj U)) ≫
    (p _* G.presheaf).germ U y hyU ≫ s3_proper_stalk_to_sections p G y = _
  rw [s3_proper_stalk_to_sections_germ, ← Category.assoc,
    s3_proper_stalk_to_sections_germ]
  exact s3_fibre_section_map_naturality p φ y U hyU

end HodgeLean.Foundations.Program
