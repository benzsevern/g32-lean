import HodgeLean.Foundations.NormalPresentation.Defs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Actual relation arrows under a functor and specified frame comparisons -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program.G32Native

/-- A functor preserving binary biproducts transports the actual relation
through the supplied distinguished and retained frame isomorphisms. -/
theorem conormal_functor_relation_transport
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F]
    {I A B : C} {A' B' : D} (a : I ⟶ A) (b : I ⟶ B)
    (eA : F.obj A ≅ A') (eB : F.obj B ≅ B') :
    F.map (HodgeLean.Foundations.NormalPresentation.relation a b) ≫
      (F.mapBiprod A B ≪≫ biprod.mapIso eA eB).hom =
      HodgeLean.Foundations.NormalPresentation.relation
        (F.map a ≫ eA.hom) (F.map b ≫ eB.hom) := by
  apply biprod.hom_ext
  · dsimp only [HodgeLean.Foundations.NormalPresentation.relation,
      Iso.trans_hom, biprod.mapIso_hom, CategoryTheory.Functor.mapBiprod_hom]
    erw [Category.assoc, Category.assoc, biprod.map_fst,
      biprod.lift_fst_assoc, ← CategoryTheory.Functor.map_comp_assoc, biprod.lift_fst]
    erw [biprod.lift_fst]
  · dsimp only [HodgeLean.Foundations.NormalPresentation.relation,
      Iso.trans_hom, biprod.mapIso_hom, CategoryTheory.Functor.mapBiprod_hom]
    erw [Category.assoc, Category.assoc, biprod.map_snd,
      biprod.lift_snd_assoc, ← CategoryTheory.Functor.map_comp_assoc, biprod.lift_snd]
    erw [biprod.lift_snd]

end HodgeLean.Foundations.Program.G32Native
