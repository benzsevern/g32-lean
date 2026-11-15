import Mathlib.CategoryTheory.Equivalence

/-! # Naturality of an arrow transported through inverse functors

The comparison of objects retains any commuting original arrow diagram.
HC no distance; AV milestone no distance. -/

open CategoryTheory
namespace HodgeLean.Foundations.BundleResolution

theorem i1_transportArrow {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (P R : D ⥤ C) (N : P ≅ R) (T : F ⋙ R ≅ 𝟭 C)
    {M O : C} {M' O' : D} (A : F.obj M ≅ M')
    (q : M ⟶ O) (q' : M' ⟶ O') (g : O' ⟶ F.obj O)
    (h : A.hom ≫ q' ≫ g = F.map q) :
    P.map A.inv ≫ N.hom.app (F.obj M) ≫ T.hom.app M ≫ q =
      P.map q' ≫ N.hom.app O' ≫ R.map g ≫ T.hom.app O := by
  have hT : R.map (F.map q) ≫ T.hom.app O = T.hom.app M ≫ q :=
    T.hom.naturality q
  rw [← hT, ← Category.assoc (N.hom.app _), ← N.hom.naturality]
  simp only [← Category.assoc]
  rw [← P.map_comp, ← h, Iso.inv_hom_id_assoc, P.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (P.map g), N.hom.naturality g]
  simp only [Category.assoc]

end HodgeLean.Foundations.BundleResolution
