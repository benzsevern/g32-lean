import HodgeLean.Foundations.Program.G32Native.PairedConormalPointRelationVector

/-! # Actual scalar coordinates of the framed relation vector -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- The distinguished coordinate of the actual framed relation vector is
exactly the scalar of the supplied distinguished ideal arrow. -/
theorem conormal_point_relation_vector_fst {X : Scheme.{0}} (k : ℕ) {I : X.Modules}
    (a : I ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : I ⟶ SheafOfModules.free (R := X.ringCatSheaf) (Fin k))
    (x : Spec (CommRingCat.of ℂ) ⟶ X)
    (u : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶ (Scheme.Modules.pullback x).obj I) :
    (conormalPointRelationVector k a b x u).1 =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
          (u ≫ (Scheme.Modules.pullback x).map a ≫
            (HodgeLean.Foundations.Curves.Picard.LineBundles.pullbackUnit x).hom))
              (1 : Γ(Spec ↧ℂ, ⊤))) := by
  rw [conormalPointRelationVector, conormal_unit_free_fibre_coordinate_fst,
    i1_unitPointCoordinates_apply]
  let F := Scheme.Modules.pullback x
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let r := HodgeLean.Foundations.NormalPresentation.relation a b
  let A := SheafOfModules.unit X.ringCatSheaf
  let B := SheafOfModules.free (R := X.ringCatSheaf) (Fin k)
  let c := (HodgeLean.Foundations.Curves.Picard.LineBundles.pullbackUnit x).hom
  have hc : (u ≫ F.map r) ≫ F.map (biprod.fst : A ⊞ B ⟶ A) ≫ c =
      u ≫ F.map a ≫ c := by
    calc
      _ = u ≫ F.map (r ≫ (biprod.fst : A ⊞ B ⟶ A)) ≫ c := by
        simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = _ := by
        dsimp only [r, HodgeLean.Foundations.NormalPresentation.relation]
        erw [biprod.lift_fst]
  have hz := congrArg (fun f : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶
      SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf =>
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((G.map f) (1 : Γ(Spec ↧ℂ, ⊤)))) hc
  simp only [CategoryTheory.Functor.map_comp] at hz
  convert! hz using 1
  all_goals simp only [G, F, c, CategoryTheory.Functor.map_comp]
  all_goals rfl

/-- Each retained coordinate of the actual framed relation vector is the
scalar of the same supplied retained ideal row. -/
theorem conormal_point_relation_vector_row {X : Scheme.{0}} (k : ℕ) {I : X.Modules}
    (a : I ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : I ⟶ SheafOfModules.free (R := X.ringCatSheaf) (Fin k))
    (x : Spec (CommRingCat.of ℂ) ⟶ X)
    (u : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶ (Scheme.Modules.pullback x).obj I)
    (i : Fin k) :
    (conormalPointRelationVector k a b x u).2 i =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
          (u ≫ (Scheme.Modules.pullback x).map (b ≫ i1_freeSheafProjection X k i) ≫
            (HodgeLean.Foundations.Curves.Picard.LineBundles.pullbackUnit x).hom))
              (1 : Γ(Spec ↧ℂ, ⊤))) := by
  rw [conormalPointRelationVector, conormal_unit_free_fibre_coordinate_row,
    i1_unitPointCoordinates_apply]
  let F := Scheme.Modules.pullback x
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let r := HodgeLean.Foundations.NormalPresentation.relation a b
  let A := SheafOfModules.unit X.ringCatSheaf
  let B := SheafOfModules.free (R := X.ringCatSheaf) (Fin k)
  let c := (HodgeLean.Foundations.Curves.Picard.LineBundles.pullbackUnit x).hom
  have hc : (u ≫ F.map r) ≫
      (F.map ((biprod.snd : A ⊞ B ⟶ B) ≫ i1_freeSheafProjection X k i) ≫ c) =
      u ≫ F.map (b ≫ i1_freeSheafProjection X k i) ≫ c := by
    calc
      _ = u ≫ F.map (r ≫ ((biprod.snd : A ⊞ B ⟶ B) ≫
          i1_freeSheafProjection X k i)) ≫ c := by
        simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = _ := by
        dsimp only [r, HodgeLean.Foundations.NormalPresentation.relation]
        erw [biprod.lift_snd_assoc]
  have hz := congrArg (fun f : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶
      SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf =>
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((G.map f) (1 : Γ(Spec ↧ℂ, ⊤)))) hc
  simp only [CategoryTheory.Functor.map_comp] at hz
  convert! hz using 1
  all_goals simp only [G, F, c, CategoryTheory.Functor.map_comp]
  all_goals rfl

end HodgeLean.Foundations.Program.G32Native
