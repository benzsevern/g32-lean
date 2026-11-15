import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeTargetRank

/-! # Actual projections of canonical unit-plus-free point coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- The module biproduct-to-product comparison retains the actual first projection. -/
theorem conormal_module_biprod_product_fst {K : Type} [Ring K]
    (M N : ModuleCat K) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.fst K M N) =
      biprod.fst := by
  apply (cancel_epi (ModuleCat.biprodIsoProd M N).inv).mp
  simp

/-- The canonical point-coordinate equivalence retains the actual distinguished unit projection. -/
theorem conormal_unit_free_fibre_coordinate_fst {X : Scheme.{0}}
    (x : Spec (CommRingCat.of ℂ) ⟶ X) (k : ℕ)
    (z : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj
        (SheafOfModules.unit X.ringCatSheaf ⊞
          SheafOfModules.free (R := X.ringCatSheaf) (Fin k)))) :
    (conormalUnitFreeFibreCoordinates x k z).1 =
      i1_unitPointCoordinates
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
          (HodgeLean.Foundations.Curves.Picard.LineBundles.pullbackUnit x).hom
          (((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
            ((Scheme.Modules.pullback x).map
              (biprod.fst : (SheafOfModules.unit X.ringCatSheaf ⊞
                SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶
                SheafOfModules.unit X.ringCatSheaf))) z)) := by
  let F := Scheme.Modules.pullback x
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  letI : G.IsRightAdjoint := ⟨_, ⟨tilde.adjunction⟩⟩
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  letI : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBinaryProducts G
  let A := SheafOfModules.unit X.ringCatSheaf
  let B := SheafOfModules.free (R := X.ringCatSheaf) (Fin k)
  have hc : G.map (F.mapBiprod A B).hom ≫ (G.mapBiprod (F.obj A) (F.obj B)).hom ≫
      (ModuleCat.biprodIsoProd _ _).hom ≫
        ModuleCat.ofHom (LinearMap.fst ℂ (G.obj (F.obj A)) (G.obj (F.obj B))) =
      G.map (F.map (biprod.fst : A ⊞ B ⟶ A)) := by
    rw [conormal_module_biprod_product_fst]
    simp only [CategoryTheory.Functor.mapBiprod_hom, biprod.lift_fst,
      ← CategoryTheory.Functor.map_comp]
  have hz := congrArg (fun f => f z) hc
  convert! congrArg (fun t => i1_unitPointCoordinates
    ((G.map (HodgeLean.Foundations.Curves.Picard.LineBundles.pullbackUnit x).hom) t)) hz using 1

/-- The module biproduct-to-product comparison retains the actual second projection. -/
theorem conormal_module_biprod_product_snd {K : Type} [Ring K]
    (M N : ModuleCat K) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.snd K M N) =
      biprod.snd := by
  apply (cancel_epi (ModuleCat.biprodIsoProd M N).inv).mp
  simp

/-- The canonical point-coordinate equivalence retains the actual specified free projection. -/
theorem conormal_unit_free_fibre_coordinate_snd {X : Scheme.{0}}
    (x : Spec (CommRingCat.of ℂ) ⟶ X) (k : ℕ)
    (z : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj
        (SheafOfModules.unit X.ringCatSheaf ⊞
          SheafOfModules.free (R := X.ringCatSheaf) (Fin k)))) :
    (conormalUnitFreeFibreCoordinates x k z).2 =
      (i1_freePointCoordinates k)
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
          (SheafOfModules.pullbackObjFreeIso x.toRingCatSheafHom (Fin k)).hom
          (((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
            ((Scheme.Modules.pullback x).map
              (biprod.snd : (SheafOfModules.unit X.ringCatSheaf ⊞
                SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶
                SheafOfModules.free (R := X.ringCatSheaf) (Fin k)))) z)) := by
  let F := Scheme.Modules.pullback x
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  letI : G.IsRightAdjoint := ⟨_, ⟨tilde.adjunction⟩⟩
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  letI : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBinaryProducts G
  let A := SheafOfModules.unit X.ringCatSheaf
  let B := SheafOfModules.free (R := X.ringCatSheaf) (Fin k)
  have hc : G.map (F.mapBiprod A B).hom ≫ (G.mapBiprod (F.obj A) (F.obj B)).hom ≫
      (ModuleCat.biprodIsoProd _ _).hom ≫
        ModuleCat.ofHom (LinearMap.snd ℂ (G.obj (F.obj A)) (G.obj (F.obj B))) =
      G.map (F.map (biprod.snd : A ⊞ B ⟶ B)) := by
    rw [conormal_module_biprod_product_snd]
    simp only [CategoryTheory.Functor.mapBiprod_hom, biprod.lift_snd,
      ← CategoryTheory.Functor.map_comp]
  have hz := congrArg (fun f => f z) hc
  convert! congrArg (fun t => (i1_freePointCoordinates k)
    ((G.map (SheafOfModules.pullbackObjFreeIso x.toRingCatSheafHom (Fin k)).hom) t)) hz using 1

end HodgeLean.Foundations.Program.G32Native
