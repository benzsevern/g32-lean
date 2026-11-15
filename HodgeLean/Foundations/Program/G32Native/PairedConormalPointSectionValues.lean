import HodgeLean.Foundations.Program.G32Native.PairedConormalGlobalSectionEvaluation
import HodgeLean.Foundations.Program.G32Native.PairedConormalPullbackAdditive
import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeTargetRank

/-! # Actual point values of the supplied presentation generators -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Curves.Picard.LineBundles

/-- The actual value of a supplied global section at a specified scheme arrow. -/
def pairedPointSectionValue {X : Scheme.{0}} (M : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) (x : Spec ↧ℂ ⟶ X) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj M) :=
  (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
    (i1_moduleSectionPullback x M s) (1 : Γ(Spec ↧ℂ, ⊤))

/-- The supplied quotient acts on the actual values of the same global generators. -/
theorem paired_pointSectionValue_naturality {X : Scheme.{0}}
    {M N : X.Modules} (φ : M ⟶ N)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) (x : Spec ↧ℂ ⟶ X) :
    pairedPointSectionValue N (s ≫ φ) x =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback x).map φ) (pairedPointSectionValue M s x) := by
  unfold pairedPointSectionValue
  rw [i1_moduleSectionPullback_naturality, Functor.map_comp]
  rfl

/-- Point values commute with the canonical comparison for composed pullbacks. -/
theorem paired_pointSectionValue_pullback {X Y : Scheme.{0}}
    (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (x : Spec ↧ℂ ⟶ X) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackComp x f).hom.app M)
      (pairedPointSectionValue ((Scheme.Modules.pullback f).obj M)
        (i1_moduleSectionPullback f M s) x) =
      pairedPointSectionValue M s (x ≫ f) := by
  have h := congrArg (fun t : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶
      (Scheme.Modules.pullback (x ≫ f)).obj M =>
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map t (1 : Γ(Spec ↧ℂ, ⊤)))
      (i1_moduleSectionPullback_composition x f M s)
  rw [Functor.map_comp] at h
  exact h

/-- Equal actual point arrows give the same section value through their
specified pullback comparison. -/
theorem paired_pointSectionValue_congr {X : Scheme.{0}}
    (M : X.Modules) (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (x y : Spec ↧ℂ ⟶ X) (h : x = y) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackCongr h).hom.app M) (pairedPointSectionValue M s x) =
      pairedPointSectionValue M s y := by
  have he := congrArg (fun t : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶
      (Scheme.Modules.pullback y).obj M =>
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map t (1 : Γ(Spec ↧ℂ, ⊤)))
      (paired_moduleSectionPullback_congr x y h M s)
  rw [Functor.map_comp] at he
  exact he

/-- The zero global section has zero value in the actual point pullback. -/
theorem paired_pointSectionValue_zero {X : Scheme.{0}}
    (M : X.Modules) (x : Spec ↧ℂ ⟶ X) :
    pairedPointSectionValue M (0 : SheafOfModules.unit X.ringCatSheaf ⟶ M) x = 0 := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  letI : G.IsRightAdjoint := ⟨_, ⟨tilde.adjunction⟩⟩
  letI : (Scheme.Modules.pullback x).Additive := conormal_scheme_pullback_additive x
  change G.map ((i1_unitPullbackIso x).inv ≫
    (Scheme.Modules.pullback x).map (0 : SheafOfModules.unit X.ringCatSheaf ⟶ M))
      (1 : Γ(Spec ↧ℂ, ⊤)) = 0
  rw [Functor.map_zero, comp_zero, Functor.map_zero]
  rfl

/-- The actual pullback of the global unit section has scalar coordinate one. -/
theorem paired_pointSectionValue_unit {X : Scheme.{0}} (x : Spec ↧ℂ ⟶ X) :
    i1_unitPointCoordinates
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit x).hom
        (pairedPointSectionValue (SheafOfModules.unit X.ringCatSheaf) (𝟙 _) x)) = 1 := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  have h : i1_moduleSectionPullback x (SheafOfModules.unit X.ringCatSheaf) (𝟙 _) ≫
      (pullbackUnit x).hom = 𝟙 _ := by
    change ((pullbackUnit x).inv ≫ (Scheme.Modules.pullback x).map (𝟙 _)) ≫
      (pullbackUnit x).hom = 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id]
  have he := congrArg (fun t : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶
      SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf =>
    G.map t (1 : Γ(Spec ↧ℂ, ⊤))) h
  rw [Functor.map_comp, CategoryTheory.Functor.map_id] at he
  change G.map (pullbackUnit x).hom
    (pairedPointSectionValue (SheafOfModules.unit X.ringCatSheaf) (𝟙 _) x) =
      (1 : Γ(Spec ↧ℂ, ⊤)) at he
  exact (congrArg i1_unitPointCoordinates he).trans
    ((i1_unitPointCoordinates_apply (1 : Γ(Spec ↧ℂ, ⊤))).trans (map_one _))

/-- A supplied free generator has its original standard coordinate after
the canonical actual point pullback comparison. -/
theorem paired_pointSectionValue_free_generator {X : Scheme.{0}}
    (x : Spec ↧ℂ ⟶ X) (k : ℕ) (i : Fin k) :
    i1_freePointCoordinates k
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (SheafOfModules.pullbackObjFreeIso x.toRingCatSheafHom (Fin k)).hom
        (pairedPointSectionValue
          (SheafOfModules.free (R := X.ringCatSheaf) (Fin k))
          (SheafOfModules.ιFree i) x)) = Pi.single i 1 := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  have h : i1_moduleSectionPullback x
      (SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) (SheafOfModules.ιFree i) ≫
      (SheafOfModules.pullbackObjFreeIso x.toRingCatSheafHom (Fin k)).hom =
        SheafOfModules.ιFree (R := (Spec ↧ℂ).ringCatSheaf) i := by
    change ((pullbackUnit x).inv ≫ (Scheme.Modules.pullback x).map
      (SheafOfModules.ιFree i)) ≫
      (SheafOfModules.pullbackObjFreeIso x.toRingCatSheafHom (Fin k)).hom = _
    have hfree : (Scheme.Modules.pullback x).map (SheafOfModules.ιFree i) ≫
        (SheafOfModules.pullbackObjFreeIso x.toRingCatSheafHom (Fin k)).hom =
        (pullbackUnit x).hom ≫ SheafOfModules.ιFree (R := (Spec ↧ℂ).ringCatSheaf) i :=
      SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
        (φ := x.toRingCatSheafHom) i
    rw [Category.assoc, hfree]
    change (pullbackUnit x).inv ≫ (pullbackUnit x).hom ≫ SheafOfModules.ιFree i = _
    rw [Iso.inv_hom_id_assoc]
  have he := congrArg (fun t : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶
      SheafOfModules.free (R := (Spec ↧ℂ).ringCatSheaf) (Fin k) =>
    G.map t (1 : Γ(Spec ↧ℂ, ⊤))) h
  rw [Functor.map_comp] at he
  have hu := congrArg (fun w : G.obj (SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf) =>
    i1_freePointCoordinates k (G.map (SheafOfModules.ιFree i) w)) i1_pointUnitComparison_one
  exact (congrArg (i1_freePointCoordinates k) he).trans
    (hu.symm.trans (i1_freePointCoordinates_generator k i))

#print axioms paired_pointSectionValue_naturality
#print axioms paired_pointSectionValue_pullback
#print axioms paired_pointSectionValue_congr
#print axioms paired_pointSectionValue_zero
#print axioms paired_pointSectionValue_unit
#print axioms paired_pointSectionValue_free_generator
end HodgeLean.Foundations.Program.G32Native
