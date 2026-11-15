import HodgeLean.Foundations.Program.G32Native.PairedConormalGeneratorValues
import HodgeLean.Foundations.Program.G32Native.PairedConormalPresentationPullback

/-! # Canonical pullback retains the ordered presentation generators -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Curves.Picard.LineBundles

/-- The canonical unit-plus-free source comparison retains each actual generator. -/
theorem conormal_generator_pullback {X Y : Scheme.{0}} (f : X ⟶ Y)
    (k : ℕ) (r : Fin (k + 1)) :
    conormalPresentationGenerator X k r ≫ (conormalUnitFreePullbackIso f k).inv =
      i1_moduleSectionPullback f
        (SheafOfModules.unit Y.ringCatSheaf ⊞
          SheafOfModules.free (R := Y.ringCatSheaf) (Fin k))
        (conormalPresentationGenerator Y k r) := by
  let F := Scheme.Modules.pullback f
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let u := pullbackUnit f
  let v := SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Fin k)
  have hfree (i : Fin k) : SheafOfModules.ιFree i ≫ v.inv =
      u.inv ≫ F.map (SheafOfModules.ιFree i) := by
    apply (cancel_mono v.hom).mp
    have h : F.map (SheafOfModules.ιFree i) ≫ v.hom =
        u.hom ≫ SheafOfModules.ιFree i :=
      SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
        (φ := f.toRingCatSheafHom) i
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, h,
      Iso.inv_hom_id_assoc]
  induction r using Fin.cases with
  | zero =>
    change biprod.inl ≫
      (biprod.map u.inv v.inv ≫ (F.mapBiprod _ _).inv) = u.inv ≫ F.map biprod.inl
    simp only [biprod.inl_map_assoc,
      CategoryTheory.Functor.mapBiprod_inv, biprod.inl_desc]
  | succ i =>
    change (SheafOfModules.ιFree i ≫ biprod.inr) ≫
      (biprod.map u.inv v.inv ≫ (F.mapBiprod _ _).inv) =
        u.inv ≫ F.map (SheafOfModules.ιFree i ≫ biprod.inr)
    simp only [Category.assoc, biprod.inr_map_assoc,
      CategoryTheory.Functor.mapBiprod_inv, biprod.inr_desc,
      CategoryTheory.Functor.map_comp]
    rw [← Category.assoc, hfree, Category.assoc]

/-- Pulling the supplied quotient retains the pointwise same global generator. -/
theorem conormal_presentation_generator_pullback {X Y : Scheme.{0}} (f : X ⟶ Y)
    (k : ℕ) (M : Y.Modules)
    (π : (SheafOfModules.unit Y.ringCatSheaf ⊞
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin k)) ⟶ M) (r : Fin (k + 1)) :
    conormalPresentationGenerator X k r ≫ conormalPresentationPullback f k M π =
      i1_moduleSectionPullback f M (conormalPresentationGenerator Y k r ≫ π) := by
  rw [conormalPresentationPullback, ← Category.assoc, conormal_generator_pullback,
    i1_moduleSectionPullback_naturality]

#print axioms conormal_presentation_generator_pullback
#print axioms conormal_generator_pullback
end HodgeLean.Foundations.Program.G32Native
