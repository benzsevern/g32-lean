import HodgeLean.Foundations.Program.G32Native.ConormalSectionEqualityNaturality
import HodgeLean.Foundations.Program.G32Native.ConormalIdealPushPullNaturality
import HodgeLean.Foundations.Program.G32Native.OriginalIdealChartSectionNaturality
import HodgeLean.Foundations.TubularEuler.ActualConormalSectionChartHelpers

/-! # The affine chart of the intrinsic original conormal section -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution

/-- The conormal comparison on a commuting source and ambient chart. -/
def conormalSectionChartIso {Q Q' A T : Scheme.{0}}
    (k : Q ⟶ A) (e : Q' ≅ Q) (w : A ≅ T) (f : Q' ⟶ T)
    (hmap : (e.hom ≫ k) ≫ w.hom = f) :
    (Scheme.Modules.pullback e.hom).obj (Conormal.sheaf k) ≅ Conormal.sheaf f :=
  s2e_conormal_source_iso k e ≪≫ (s2e_conormal_target_iso (e.hom ≫ k) w).symm ≪≫
    eqToIso (congrArg Conormal.sheaf hmap)

/-- Transport of the conormal image of an ideal section to ambient coordinates. -/
theorem conormalChartSection_target {Q W W' : Scheme.{0}}
    (j : Q ⟶ W) (e : W ≅ W')
    (s : SheafOfModules.unit.{0} W.ringCatSheaf ⟶ Conormal.idealModule j) :
    i1_module_sectionPullback j (Conormal.idealModule j) s ≫
        (s2e_conormal_target_iso j e).inv =
      i1_module_sectionPullback (j ≫ e.hom) (Conormal.idealModule (j ≫ e.hom))
        (conormalChartIdealSection j e s) := by
  apply (cancel_mono (s2e_conormal_target_iso j e).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (conormalSection_target_iso j e s _ (conormalChartIdealSection_pullback j e s)).symm

/-- The conormal chart carries the image of an ideal section to its transported image. -/
theorem conormalSectionChartIso_section {Q Q' A T : Scheme.{0}}
    (k : Q ⟶ A) (e : Q' ≅ Q) (w : A ≅ T) (f : Q' ⟶ T)
    (hmap : (e.hom ≫ k) ≫ w.hom = f)
    (s : SheafOfModules.unit.{0} A.ringCatSheaf ⟶ Conormal.idealModule k) :
    i1_module_sectionPullback e.hom (Conormal.sheaf k)
        (i1_module_sectionPullback k (Conormal.idealModule k) s) ≫
      (conormalSectionChartIso k e w f hmap).hom =
        i1_module_sectionPullback f (Conormal.idealModule f)
          (transportedIdealChartSection (e.hom ≫ k) w f hmap
            (conormalSourceIdealSection k e s)) := by
  dsimp only [conormalSectionChartIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, conormalSection_source_iso_typed k e s,
    conormalChartSection_target]
  rw [conormalSection_hom_eq _ _ hmap]
  rfl

/-- The specified affine conormal comparison has the commuting-chart construction. -/
theorem originalConormalAffineChartIso_construction
    {Q W : Scheme.{0}} (j : Q ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A)
    (hmap : ((hA.preimage j).isoSpec.inv ≫ (j ∣_ A)) ≫ hA.isoSpec.hom =
      Spec.map (j.app A)) :
    s2e_immersion_affine_chart_conormal_iso j A hA =
      conormalSectionChartIso (j ∣_ A) (hA.preimage j).isoSpec.symm hA.isoSpec
        (Spec.map (j.app A)) hmap := by
  rfl

/-- The conormal image of the original ideal section has the canonical affine equation. -/
theorem originalConormalOpenSection_affine_chart
    {Q W : Scheme.{0}} (j : Q ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom) :
    i1_module_sectionPullback (hA.preimage j).isoSpec.inv (Conormal.sheaf (j ∣_ A))
        (i1_module_sectionPullback (j ∣_ A) (Conormal.idealModule (j ∣_ A))
          (originalIdealOpenSection j A u)) ≫
      (s2e_immersion_affine_chart_conormal_iso j A hA).hom =
        affineConormalSection (W.presheaf.obj (.op A))
          (Q.presheaf.obj (.op (j ⁻¹ᵁ A))) (j.app A) u := by
  have hmap : ((hA.preimage j).isoSpec.inv ≫ (j ∣_ A)) ≫ hA.isoSpec.hom =
      Spec.map (j.app A) :=
    (Category.assoc _ _ _).trans (s2e_closedImmersion_affine_chart_map j A hA)
  rw [originalConormalAffineChartIso_construction j A hA hmap]
  erw [conormalSectionChartIso_section (j ∣_ A) (hA.preimage j).isoSpec.symm
    hA.isoSpec (Spec.map (j.app A)) hmap (originalIdealOpenSection j A u)]
  erw [originalIdealTransportedChartSection_eq j A hA u hmap]
  rfl

end HodgeLean.Foundations.TubularEuler
