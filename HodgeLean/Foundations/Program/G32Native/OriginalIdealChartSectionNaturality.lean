import HodgeLean.Foundations.Program.G32Native.OriginalIdealChartSourceNaturality
import HodgeLean.Foundations.Program.SchoenCycleC2ImmersionChartMapHelpers

/-! # The original ideal equation through both affine chart isomorphisms -/
noncomputable section
set_option maxHeartbeats 50000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution
open HodgeLean.Foundations.Algebraic

/-- An ideal section transported through a commuting scheme chart. -/
def transportedIdealChartSection {S A T : Scheme.{0}}
    (g : S ⟶ A) (w : A ≅ T) (f : S ⟶ T) (h : g ≫ w.hom = f)
    (r : SheafOfModules.unit.{0} A.ringCatSheaf ⟶ Conormal.idealModule g) :
    SheafOfModules.unit.{0} T.ringCatSheaf ⟶ Conormal.idealModule f :=
  (SheafOfModules.unitToPushforwardObjUnit w.hom.toRingCatSheafHom ≫
    (Scheme.Modules.pushforward w.hom).map r ≫
      (s2e_idealModule_target_pushforward_iso g w).hom) ≫
    (eqToIso (congrArg Conormal.idealModule h)).hom

/-- Transport of an ideal section through a commuting source and ambient chart. -/
theorem idealSection_chart_inclusion {S A T : Scheme.{0}}
    (g : S ⟶ A) (w : A ≅ T) (f : S ⟶ T) (h : g ≫ w.hom = f)
    (r : SheafOfModules.unit.{0} A.ringCatSheaf ⟶ Conormal.idealModule g)
    (c : Γ(A, ⊤))
    (hr : r ≫ conormalIdealInclusion g =
      f5sheaf_scal (X := A) c) :
    transportedIdealChartSection g w f h r ≫ conormalIdealInclusion f =
      f5sheaf_scal (X := T) (w.inv.appTop c) := by
  subst f
  dsimp only [transportedIdealChartSection]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact idealSection_target_transport_scalar g w r c hr

/-- The ideal equation transported through the source and ambient affine charts. -/
def originalIdealChartSection
    {Q W : Scheme.{0}} (j : Q ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom) :
    SheafOfModules.unit.{0} (Spec (W.presheaf.obj (.op A))).ringCatSheaf ⟶
      Conormal.idealModule (Spec.map (j.app A)) := by
  let e := (hA.preimage j).isoSpec.symm
  let g := e.hom ≫ (j ∣_ A)
  let r := conormalSourceIdealSection (j ∣_ A) e (originalIdealOpenSection j A u)
  have hmap : g ≫ hA.isoSpec.hom = Spec.map (j.app A) := by
    simpa only [g, e, Iso.symm_hom, Category.assoc] using
      s2e_closedImmersion_affine_chart_map j A hA
  exact transportedIdealChartSection g hA.isoSpec (Spec.map (j.app A)) hmap r

/-- The chart section has the specified transport formula for any proof of its chart square. -/
theorem originalIdealChartSection_eq_construction
    {Q W : Scheme.{0}} (j : Q ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom)
    (hmap : ((hA.preimage j).isoSpec.inv ≫ (j ∣_ A)) ≫ hA.isoSpec.hom =
      Spec.map (j.app A)) :
    originalIdealChartSection j A hA u =
      transportedIdealChartSection ((hA.preimage j).isoSpec.inv ≫ (j ∣_ A))
        hA.isoSpec (Spec.map (j.app A)) hmap
        (conormalSourceIdealSection (j ∣_ A) (hA.preimage j).isoSpec.symm
          (originalIdealOpenSection j A u)) := by
  rfl

/-- Both affine chart changes retain the original function in inverse ambient coordinates. -/
theorem originalIdealChartSection_transported_scalar
    {Q W : Scheme.{0}} (j : Q ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom) :
    originalIdealChartSection j A hA u ≫ conormalIdealInclusion (Spec.map (j.app A)) =
      f5sheaf_scal (X := Spec (W.presheaf.obj (.op A)))
        (hA.isoSpec.inv.appTop (A.topIso.inv u.val)) := by

  have hmap : ((hA.preimage j).isoSpec.inv ≫ (j ∣_ A)) ≫ hA.isoSpec.hom =
      Spec.map (j.app A) :=
    (Category.assoc _ _ _).trans (s2e_closedImmersion_affine_chart_map j A hA)
  exact (idealSection_inclusion_congr (Spec.map (j.app A))
    (originalIdealChartSection_eq_construction j A hA u hmap)).trans
      (idealSection_chart_inclusion ((hA.preimage j).isoSpec.inv ≫ (j ∣_ A))
        hA.isoSpec (Spec.map (j.app A)) hmap
        (conormalSourceIdealSection (j ∣_ A) (hA.preimage j).isoSpec.symm
          (originalIdealOpenSection j A u))
        (A.topIso.inv u.val) (originalIdealChartSource_scalar j A hA u))

/-- Both affine chart changes retain the original regular function. -/
theorem originalIdealChartSection_inclusion
    {Q W : Scheme.{0}} (j : Q ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom) :
    originalIdealChartSection j A hA u ≫ conormalIdealInclusion (Spec.map (j.app A)) =
      f5sheaf_scal (X := Spec (W.presheaf.obj (.op A)))
        ((Scheme.ΓSpecIso (W.presheaf.obj (.op A))).inv u.val) :=
  (originalIdealChartSection_transported_scalar j A hA u).trans
    (congrArg (f5sheaf_scal (X := Spec (W.presheaf.obj (.op A))))
      (originalIdealOpenSection_affine_scalar j A hA u))

/-- The transported original ideal section equals the canonical affine section. -/
theorem originalIdealChartSection_eq
    {Q W : Scheme.{0}} (j : Q ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom) :
    originalIdealChartSection j A hA u =
      affineIdealModuleSection (W.presheaf.obj (.op A))
        (Q.presheaf.obj (.op (j ⁻¹ᵁ A))) (j.app A) u :=
  affineIdealModuleSection_typed_unique _ _ (j.app A) u (originalIdealChartSection j A hA u)
    (originalIdealChartSection_inclusion j A hA u)

/-- The explicit transported section is the original affine ideal section. -/
theorem originalIdealTransportedChartSection_eq
    {Q W : Scheme.{0}} (j : Q ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A) (u : RingHom.ker (j.app A).hom)
    (hmap : ((hA.preimage j).isoSpec.inv ≫ (j ∣_ A)) ≫ hA.isoSpec.hom =
      Spec.map (j.app A)) :
    transportedIdealChartSection ((hA.preimage j).isoSpec.inv ≫ (j ∣_ A))
        hA.isoSpec (Spec.map (j.app A)) hmap
        (conormalSourceIdealSection (j ∣_ A) (hA.preimage j).isoSpec.symm
          (originalIdealOpenSection j A u)) =
      affineIdealModuleSection (W.presheaf.obj (.op A))
        (Q.presheaf.obj (.op (j ⁻¹ᵁ A))) (j.app A) u :=
  (originalIdealChartSection_eq_construction j A hA u hmap).symm.trans
    (originalIdealChartSection_eq j A hA u)

end HodgeLean.Foundations.TubularEuler
