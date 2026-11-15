import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineComparisonSections
import HodgeLean.Foundations.Program.G32Native.PairedC3LocalModuleComparison

/-! # Original ideal generators in affine chart kernel coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The actual original ideal section transported to the entire affine chart. -/
def pairedC3AffineChartIdealSection {Y W : Scheme.{0}}
    (p : Y ⟶ W) (R S : CommRingCat.{0}) (q : R ⟶ S)
    (a : Spec R ⟶ W) (b : Spec S ⟶ Y) (h : b ≫ p = Spec.map q ≫ a)
    (U : W.Opens) (ha : a ⁻¹ᵁ U = ⊤) (s : Γ(Conormal.idealModule p, U)) :
    Γ(Conormal.idealModule (Spec.map q), ⊤) :=
  pairedC3ModuleRestrict (Conormal.idealModule (Spec.map q)) ha.ge
    ((Conormal.idealPushforwardMap p (Spec.map q) a b h).app U s)

/-- The original ideal generator's affine kernel value is its original
regular function pulled through the chart's structural map. -/
theorem paired_c3_affine_chart_ideal_value {Y W : Scheme.{0}}
    (p : Y ⟶ W) (R S : CommRingCat.{0}) (q : R ⟶ S)
    (a : Spec R ⟶ W) (b : Spec S ⟶ Y) (h : b ≫ p = Spec.map q ≫ a)
    (U : W.Opens) (ha : a ⁻¹ᵁ U = ⊤) (s : Γ(Conormal.idealModule p, U)) :
    (s2e_affine_ideal_sections_equiv R S q
      (pairedC3AffineChartIdealSection p R S q a b h U ha s)).val =
      (Scheme.ΓSpecIso R).hom (a.appLE U ⊤ ha.ge
        (Scheme.Modules.Hom.app (X := W)
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom)) U s)) := by
  let u := Conormal.idealPushforwardMap p (Spec.map q) a b h
  let z := u.app U s
  let j := kernel.ι (SheafOfModules.unitToPushforwardObjUnit (Spec.map q).toRingCatSheafHom)
  have hu := congrArg (fun f => f.app U s)
    (Conormal.idealPushforwardMap_inclusion p (Spec.map q) a b h)
  change Scheme.Modules.Hom.app (X := Spec R) j (a ⁻¹ᵁ U) z = a.app U
    (Scheme.Modules.Hom.app (X := W)
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom)) U s) at hu
  have hn := PresheafOfModules.naturality_apply j.val (homOfLE ha.ge).op z
  have hr := congrArg (fun t => (Spec R).presheaf.map (homOfLE ha.ge).op t) hu
  change (Scheme.ΓSpecIso R).hom
    ((s2e_idealModule_sections_equiv (Spec.map q) ⊤
      (pairedC3ModuleRestrict (Conormal.idealModule (Spec.map q)) ha.ge z)).val) = _
  rw [s2e_idealModule_sections_equiv_coe]
  exact congrArg ((Scheme.ΓSpecIso R).hom) (hn.trans hr)

/-- The same affine value in the original section-kernel coordinates. -/
theorem paired_c3_affine_chart_ideal_section_value {Y W : Scheme.{0}}
    (p : Y ⟶ W) (R S : CommRingCat.{0}) (q : R ⟶ S)
    (a : Spec R ⟶ W) (b : Spec S ⟶ Y) (h : b ≫ p = Spec.map q ≫ a)
    (U : W.Opens) (ha : a ⁻¹ᵁ U = ⊤) (s : Γ(Conormal.idealModule p, U)) :
    (s2e_affine_ideal_sections_equiv R S q
      (pairedC3AffineChartIdealSection p R S q a b h U ha s)).val =
      (Scheme.ΓSpecIso R).hom (a.appLE U ⊤ ha.ge
        (s2e_idealModule_sections_equiv p U s).val) := by
  rw [s2e_idealModule_sections_equiv_coe]
  exact paired_c3_affine_chart_ideal_value p R S q a b h U ha s

#print axioms paired_c3_affine_chart_ideal_value
end HodgeLean.Foundations.Program.G32Native
