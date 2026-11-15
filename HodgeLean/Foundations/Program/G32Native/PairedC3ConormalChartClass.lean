import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalComparisonSections
import HodgeLean.Foundations.Program.G32Native.PairedC3PullbackSections
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineChartIdealValue

/-! # Canonical conormal classes on an entire affine chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Restriction of the natural conormal comparison to the full chart keeps
the canonical ideal class, including its original ideal pushforward map. -/
theorem paired_c3_conormal_chart_class {Y W : Scheme.{0}}
    (p : Y ⟶ W) (R S : CommRingCat.{0}) (q : R ⟶ S)
    (a : Spec R ⟶ W) (b : Spec S ⟶ Y) (h : b ≫ p = Spec.map q ≫ a)
    (U : W.Opens) (ha : a ⁻¹ᵁ U = ⊤) (hL : (b ≫ p) ⁻¹ᵁ U = ⊤)
    (s : Γ(Conormal.idealModule p, U)) :
    (Conormal.comparisonMap p (Spec.map q) a b h).app ⊤
      (pairedC3ModuleRestrict ((Scheme.Modules.pullback b).obj (Conormal.sheaf p)) hL.ge
        (pairedC3PullbackSection b (Conormal.sheaf p) (p ⁻¹ᵁ U)
          (pairedC3PullbackSection p (Conormal.idealModule p) U s))) =
      pairedC3PullbackSection (Spec.map q) (Conormal.idealModule (Spec.map q)) ⊤
        (pairedC3ModuleRestrict (Conormal.idealModule (Spec.map q)) ha.ge
          ((Conormal.idealPushforwardMap p (Spec.map q) a b h).app U s)) := by
  let z := (Conormal.idealPushforwardMap p (Spec.map q) a b h).app U s
  have hc := paired_c3_conormal_comparison_section p (Spec.map q) a b h U s
  have hi := paired_c3_ideal_pullback_section p (Spec.map q) a b h U s
  have hn := PresheafOfModules.naturality_apply
    (Conormal.comparisonMap p (Spec.map q) a b h).val (homOfLE hL.ge).op
      (pairedC3PullbackSection b (Conormal.sheaf p) (p ⁻¹ᵁ U)
        (pairedC3PullbackSection p (Conormal.idealModule p) U s))
  have hr := congrArg (pairedC3ModuleRestrict (Conormal.sheaf (Spec.map q)) hL.ge) hc
  have hp := paired_c3_pullback_section_restrict (Spec.map q)
    (Conormal.idealModule (Spec.map q)) (a ⁻¹ᵁ U) ⊤ ha.ge z
  apply hn.trans
  apply hr.trans
  rw [paired_c3_module_restrict_comp]
  have hit := congrArg (fun t => pairedC3ModuleRestrict (Conormal.sheaf (Spec.map q))
    (hL.ge.trans (congrArg (fun f : Spec S ⟶ W => f ⁻¹ᵁ U) h).le)
      (pairedC3PullbackSection (Spec.map q) (Conormal.idealModule (Spec.map q)) (a ⁻¹ᵁ U) t)) hi
  exact hit.trans hp.symm

/-- The original canonical conormal class pulled to the entire source chart. -/
def pairedC3ConormalChartSourceClass {Y W Z : Scheme.{0}}
    (p : Y ⟶ W) (b : Z ⟶ Y) (U : W.Opens) (V : Y.Opens)
    (hv : p ⁻¹ᵁ U = V) (hb : b ⁻¹ᵁ V = ⊤) (s : Γ(Conormal.idealModule p, U)) :
    Γ((Scheme.Modules.pullback b).obj (Conormal.sheaf p), ⊤) :=
  pairedC3ModuleRestrict ((Scheme.Modules.pullback b).obj (Conormal.sheaf p)) hb.ge
    (pairedC3PullbackSection b (Conormal.sheaf p) V
      (pairedC3ModuleRestrict (Conormal.sheaf p) hv.ge
        (pairedC3PullbackSection p (Conormal.idealModule p) U s)))

/-- Original source-open restriction commutes with the full affine chart
comparison without changing the represented ideal class. -/
theorem paired_c3_conormal_chart_class_restricted {Y W : Scheme.{0}}
    (p : Y ⟶ W) (R S : CommRingCat.{0}) (q : R ⟶ S)
    (a : Spec R ⟶ W) (b : Spec S ⟶ Y) (h : b ≫ p = Spec.map q ≫ a)
    (U : W.Opens) (V : Y.Opens) (hv : p ⁻¹ᵁ U = V)
    (ha : a ⁻¹ᵁ U = ⊤) (hb : b ⁻¹ᵁ V = ⊤) (s : Γ(Conormal.idealModule p, U)) :
    (Conormal.comparisonMap p (Spec.map q) a b h).app ⊤
      (pairedC3ConormalChartSourceClass p b U V hv hb s) =
      pairedC3PullbackSection (Spec.map q) (Conormal.idealModule (Spec.map q)) ⊤
        (pairedC3AffineChartIdealSection p R S q a b h U ha s) := by
  have hL : (b ≫ p) ⁻¹ᵁ U = ⊤ := by
    change b ⁻¹ᵁ (p ⁻¹ᵁ U) = ⊤
    rw [hv, hb]
  have hn := paired_c3_pullback_section_restrict b (Conormal.sheaf p) (p ⁻¹ᵁ U) V hv.ge
    (pairedC3PullbackSection p (Conormal.idealModule p) U s)
  have hr := congrArg (pairedC3ModuleRestrict ((Scheme.Modules.pullback b).obj (Conormal.sheaf p)) hb.ge) hn
  have hs := paired_c3_module_restrict_comp ((Scheme.Modules.pullback b).obj (Conormal.sheaf p))
    (b.preimage_mono hv.ge) hb.ge
    (pairedC3PullbackSection b (Conormal.sheaf p) (p ⁻¹ᵁ U)
      (pairedC3PullbackSection p (Conormal.idealModule p) U s))
  exact (congrArg (fun z => (Conormal.comparisonMap p (Spec.map q) a b h).app ⊤ z)
    (hr.trans hs)).trans (paired_c3_conormal_chart_class p R S q a b h U ha hL s)

#print axioms paired_c3_conormal_chart_class
end HodgeLean.Foundations.Program.G32Native
