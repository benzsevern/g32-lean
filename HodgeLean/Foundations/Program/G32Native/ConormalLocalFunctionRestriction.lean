import HodgeLean.Foundations.Program.G32Native.CanonicalConormalEvaluation
import HodgeLean.Foundations.Program.G32Native.ModuleSectionRestrictionNaturality
import HodgeLean.Foundations.Program.G32Native.ModuleSectionRestrictionUnit
import HodgeLean.Foundations.Program.G32Native.OpenTopSectionRestriction
import HodgeLean.Foundations.Curves.Picard.LineBundles.PullbackScalars

/-! # Original local ideal functions under ambient open restriction -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Restriction of an original local ideal section retains exactly the
original regular function under the actual ambient ring restriction. -/
theorem conormalLocalFunction_restrict {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    (U V : W.left.Opens) (hVU : V ≤ U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) :
    conormalLocalFunction i V (moduleSectionRestrict (Conormal.idealModule i.left) U V hVU s) =
      W.left.presheaf.map (homOfLE hVU).op (conormalLocalFunction i U s) := by
  let M := Conormal.idealModule i.left
  let sV := moduleSectionRestrict M U V hVU s
  let j := W.left.homOfLE hVU
  let a := s ≫ (Scheme.Modules.pullback U.ι).map (conormalIdealInclusion i.left) ≫
    (pullbackUnit U.ι).hom
  have hm : sV ≫ (Scheme.Modules.pullback V.ι).map (conormalIdealInclusion i.left) ≫
      (pullbackUnit V.ι).hom =
    (pullbackUnit j).inv ≫ (Scheme.Modules.pullback j).map a ≫ (pullbackUnit j).hom := by
    change (moduleSectionRestrict M U V hVU s ≫
      (Scheme.Modules.pullback V.ι).map (conormalIdealInclusion i.left)) ≫
        (pullbackUnit V.ι).hom = _
    rw [moduleSectionRestrict_naturality, moduleSectionRestrict_structure] <;> rfl
  have hc : ((pullbackUnit j).inv ≫ (Scheme.Modules.pullback j).map a ≫ (pullbackUnit j).hom).val.app
      (op ⊤) (1 : Γ(V.toScheme, ⊤)) =
    j.appTop (a.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤))) :=
      pullbackUnitEnd_coefficient j a ⊤
  have hd := congrArg (fun f : Γ(U.toScheme, ⊤) ⟶ Γ(W.left, V) =>
    f (a.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤))))
      (openTopIso_restriction W.left U V hVU)
  change V.topIso.hom ((sV ≫ (Scheme.Modules.pullback V.ι).map (conormalIdealInclusion i.left) ≫
    (pullbackUnit V.ι).hom).val.app (op ⊤) (1 : Γ(V.toScheme, ⊤))) =
    W.left.presheaf.map (homOfLE hVU).op (U.topIso.hom (a.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤))))
  rw [hm, hc]
  exact hd.symm

#print axioms conormalLocalFunction_restrict
end HodgeLean.Foundations.Program.G32Native
