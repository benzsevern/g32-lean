import HodgeLean.Foundations.Program.G32Native.ModuleSectionValueFactorization
import HodgeLean.Foundations.Program.G32Native.PullbackSectionValueCongr

/-! # Restriction of original local module section morphisms -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Restrict an original local section using the actual open morphism,
pullback-composition map and original structure-module unit. -/
def moduleSectionRestrict {W : Scheme.{0}} (M : W.Modules)
    (U V : W.Opens) (hVU : V ≤ U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj M) :
    unit V.toScheme ⟶ (Scheme.Modules.pullback V.ι).obj M :=
  (pullbackUnit (W.homOfLE hVU)).inv ≫
    (Scheme.Modules.pullback (W.homOfLE hVU)).map s ≫
    (Scheme.Modules.pullbackComp (W.homOfLE hVU) U.ι).hom.app M ≫
    (Scheme.Modules.pullbackCongr (W.homOfLE_ι hVU)).hom.app M

/-- Restricting the original local module section to a smaller ambient
open retains its value at every original point of that smaller open. -/
theorem moduleSectionValue_restrict {W : Over (Spec ↧ℂ)} (M : W.left.Modules)
    (U V : W.left.Opens) (hVU : V ≤ U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (p : ComplexPoint W) (hpV : p ∈ Point.overOpen V) :
    moduleSectionValue M V (moduleSectionRestrict M U V hVU s) p hpV =
      moduleSectionValue M U s p (hVU hpV) := by
  let f := liftToOpen W V p hpV
  let g := W.left.homOfLE hVU
  have hf : f ≫ V.ι = p.left := liftToOpen_fac W V p hpV
  have hg : g ≫ U.ι = V.ι := W.left.homOfLE_ι hVU
  have hfU : (f ≫ g) ≫ U.ι = p.left := by rw [Category.assoc, hg]; exact hf
  have h := pullbackSectionValue_triple_congr f g U.ι V.ι p.left hg hf M s
  have hv := congrArg (fun a : unit (Spec ↧ℂ) ⟶ (Scheme.Modules.pullback p.left).obj M =>
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map a (1 : Γ(Spec ↧ℂ, ⊤))) h
  exact (moduleSectionValue_factorization M V (moduleSectionRestrict M U V hVU s)
    p hpV f hf).symm.trans
      (hv.trans (moduleSectionValue_factorization M U s p (hVU hpV) (f ≫ g) hfU))

#print axioms moduleSectionValue_restrict
#print axioms moduleSectionRestrict
end HodgeLean.Foundations.Program.G32Native
