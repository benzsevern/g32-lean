import HodgeLean.Foundations.Program.G32Native.ModuleSectionRestriction

/-! # Original module maps in local section restriction -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Restriction of original local sections retains every specified
original module morphism. -/
theorem moduleSectionRestrict_naturality {W : Scheme.{0}} {M N : W.Modules}
    (E : M ⟶ N) (U V : W.Opens) (hVU : V ≤ U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj M) :
    moduleSectionRestrict M U V hVU s ≫ (Scheme.Modules.pullback V.ι).map E =
    moduleSectionRestrict N U V hVU (s ≫ (Scheme.Modules.pullback U.ι).map E) := by
  let j := W.homOfLE hVU
  let hk := W.homOfLE_ι hVU
  have hn := (Scheme.Modules.pullbackComp j U.ι).hom.naturality E
  change (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback U.ι).map E) ≫
      (Scheme.Modules.pullbackComp j U.ι).hom.app N =
    (Scheme.Modules.pullbackComp j U.ι).hom.app M ≫
      (Scheme.Modules.pullback (j ≫ U.ι)).map E at hn
  have hg := (Scheme.Modules.pullbackCongr hk).hom.naturality E
  change (Scheme.Modules.pullback (j ≫ U.ι)).map E ≫
      (Scheme.Modules.pullbackCongr hk).hom.app N =
    (Scheme.Modules.pullbackCongr hk).hom.app M ≫
      (Scheme.Modules.pullback V.ι).map E at hg
  unfold moduleSectionRestrict
  simp only [Functor.map_comp, Category.assoc]
  rw [← hg, ← reassoc_of% hn]

#print axioms moduleSectionRestrict_naturality
end HodgeLean.Foundations.Program.G32Native
