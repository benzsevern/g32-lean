import HodgeLean.Foundations.Program.G32Native.PullbackSectionValueTriple

/-! # Original local section values through specified composite equalities -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Actual local section values retain the original unit and section when
the intermediate and final composite maps have specified equalities. -/
theorem pullbackSectionValue_triple_congr {X Y Z T : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (k : Y ⟶ T) (p : X ⟶ T)
    (hk : g ≫ h = k) (hp : f ≫ k = p) (M : T.Modules)
    (s : unit Z ⟶ (Scheme.Modules.pullback h).obj M) :
    (pullbackUnit f).inv ≫ (Scheme.Modules.pullback f).map
      ((pullbackUnit g).inv ≫ (Scheme.Modules.pullback g).map s ≫
        (Scheme.Modules.pullbackComp g h).hom.app M ≫
        (Scheme.Modules.pullbackCongr hk).hom.app M) ≫
      (Scheme.Modules.pullbackComp f k).hom.app M ≫
      (Scheme.Modules.pullbackCongr hp).hom.app M =
    (pullbackUnit (f ≫ g)).inv ≫ (Scheme.Modules.pullback (f ≫ g)).map s ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫
      (Scheme.Modules.pullbackCongr (by rw [Category.assoc, hk]; exact hp)).hom.app M := by
  cases hk
  cases hp
  simpa only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id] using pullbackSectionValue_triple f g h M s

#print axioms pullbackSectionValue_triple_congr
end HodgeLean.Foundations.Program.G32Native
