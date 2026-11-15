import HodgeLean.Foundations.Program.G32Native.UnionConormalIsoPullbackEquivalence

/-! # Direct image objects under scheme isomorphisms -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Invertible vertical maps identify pullback of direct image with direct image of pullback. -/
def unionConormalIsoPushforwardObjectIso
    {X Y X' Y' : Scheme.{0}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (b : X' ⟶ X) (j : Y' ⟶ Y) [IsIso b] [IsIso j]
    (h : b ≫ f = f' ≫ j) (M : X.Modules) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback b).obj M) := by
  haveI := unionConormal_isoPullback_isEquivalence b
  haveI := unionConormal_isoPullback_isEquivalence j
  let ab := Scheme.Modules.pullbackPushforwardAdjunction b
  let aj := Scheme.Modules.pullbackPushforwardAdjunction j
  haveI : IsIso ab.unit := by dsimp only [ab]; infer_instance
  haveI : IsIso aj.counit := by dsimp only [aj]; infer_instance
  let e : Scheme.Modules.pushforward b ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward j :=
    Scheme.Modules.pushforwardComp b f ≪≫ Scheme.Modules.pushforwardCongr h ≪≫
      (Scheme.Modules.pushforwardComp f' j).symm
  exact (Scheme.Modules.pullback j).mapIso
      ((Scheme.Modules.pushforward f).mapIso (asIso (ab.unit.app M))) ≪≫
    (Scheme.Modules.pullback j).mapIso (e.app ((Scheme.Modules.pullback b).obj M)) ≪≫
    asIso (aj.counit.app ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback b).obj M)))

end HodgeLean.Foundations.Program.G32Native
