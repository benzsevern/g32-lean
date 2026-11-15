import HodgeLean.Foundations.Program.G32Native.UnionConormalUnitAdjunctionIso
import HodgeLean.Foundations.Program.G32Native.UnionConormalClosedPushforwardEpi
import HodgeLean.Foundations.Program.G32Native.UnionConormalIsoPullbackEquivalence

/-! # Pullback unit epimorphy through scheme isomorphisms -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Unit epimorphy descends through a commuting square whose vertical maps are isomorphisms. -/
lemma unionConormal_unit_epi_of_scheme_isos
    {X Y X' Y' : Scheme.{0}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (b : X' ⟶ X) (j : Y' ⟶ Y) [IsIso b] [IsIso j]
    (h : b ≫ f = f' ≫ j) (M : Y.Modules)
    [Epi ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
      ((Scheme.Modules.pullback j).obj M))] :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  haveI := unionConormal_isoPullback_isEquivalence b
  haveI := unionConormal_isoPullback_isEquivalence j
  let af := Scheme.Modules.pullbackPushforwardAdjunction f
  let af' := Scheme.Modules.pullbackPushforwardAdjunction f'
  let ab := Scheme.Modules.pullbackPushforwardAdjunction b
  let aj := Scheme.Modules.pullbackPushforwardAdjunction j
  haveI : IsIso aj.unit := by dsimp only [aj]; infer_instance
  haveI : IsIso ab.unit := by dsimp only [ab]; infer_instance
  let e : Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward j ≅
      Scheme.Modules.pushforward b ⋙ Scheme.Modules.pushforward f :=
    Scheme.Modules.pushforwardComp f' j ≪≫ Scheme.Modules.pushforwardCongr h.symm ≪≫
      (Scheme.Modules.pushforwardComp b f).symm
  haveI : Epi ((Scheme.Modules.pushforward j).map
      (af'.unit.app ((Scheme.Modules.pullback j).obj M))) :=
    unionConormal_closedPushforward_epi j _
  haveI : Epi ((aj.comp af').unit.app M) := by
    rw [Adjunction.comp_unit_app]
    infer_instance
  have he := unionConormal_unit_epi_of_rightAdjointIso (aj.comp af') (af.comp ab) e M
  rw [Adjunction.comp_unit_app] at he
  exact (epi_comp_iff_of_isIso _
    ((Scheme.Modules.pushforward f).map (ab.unit.app ((Scheme.Modules.pullback f).obj M)))).mp he

end HodgeLean.Foundations.Program.G32Native
