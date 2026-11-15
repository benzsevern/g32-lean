import HodgeLean.Foundations.Program.G32Native.PairedConormalFibreRankObstruction

/-! # Actual relation maps under successive scheme pullbacks -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The canonical pullback composition isomorphism detects exactly the same
zero relation map, with the supplied two scheme arrows retained. -/
theorem conormal_pullback_comp_map_eq_zero {X Y Z : Scheme}
    (x : Z ⟶ X) (f : X ⟶ Y) {I A : Y.Modules} (a : I ⟶ A) :
    (Scheme.Modules.pullback x).map ((Scheme.Modules.pullback f).map a) = 0 ↔
      (Scheme.Modules.pullback (x ≫ f)).map a = 0 := by
  let e := Scheme.Modules.pullbackComp x f
  have hn := e.hom.naturality a
  change (Scheme.Modules.pullback x).map ((Scheme.Modules.pullback f).map a) ≫
      e.hom.app A = e.hom.app I ≫ (Scheme.Modules.pullback (x ≫ f)).map a at hn
  constructor
  · intro h
    apply (cancel_epi (e.hom.app I)).mp
    rw [← hn, h, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
  · intro h
    apply (cancel_mono (e.hom.app A)).mp
    rw [hn, h, CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]

end HodgeLean.Foundations.Program.G32Native
