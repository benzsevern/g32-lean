import HodgeLean.Foundations.Program.G32Native.UnionConormalClosedPushforwardEpi

/-! # Recovering epimorphy from transposition and an epic unit -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- For an immersion, an epic pullback unit and epic comparison make its transpose epic. -/
lemma unionConormal_closedTranspose_epi_of_unit
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) (N : X.Modules)
    (v : (Scheme.Modules.pullback f).obj M ⟶ N) [Epi v]
    [Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)] :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ v) := by
  haveI := unionConormal_closedPushforward_epi f v
  rw [Adjunction.homEquiv_unit]
  infer_instance

end HodgeLean.Foundations.Program.G32Native
