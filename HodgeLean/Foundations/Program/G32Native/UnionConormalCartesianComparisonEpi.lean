import HodgeLean.Foundations.Program.G32Native.UnionConormalIdealEpi

/-! # Epic conormal comparison for cartesian immersion diagrams -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Natural conormal comparison in a cartesian immersion square is epic. -/
lemma unionConormal_comparison_epi_of_isPullback
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) (g : Q' ⟶ Q) (sq : IsPullback g i' i f) :
    Epi (comparisonMap i i' f g sq.w) := by
  haveI := unionConormal_idealMap_epi_of_isPullback i i' f g sq
  haveI : Epi ((Scheme.Modules.pullback i').map (idealPullbackMap i i' f g sq.w)) :=
    inferInstance
  rw [unionConormal_comparisonMap_eq_prefix]
  infer_instance

end HodgeLean.Foundations.Program.G32Native
