import HodgeLean.Foundations.Program.G32Native.UnionConormalSupIdealEpi

/-! # Epic conormal comparison from the supplied intersection equation -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- The supplied intersection equation makes the actual conormal comparison epic. -/
lemma unionConormal_comparison_epi_of_sup
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) [IsClosedImmersion f] (g : Q' ⟶ Q)
    (h : g ≫ i = i' ≫ f) (hsup : (i' ≫ f).ker = i.ker ⊔ f.ker) :
    Epi (comparisonMap i i' f g h) := by
  haveI := unionConormal_idealMap_epi_of_sup i i' f g h hsup
  haveI : Epi ((Scheme.Modules.pullback i').map (idealPullbackMap i i' f g h)) :=
    inferInstance
  rw [unionConormal_comparisonMap_eq_prefix]
  infer_instance

end HodgeLean.Foundations.Program.G32Native
