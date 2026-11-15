import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

/-! A smooth chart determines the degree of a local rational orientation. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Topology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem localOrientation_degree_eq_chart_dimension (X : TopCat.{0}) [T1Space X]
    (n : ℕ) (o : LocalRationalOrientation X n) (d : ℕ)
    (e : OpenPartialHomeomorph X (Fin d → ℂ)) (x : X) (hx : x ∈ e.source) :
    n = 2 * d := by
  by_contra h
  haveI := o.vanishes x (2 * d) (Ne.symm h)
  exact localClassOfChart_ne_zero d e x hx (Subsingleton.elim _ _)

#print axioms localOrientation_degree_eq_chart_dimension
end HodgeLean.Foundations.QuotientDuality
