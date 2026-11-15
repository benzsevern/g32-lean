import HodgeLean.Foundations.QuotientDuality.LocalTraceChecks
import HodgeLean.Foundations.Singular.Cup

/-! # Independent tests for the retained middle-duality inputs

The tests perturb the ambient dimension, the cohomology dimension bound,
and the requirement that the trace use a fundamental class on every component.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality.P1bPerfectChecks

/-- A zero-dimensional ambient Euclidean space cannot triangulate two points.
Source: Bochnak–Coste–Roy, Real Algebraic Geometry, Theorem 9.2.1.
HC no distance; AV milestone no distance. -/
theorem p1b_retained_triangulation_falsification
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 0))) :
    ¬ Nonempty (K.space ≃ₜ Fin 2) := by
  rintro ⟨e⟩
  have he : (0 : Fin 2) = 1 := by
    exact e.symm.injective (Subsingleton.elim _ _)
  exact (by decide : (0 : Fin 2) ≠ 1) he

example (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 0))) :
    ¬ Nonempty (K.space ≃ₜ Fin 2) := p1b_retained_triangulation_falsification K

/-- Finite middle cohomology cannot be strengthened to zero middle cohomology.
Source: Hatcher, Algebraic Topology, section 3.1, cohomology of a point.
HC no distance; AV milestone no distance. -/
theorem p1b_retained_finite_falsification :
    ¬ Subsingleton (Cohomology ℚ (TopCat.of Unit) 0) := by
  intro h
  let := h
  exact HodgeLean.Foundations.Singular.unit_ne_zero (R := ℚ) (TopCat.of Unit)
    (Subsingleton.elim _ _)

example : ¬ Subsingleton (Cohomology ℚ (TopCat.of Unit) 0) :=
  p1b_retained_finite_falsification

/-- A nonzero trace class on just one component does not give a perfect pairing.
Source: Bredon, Sheaf Theory, V.9; Hatcher, section 3.3.
HC no distance; AV milestone no distance. -/
theorem p1b_middle_perfect_falsification :
    ∃ (X : TopCat.{0}) (c : Homology ℚ X 0), c ≠ 0 ∧
      ¬ Function.Injective (localTracePairing X 0 0 c) := by
  exact ⟨_, _, LocalTraceChecks.check_local_middle_duality⟩

example := p1b_middle_perfect_falsification

end HodgeLean.Foundations.QuotientDuality.P1bPerfectChecks
