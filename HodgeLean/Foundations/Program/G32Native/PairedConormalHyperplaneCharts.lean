import HodgeLean.Foundations.Program.SchoenCycleChartIdeals
import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs

/-! # Actual coordinate equations of the projective hyperplane -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native

/-- The normalized equation of coordinate zero in the supplied projective chart. -/
def paired_hyperplaneChartEquation (k : ℕ) (i : Fin (k + 1)) :
    MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ :=
  if h : (0 : Fin (k + 1)) = i then 1 else MvPolynomial.X ⟨0, h⟩

/-- The actual hyperplane ideal has the normalized coordinate equation on each chart. -/
theorem paired_hyperplane_ideal_chart (k : ℕ) (i : Fin (k + 1)) :
    Ideal.map (Scheme.ΓSpecIso
        ↧(MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)).hom.hom
      (((s2e_hyperplaneIdeal k).comap (s2e_s2b_chart i)).ideal ⟨⊤, isAffineOpen_top _⟩) =
      Ideal.span {paired_hyperplaneChartEquation k i} := by
  change Ideal.map _
    (((s2e_s2b_residueIdeal k 0).comap (s2e_s2b_chart i)).ideal ⟨⊤, isAffineOpen_top _⟩) = _
  rw [s2e_residueIdeal_chart, s2e_chartHom_coordinate]
  rfl

/-- The chart equation is nonzero, including the chart where the hyperplane is absent. -/
theorem paired_hyperplaneChartEquation_ne_zero (k : ℕ) (i : Fin (k + 1)) :
    paired_hyperplaneChartEquation k i ≠ 0 := by
  classical
  unfold paired_hyperplaneChartEquation
  split_ifs
  · exact one_ne_zero
  · exact MvPolynomial.X_ne_zero _

end HodgeLean.Foundations.Program.G32Native
