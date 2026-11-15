import HodgeLean.Foundations.Program.SchoenTowerT11bGraph

/-! Finite base pieces for constant maps.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A Boolean polynomial description of a specified point of the real line.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, point cells. -/
def s2v_t11b_pointFormula (d : ℝ) : s2v_t11b_Formula 1 :=
  s2v_t11b_zeroFormula (MvPolynomial.X 0 - MvPolynomial.C d)

/-- The point-cell description has precisely its specified real coordinate.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, point cells. -/
theorem s2v_t11b_realize_pointFormula (d t : ℝ) :
    WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (s2v_t11b_pointFormula d).realize ↔ t = d := by
  simp only [s2v_t11b_pointFormula, s2v_t11b_realize_zeroFormula, map_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero]

/-- The fiber over a point is the product model over that point cell.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, point-cell case. -/
def s2v_t11b_pointBaseChart {X : Type*} [TopologicalSpace X]
    (S : Set X) (p : X → ℝ) (d : ℝ) :
    {y : X | y ∈ S ∧ WithLp.toLp 2 (fun _ : Fin 1 => p y) ∈ (s2v_t11b_pointFormula d).realize} ≃ₜ
      ({y : X | y ∈ S ∧ p y = d} ×
        {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (s2v_t11b_pointFormula d).realize}) := by
  letI : Unique {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈
      (s2v_t11b_pointFormula d).realize} :=
    { default := ⟨d, (s2v_t11b_realize_pointFormula d d).mpr rfl⟩
      uniq := fun t => Subtype.ext ((s2v_t11b_realize_pointFormula d t.val).mp t.property) }
  exact (Homeomorph.setCongr (by
    ext y
    simp only [s2v_t11b_realize_pointFormula])).trans (Homeomorph.prodUnique _ _).symm

end HodgeLean.Foundations.Program
