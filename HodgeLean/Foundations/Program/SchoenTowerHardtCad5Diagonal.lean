import HodgeLean.Foundations.Program.SchoenTowerHardtCad3FormulaTools
import HodgeLean.Foundations.Program.SchoenTowerT11bGraph

/-! Boolean graphs of coordinate identities. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_diagonal_formula (n : ℕ) :
    ∃ D : s2v_t11b_Formula (n + n),
      ∀ x y : EuclideanSpace ℝ (Fin n),
        WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => y i)) ∈ D.realize ↔ y = x := by
  obtain ⟨D, hD⟩ := s2v_hardt_cad3_finite_inter (fun i : Fin n =>
    s2v_t11b_zeroFormula (MvPolynomial.X (i.castAdd n) - MvPolynomial.X (i.natAdd n)))
  refine ⟨D, ?_⟩
  intro x y
  rw [hD]
  constructor
  · intro h
    ext i
    have hi := (s2v_t11b_realize_zeroFormula _ _).mp (h i)
    have he : x i = y i := by
      simpa only [map_sub, MvPolynomial.eval_X, Fin.append_left, Fin.append_right,
        sub_eq_zero] using hi
    exact he.symm
  · intro h
    subst y
    intro i
    rw [s2v_t11b_realize_zeroFormula]
    simp only [map_sub, MvPolynomial.eval_X, Fin.append_left, Fin.append_right, sub_self]

theorem s2v_hardt_cad5_coordinate_map_graph {n m : ℕ} (r : Fin m → Fin n) :
    ∃ D : s2v_t11b_Formula (n + m),
      ∀ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)),
        WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => y i)) ∈ D.realize ↔
          y = WithLp.toLp 2 (fun j => x (r j)) := by
  obtain ⟨D, hD⟩ := s2v_hardt_cad3_finite_inter (fun i : Fin m =>
    s2v_t11b_zeroFormula (MvPolynomial.X ((r i).castAdd m) - MvPolynomial.X (i.natAdd n)))
  refine ⟨D, ?_⟩
  intro x y
  rw [hD]
  constructor
  · intro h
    ext i
    have hi := (s2v_t11b_realize_zeroFormula _ _).mp (h i)
    have he : x (r i) = y i := by
      simpa only [map_sub, MvPolynomial.eval_X, Fin.append_left, Fin.append_right,
        sub_eq_zero] using hi
    exact he.symm
  · intro h
    subst y
    intro i
    rw [s2v_t11b_realize_zeroFormula]
    simp only [map_sub, MvPolynomial.eval_X, Fin.append_left, Fin.append_right, sub_self]

end HodgeLean.Foundations.Program
