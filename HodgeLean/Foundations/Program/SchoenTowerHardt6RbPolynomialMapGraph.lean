import HodgeLean.Foundations.Program.SchoenTowerHardtCad3FormulaTools

/-! Actual Boolean graph equations for maps with prescribed polynomial coordinates. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_polynomial_map_graph {n q : ℕ}
    (P : Fin q → MvPolynomial (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (hf : ∀ x i, f x i = MvPolynomial.eval (fun j => x j) (P i)) :
    ∃ G : s2v_t11b_Formula (n + q), ∀ z, z ∈ G.realize ↔
      ∃ x : EuclideanSpace ℝ (Fin n),
        (∀ i, z (Fin.castAdd q i) = x i) ∧
        (∀ i, z (Fin.natAdd n i) = f x i) := by
  let E : Fin q → s2v_t11b_Formula (n + q) := fun i =>
    s2v_t11b_zeroFormula (MvPolynomial.X (Fin.natAdd n i) -
      MvPolynomial.rename (Fin.castAdd q) (P i))
  obtain ⟨G, hG⟩ := s2v_hardt_cad3_finite_inter E
  refine ⟨G, ?_⟩
  intro z
  have hE : ∀ i, z ∈ (E i).realize ↔ z (Fin.natAdd n i) =
      MvPolynomial.eval (fun j => z (Fin.castAdd q j)) (P i) := by
    intro i
    rw [s2v_t11b_realize_zeroFormula]
    simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_rename, sub_eq_zero]
    rfl
  rw [hG]
  simp_rw [hE]
  constructor
  · intro hz
    let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => z (Fin.castAdd q i))
    exact ⟨x, fun _ => rfl, fun i => (hz i).trans (hf x i).symm⟩
  · rintro ⟨x, hx, hy⟩ i
    rw [hy i, hf]
    have he : (fun j => x j) = (fun j => z (Fin.castAdd q j)) :=
      funext fun j => (hx j).symm
    rw [he]

end HodgeLean.Foundations.Program
