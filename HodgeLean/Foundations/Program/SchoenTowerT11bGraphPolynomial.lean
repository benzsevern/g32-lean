import HodgeLean.Foundations.Program.SchoenTowerT11bGraphInterior

/-! Nonzero polynomial carriers extracted from Boolean graph descriptions.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Multiply the nonzero atoms of a Boolean polynomial expression.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, boundary-polynomial step. -/
def s2v_t11b_boundaryPolynomial {n : ℕ} (f : s2v_t11b_Formula n) :
    MvPolynomial (Fin n) ℝ :=
  ∏ p ∈ f.atoms.erase 0, p

/-- The polynomial extracted from the nonzero atoms is itself nonzero.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, boundary-polynomial step. -/
theorem s2v_t11b_boundaryPolynomial_ne_zero {n : ℕ} (f : s2v_t11b_Formula n) :
    s2v_t11b_boundaryPolynomial f ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (Finset.mem_erase.mp hp).1

/-- The extracted polynomial vanishes on every member of a realization with empty interior.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, boundary-polynomial step. -/
theorem s2v_t11b_boundaryPolynomial_zero_on {n : ℕ} (f : s2v_t11b_Formula n)
    (hinterior : interior f.realize = ∅) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ f.realize) :
    MvPolynomial.eval (fun i => x i) (s2v_t11b_boundaryPolynomial f) = 0 := by
  classical
  have hxi : x ∉ interior f.realize := by
    rw [hinterior]
    simp only [Set.mem_empty_iff_false, not_false_eq_true]
  obtain ⟨p, hp, hn, hz⟩ := s2v_t11b_boundary_active_atom f x hx hxi
  rw [s2v_t11b_boundaryPolynomial, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hn, hp⟩) hz

/-- Every Boolean polynomial graph is contained in a specified nonzero polynomial zero set.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, graph-carrier step. -/
theorem s2v_t11b_graph_polynomial_carrier {n : ℕ} (f : s2v_t11b_Formula n)
    (p : EuclideanSpace ℝ (Fin n) → ℝ) (g : s2v_t11b_Formula (n + 1))
    (hg : ∀ z : EuclideanSpace ℝ (Fin (n + 1)), z ∈ g.realize ↔
      WithLp.toLp 2 (fun i : Fin n => z i.castSucc) ∈ f.realize ∧
        z (Fin.last n) = p (WithLp.toLp 2 (fun i : Fin n => z i.castSucc))) :
    s2v_t11b_boundaryPolynomial g ≠ 0 ∧
      ∀ z ∈ g.realize,
        MvPolynomial.eval (fun i => z i) (s2v_t11b_boundaryPolynomial g) = 0 := by
  refine ⟨s2v_t11b_boundaryPolynomial_ne_zero g, ?_⟩
  intro z hz
  exact s2v_t11b_boundaryPolynomial_zero_on g
    (s2v_t11b_graph_realize_empty_interior f p g hg) z hz

end HodgeLean.Foundations.Program
