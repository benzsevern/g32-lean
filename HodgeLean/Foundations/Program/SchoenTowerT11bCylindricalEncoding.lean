import HodgeLean.Foundations.Program.SchoenTowerT11bMvRegularBooleanProjection
import HodgeLean.Foundations.Program.SchoenTowerT11bBooleanSections

/-! Cylindrical encoding of actual finite Boolean polynomial formulas.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Separating the first coordinate retains the actual evaluation of a multivariate polynomial.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, cylindrical polynomial encoding step. -/
theorem s2v_t11b_finSucc_family_eval {n : ℕ} (q : MvPolynomial (Fin (n + 1)) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) (x : ℝ) :
    (MvPolynomial.finSuccEquiv ℝ n q).eval₂ (MvPolynomial.eval (fun i => t i)) x =
      MvPolynomial.eval (Fin.cons x (fun i => t i)) q := by
  simpa only [Polynomial.eval₂_eq_eval_map] using
    (MvPolynomial.eval_eq_eval_mv_eval' (fun i => t i) x q).symm

/-- The cylindrical encoding of the product of all nonzero formula atoms is nonzero.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, cylindrical carrier step. -/
theorem s2v_t11b_finSucc_carrier_ne_zero {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    MvPolynomial.finSuccEquiv ℝ n (s2v_t11b_boundaryPolynomial f) ≠ 0 := by
  intro h
  apply s2v_t11b_boundaryPolynomial_ne_zero f
  apply (MvPolynomial.finSuccEquiv ℝ n).injective
  rw [h, map_zero]

/-- Every nonzero formula atom divides its cylindrical carrier polynomial.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, cylindrical carrier step. -/
theorem s2v_t11b_finSucc_atom_dvd_carrier {n : ℕ} (f : s2v_t11b_Formula (n + 1))
    (q : MvPolynomial (Fin (n + 1)) ℝ) (hq : q ∈ f.atoms) (hne : q ≠ 0) :
    MvPolynomial.finSuccEquiv ℝ n q ∣
      MvPolynomial.finSuccEquiv ℝ n (s2v_t11b_boundaryPolynomial f) := by
  classical
  have hdiv : q ∣ s2v_t11b_boundaryPolynomial f :=
    Finset.dvd_prod_of_mem (fun p => p) (Finset.mem_erase.mpr ⟨hne, hq⟩)
  obtain ⟨r, hr⟩ := hdiv
  refine ⟨MvPolynomial.finSuccEquiv ℝ n r, ?_⟩
  exact (congrArg (MvPolynomial.finSuccEquiv ℝ n) hr).trans
    (map_mul (MvPolynomial.finSuccEquiv ℝ n) q r)

end HodgeLean.Foundations.Program
