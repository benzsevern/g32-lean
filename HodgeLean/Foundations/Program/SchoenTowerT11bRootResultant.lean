import HodgeLean.Foundations.Program.SchoenTowerT11bSimpleTriviality
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! Exceptional parameter polynomials for common roots and multiple roots.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A common specialized root forces the parameter resultant to vanish.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, projection-polynomial step. -/
theorem s2v_t11b_family_common_root_resultant
    (P Q : Polynomial (Polynomial ℝ))
    (hdegree : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) (t x : ℝ)
    (hP : P.eval₂ (Polynomial.evalRingHom t) x = 0)
    (hQ : Q.eval₂ (Polynomial.evalRingHom t) x = 0) :
    (P.resultant Q).eval t = 0 := by
  obtain ⟨A, B, _, _, h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant P Q
    le_rfl le_rfl hdegree
  have he := congrArg
    (fun S : Polynomial (Polynomial ℝ) => S.eval₂ (Polynomial.evalRingHom t) x) h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    hP, hQ, zero_mul, zero_add] at he
  exact he.symm

/-- Away from the derivative resultant, all specialized real roots are simple.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, projection-polynomial step. -/
theorem s2v_t11b_simple_roots_of_resultant_ne_zero
    (P : Polynomial (Polynomial ℝ)) (hdegree : P.natDegree ≠ 0) (a : ℝ)
    (hresultant : (P.resultant P.derivative).eval a ≠ 0) :
    ∀ x : ℝ, P.eval₂ (Polynomial.evalRingHom a) x = 0 →
      (P.map (Polynomial.evalRingHom a)).derivative.eval x ≠ 0 := by
  intro x hx hdx
  have hd : P.derivative.eval₂ (Polynomial.evalRingHom a) x = 0 := by
    simpa only [Polynomial.eval₂_eq_eval_map, Polynomial.derivative_map] using hdx
  exact hresultant (s2v_t11b_family_common_root_resultant P P.derivative
    (Or.inl hdegree) a x hx hd)

/-- The derivative resultant supplies a finite exceptional set outside which actual-fiber local charts exist.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, projection-polynomial step. -/
theorem s2v_t11b_monic_family_finite_exceptional_values
    (P : Polynomial (Polynomial ℝ)) (hP : P.Monic) (hdegree : P.natDegree ≠ 0)
    (hresultant : P.resultant P.derivative ≠ 0) :
    ∃ s : Finset ℝ, ∀ a : ℝ, a ∉ s →
      ∃ ε : ℝ, 0 < ε ∧ ∃ e :
        ({x : ℝ | P.eval₂ (Polynomial.evalRingHom a) x = 0} × Metric.ball a ε) ≃ₜ
        {z : Metric.ball a ε × ℝ | P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0},
        ∀ y, (e y).val.1 = y.2 := by
  classical
  refine ⟨(P.resultant P.derivative).roots.toFinset, ?_⟩
  intro a ha
  have hres : (P.resultant P.derivative).eval a ≠ 0 := fun hz =>
    ha (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hresultant).mpr hz))
  exact s2v_t11b_monic_simple_fiber_triviality P hP a
    (s2v_t11b_simple_roots_of_resultant_ne_zero P hdegree a hres)

end HodgeLean.Foundations.Program
