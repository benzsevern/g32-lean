import HodgeLean.Foundations.HodgeGroupAlgebraicDescent

noncomputable section
open MvPolynomial
namespace HodgeLean.Foundations
variable {k : Type*} [Field k] {n : ℕ}

/-- Clearing a common denominator in a polynomial substitution, including
substitutions parametrized by an arbitrary set of admissible points. -/
theorem pel_clear_denominator_substitution {σ τ U : Type*}
    (a : U → σ → k) (b : U → τ → k)
    (D : MvPolynomial σ k) (Q : τ → MvPolynomial σ k)
    (hQ : ∀ u i, eval (a u) (Q i) = eval (a u) D * b u i)
    (f : MvPolynomial τ k) :
    ∃ F : MvPolynomial σ k, ∃ m : ℕ, ∀ u,
      eval (a u) F = eval (a u) D ^ m * eval (b u) f := by
  induction f using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, by intro u; simp⟩
  | add p q hp hq =>
    obtain ⟨P, m, hP⟩ := hp
    obtain ⟨Q', l, hQ'⟩ := hq
    refine ⟨P * D ^ l + Q' * D ^ m, m + l, ?_⟩
    intro u
    simp only [map_add, map_mul, map_pow, hP, hQ', pow_add]
    ring
  | mul_X p i hp =>
    obtain ⟨P, m, hP⟩ := hp
    refine ⟨P * Q i, m + 1, ?_⟩
    intro u
    simp only [map_mul, hP, hQ, eval_X, pow_succ]
    ring

/-- Clearing denominators for a rational map on invertible matrices. -/
theorem pel_clear_denominator
    (D : MvPolynomial (Fin n × Fin n) k)
    (Q : Fin n × Fin n → MvPolynomial (Fin n × Fin n) k)
    (φ : Matrix.GeneralLinearGroup (Fin n) k → Matrix.GeneralLinearGroup (Fin n) k)
    (hQ : ∀ g i, eval (g1_coords g) (Q i) =
      eval (g1_coords g) D * g1_coords (φ g) i)
    (f : MvPolynomial (Fin n × Fin n) k) :
    ∃ F : MvPolynomial (Fin n × Fin n) k, ∃ m : ℕ, ∀ g,
      eval (g1_coords g) F = eval (g1_coords g) D ^ m * eval (g1_coords (φ g)) f :=
  pel_clear_denominator_substitution g1_coords (fun g => g1_coords (φ g)) D Q hQ f

/-- A common polynomial denominator that never vanishes gives Zariski continuity. -/
theorem pel_continuous_of_denominator
    (D : MvPolynomial (Fin n × Fin n) k)
    (Q : Fin n × Fin n → MvPolynomial (Fin n × Fin n) k)
    (φ : Matrix.GeneralLinearGroup (Fin n) k → Matrix.GeneralLinearGroup (Fin n) k)
    (hD : ∀ g, eval (g1_coords g) D ≠ 0)
    (hQ : ∀ g i, eval (g1_coords g) (Q i) =
      eval (g1_coords g) D * g1_coords (φ g) i) :
    @Continuous _ _ (g1_zariski k n) (g1_zariski k n) φ := by
  letI := g1_zariski k n
  apply g2h_continuous_of_poly
  intro f
  obtain ⟨F, m, hF⟩ := pel_clear_denominator D Q φ hQ f
  refine ⟨F, fun g => ?_⟩
  rw [hF, mul_eq_zero]
  simp only [pow_ne_zero m (hD g), false_or]

end HodgeLean.Foundations
