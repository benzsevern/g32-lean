import HodgeLean.Foundations.Program.SchoenTowerT11bSmoothCoefficientRoots

/-! Smooth polynomial root families with Euclidean parameters of arbitrary dimension.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every real multivariate polynomial is smooth on its actual Euclidean parameter space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional coefficient smoothness step. -/
theorem s2v_t11b_mv_parameter_eval_contDiff {n : ℕ} (q : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) q) := by
  induction q using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (contDiff_const : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun _ : EuclideanSpace ℝ (Fin n) => c))
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p i hp =>
    have hi : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : EuclideanSpace ℝ (Fin n) => x i) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).contDiff
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul hi

/-- Evaluate multivariate coefficient polynomials as actual functions on the Euclidean parameter space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional coefficient encoding step. -/
def s2v_t11b_mvParameterPolynomial {n : ℕ} (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    Polynomial (EuclideanSpace ℝ (Fin n) → ℝ) :=
  P.map (RingHom.pi (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i)))

/-- Every encoded coefficient of the actual multivariate family is smooth.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional coefficient encoding step. -/
theorem s2v_t11b_mvParameterPolynomial_coeff_contDiff {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) (i : ℕ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) ((s2v_t11b_mvParameterPolynomial P).coeff i) := by
  have heq : (s2v_t11b_mvParameterPolynomial P).coeff i =
      (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => x j) (P.coeff i)) := by
    funext x
    simp only [s2v_t11b_mvParameterPolynomial, Polynomial.coeff_map, RingHom.pi_apply]
  rw [heq]
  exact s2v_t11b_mv_parameter_eval_contDiff (P.coeff i)

/-- Specializing the functional coefficient encoding retains the actual polynomial of the chosen parameter fiber.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional coefficient specialization step. -/
theorem s2v_t11b_mvParameterPolynomial_specialize {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) (a : EuclideanSpace ℝ (Fin n)) :
    (s2v_t11b_mvParameterPolynomial P).map
      (Pi.evalRingHom (fun _ : EuclideanSpace ℝ (Fin n) => ℝ) a) =
      P.map (MvPolynomial.eval (fun i => a i)) := by
  simp only [s2v_t11b_mvParameterPolynomial, Polynomial.map_map]
  apply congrArg (fun f : MvPolynomial (Fin n) ℝ →+* ℝ => P.map f)
  apply RingHom.ext
  intro q
  simp only [RingHom.comp_apply, Pi.evalRingHom_apply, RingHom.pi_apply]

/-- The Euclidean coefficient encoding retains the original joint polynomial evaluation.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional evaluation compatibility step. -/
theorem s2v_t11b_mvParameterPolynomial_eval {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) (a : EuclideanSpace ℝ (Fin n)) (x : ℝ) :
    (s2v_t11b_mvParameterPolynomial P).eval₂
      (Pi.evalRingHom (fun _ : EuclideanSpace ℝ (Fin n) => ℝ) a) x =
      P.eval₂ (MvPolynomial.eval (fun i => a i)) x := by
  simpa only [Polynomial.eval₂_eq_eval_map] using congrArg (fun q : Polynomial ℝ => q.eval x)
    (s2v_t11b_mvParameterPolynomial_specialize P a)

/-- Actual multivariate parameter polynomials have local projection charts at every simple real fiber root.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional polynomial root projection step. -/
theorem s2v_t11b_mv_parameter_simple_root_projection_chart {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) (a : EuclideanSpace ℝ (Fin n)) (b : ℝ)
    (hroot : P.eval₂ (MvPolynomial.eval (fun i => a i)) b = 0)
    (hsimple : (P.map (MvPolynomial.eval (fun i => a i))).derivative.eval b ≠ 0) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ e : Metric.ball a ε ≃ₜ
      {z : EuclideanSpace ℝ (Fin n) × ℝ | z.1 ∈ Metric.ball a ε ∧ z.2 ∈ Metric.ball b δ ∧
        P.eval₂ (MvPolynomial.eval (fun i => z.1 i)) z.2 = 0},
      ∀ t, (e t).val.1 = t.val := by
  have hr := (s2v_t11b_mvParameterPolynomial_eval P a b).trans hroot
  have hs : ((s2v_t11b_mvParameterPolynomial P).map
      (Pi.evalRingHom (fun _ : EuclideanSpace ℝ (Fin n) => ℝ) a)).derivative.eval b ≠ 0 := by
    rw [s2v_t11b_mvParameterPolynomial_specialize]
    exact hsimple
  obtain ⟨ε, δ, hε, hδ, e, he⟩ :=
    s2v_t11b_smooth_coefficient_root_projection_chart (s2v_t11b_mvParameterPolynomial P)
      (s2v_t11b_mvParameterPolynomial_coeff_contDiff P) a b hr hs
  have hset : {z : EuclideanSpace ℝ (Fin n) × ℝ | z.1 ∈ Metric.ball a ε ∧ z.2 ∈ Metric.ball b δ ∧
      (s2v_t11b_mvParameterPolynomial P).eval₂
        (Pi.evalRingHom (fun _ : EuclideanSpace ℝ (Fin n) => ℝ) z.1) z.2 = 0} =
      {z : EuclideanSpace ℝ (Fin n) × ℝ | z.1 ∈ Metric.ball a ε ∧ z.2 ∈ Metric.ball b δ ∧
        P.eval₂ (MvPolynomial.eval (fun i => z.1 i)) z.2 = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, s2v_t11b_mvParameterPolynomial_eval]
  refine ⟨ε, δ, hε, hδ, e.trans (Homeomorph.setCongr hset), ?_⟩
  intro t
  exact he t

end HodgeLean.Foundations.Program
