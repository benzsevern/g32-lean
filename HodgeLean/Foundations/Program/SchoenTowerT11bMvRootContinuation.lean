import HodgeLean.Foundations.Program.SchoenTowerT11bCoefficientTriviality
import HodgeLean.Foundations.Program.SchoenTowerT11bMvParameterRoots
import Mathlib.Algebra.MvPolynomial.Funext

/-! Ordered roots of actual polynomial families in every Euclidean parameter dimension.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Evaluating multivariate polynomials on all Euclidean parameters loses no coefficient information.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, parameter-polynomial encoding step. -/
theorem s2v_t11b_mv_coefficient_evaluation_injective {n : ℕ} :
    Function.Injective (RingHom.pi (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i))) := by
  intro p q h
  apply MvPolynomial.funext
  intro z
  have hz := congrFun h (WithLp.toLp 2 z)
  simpa only [RingHom.pi_apply] using hz

/-- The functional coefficient encoding retains the evaluated leading coefficient of the original family.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, parameter degree-preservation step. -/
theorem s2v_t11b_mvParameterPolynomial_leadingCoeff {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) (a : EuclideanSpace ℝ (Fin n)) :
    (s2v_t11b_mvParameterPolynomial P).leadingCoeff a =
      MvPolynomial.eval (fun i => a i) P.leadingCoeff := by
  simp only [s2v_t11b_mvParameterPolynomial,
    Polynomial.leadingCoeff_map_of_injective s2v_t11b_mv_coefficient_evaluation_injective,
    RingHom.pi_apply]

/-- Actual multivariate polynomial families have globally continuous ordered roots on connected simple degree-preserving regions.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional ordered-root continuation step. -/
theorem s2v_t11b_mv_parameter_ordered_sections {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsPreconnected K) (a : K)
    (hlead : ∀ t ∈ K, MvPolynomial.eval (fun i => t i) P.leadingCoeff ≠ 0)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, P.eval₂ (MvPolynomial.eval (fun i => t i)) x = 0 →
      (P.map (MvPolynomial.eval (fun i => t i))).derivative.eval x ≠ 0) :
    ∃ m : ℕ, ∃ ψ : Fin m → K → ℝ,
      (∀ i, Continuous (ψ i)) ∧ (∀ t, StrictMono (fun i => ψ i t)) ∧
      ∀ t : K, ∀ x : ℝ,
        P.eval₂ (MvPolynomial.eval (fun i => t.val i)) x = 0 ↔ ∃ i, x = ψ i t := by
  have hl : ∀ t ∈ K, (s2v_t11b_mvParameterPolynomial P).leadingCoeff t ≠ 0 := by
    intro t ht
    rw [s2v_t11b_mvParameterPolynomial_leadingCoeff]
    exact hlead t ht
  have hs : ∀ t ∈ K, ∀ x : ℝ,
      (s2v_t11b_mvParameterPolynomial P).eval₂
        (Pi.evalRingHom (fun _ : EuclideanSpace ℝ (Fin n) => ℝ) t) x = 0 →
      ((s2v_t11b_mvParameterPolynomial P).map
        (Pi.evalRingHom (fun _ : EuclideanSpace ℝ (Fin n) => ℝ) t)).derivative.eval x ≠ 0 := by
    intro t ht x hx
    rw [s2v_t11b_mvParameterPolynomial_specialize]
    apply hsimple t ht x
    rwa [s2v_t11b_mvParameterPolynomial_eval] at hx
  obtain ⟨m, ψ, hc, hm, hr⟩ := s2v_t11b_smooth_coefficient_ordered_sections
    (s2v_t11b_mvParameterPolynomial P) (s2v_t11b_mvParameterPolynomial_coeff_contDiff P) K hK a hl hs
  refine ⟨m, ψ, hc, hm, ?_⟩
  intro t x
  simpa only [s2v_t11b_mvParameterPolynomial_eval] using hr t x

/-- Increasing real root sections give product coordinates over a connected parameter set.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, ordered-section assembly step. -/
theorem s2v_t11b_mv_parameter_connected_triviality {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsPreconnected K) (a : K)
    (hlead : ∀ t ∈ K, MvPolynomial.eval (fun i => t i) P.leadingCoeff ≠ 0)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, P.eval₂ (MvPolynomial.eval (fun i => t i)) x = 0 →
      (P.map (MvPolynomial.eval (fun i => t i))).derivative.eval x ≠ 0) :
    ∃ e : ({x : ℝ | P.eval₂ (MvPolynomial.eval (fun i => a.val i)) x = 0} × K) ≃ₜ
      {z : K × ℝ | P.eval₂ (MvPolynomial.eval (fun i => z.1.val i)) z.2 = 0},
      ∀ y, (e y).val.1 = y.2 := by
  classical
  obtain ⟨m, ψ, hc, hmono, hroots⟩ :=
    s2v_t11b_mv_parameter_ordered_sections P K hK a hlead hsimple
  let R := {x : ℝ | P.eval₂ (MvPolynomial.eval (fun i => a.val i)) x = 0}
  let idx : Fin m → R := fun i => ⟨ψ i a, (hroots a _).mpr ⟨i, rfl⟩⟩
  have hidx : Function.Bijective idx := by
    constructor
    · intro i j hij
      exact (hmono a).injective (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, hi⟩ := (hroots a x.val).mp x.property
      exact ⟨i, Subtype.ext hi.symm⟩
  let rootEquiv : Fin m ≃ₜ R := (Equiv.ofBijective idx hidx).toHomeomorphOfContinuousClosed
    continuous_of_discreteTopology (fun A _ => ((Set.toFinite A).image idx).isClosed)
  let e₀ := s2v_t11b_finite_graph_homeomorph ψ hc (fun t => (hmono t).injective)
  have hsets : {z : K × ℝ | ∃ i, z.2 = ψ i z.1} =
      {z : K × ℝ | P.eval₂ (MvPolynomial.eval (fun i => z.1.val i)) z.2 = 0} := by
    ext z
    exact (hroots z.1 z.2).symm
  let e := ((rootEquiv.symm.prodCongr (Homeomorph.refl K)).trans e₀).trans
    (Homeomorph.setCongr hsets)
  refine ⟨e, ?_⟩
  intro y
  exact congrArg Prod.fst
    (s2v_t11b_finite_graph_homeomorph_apply ψ hc (fun t => (hmono t).injective)
      (rootEquiv.symm y.1) y.2)

end HodgeLean.Foundations.Program
