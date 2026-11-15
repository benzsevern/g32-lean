import HodgeLean.Foundations.Program.SchoenTowerT11bGraphPolynomial
import HodgeLean.Foundations.Program.SchoenTowerT11bIntervals

/-! Boolean membership compatibility along continuous sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Agreement on the signs of all atoms gives agreement on the original Boolean expression.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, sign-decomposition compatibility step. -/
theorem s2v_t11b_formula_membership_of_atom_signs {n : ℕ} (f : s2v_t11b_Formula n)
    (x y : EuclideanSpace ℝ (Fin n))
    (h : ∀ q ∈ f.atoms,
      (0 ≤ MvPolynomial.eval (fun i => x i) q ↔ 0 ≤ MvPolynomial.eval (fun i => y i) q)) :
    x ∈ f.realize ↔ y ∈ f.realize := by
  revert h
  induction f with
  | nonneg q =>
    intro h
    exact h q (Finset.mem_singleton_self q)
  | compl f ih =>
    intro h
    exact not_congr (ih h)
  | inter f g ihf ihg =>
    intro h
    exact and_congr (ihf (fun q hq => h q (Finset.mem_union_left _ hq)))
      (ihg (fun q hq => h q (Finset.mem_union_right _ hq)))

/-- Boolean membership is constant along a connected section whose atoms vanish identically or never vanish.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, sign-invariant section step. -/
theorem s2v_t11b_formula_constant_on_section {n : ℕ} (f : s2v_t11b_Formula n)
    (K : Set ℝ) (hK : IsPreconnected K) (ψ : K → EuclideanSpace ℝ (Fin n))
    (hψ : Continuous ψ)
    (hatoms : ∀ q ∈ f.atoms,
      (∀ t : K, MvPolynomial.eval (fun i => ψ t i) q = 0) ∨
        (∀ t : K, MvPolynomial.eval (fun i => ψ t i) q ≠ 0)) (a b : K) :
    ψ a ∈ f.realize ↔ ψ b ∈ f.realize := by
  haveI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  apply s2v_t11b_formula_membership_of_atom_signs
  intro q hq
  rcases hatoms q hq with hz | hn
  · rw [hz a, hz b]
  · have hc : Continuous (fun t : K => MvPolynomial.eval (fun i => ψ t i) q) :=
      q.continuous_eval.comp ((PiLp.continuous_ofLp 2 _).comp hψ)
    exact s2v_t11b_nonzero_sign Set.univ isPreconnected_univ _ hc.continuousOn
      (fun t _ => hn t) a b (Set.mem_univ a) (Set.mem_univ b)

end HodgeLean.Foundations.Program
