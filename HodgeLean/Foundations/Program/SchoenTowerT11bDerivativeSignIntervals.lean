import HodgeLean.Foundations.Program.SchoenTowerT11bCompactConnectedNeighborhood
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Interval fibers of fixed polynomial derivative inequality patterns.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Fixing a polynomial inequality preserves an interval on which its derivative has a fixed inequality sign.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, derivative-sign interval refinement step. -/
theorem s2v_t11b_derivative_sign_interval_refinement (p : Polynomial ℝ) (T : Set ℝ)
    (hT : T.OrdConnected) (b c : Bool)
    (hb : ∀ x ∈ T, b = true ↔ 0 ≤ p.derivative.eval x) :
    Set.OrdConnected {x : ℝ | x ∈ T ∧ (c = true ↔ 0 ≤ p.eval x)} := by
  have hm : MonotoneOn p.eval T ∨ AntitoneOn p.eval T := by
    cases b
    · right
      apply antitoneOn_of_hasDerivWithinAt_nonpos hT.convex p.continuous.continuousOn
        (fun x _ => (p.hasDerivAt x).hasDerivWithinAt)
      intro x hx
      have hn : ¬ 0 ≤ p.derivative.eval x := fun h => Bool.false_ne_true ((hb x (interior_subset hx)).mpr h)
      exact (lt_of_not_ge hn).le
    · left
      exact monotoneOn_of_hasDerivWithinAt_nonneg hT.convex p.continuous.continuousOn
        (fun x _ => (p.hasDerivAt x).hasDerivWithinAt)
        (fun x hx => (hb x (interior_subset hx)).mp rfl)
  refine ⟨?_⟩
  intro x hx y hy z hz
  have hzT := hT.out hx.1 hy.1 hz
  refine ⟨hzT, ?_⟩
  cases c with
  | false =>
    have hx' : p.eval x < 0 := lt_of_not_ge (fun h => Bool.false_ne_true (hx.2.mpr h))
    have hy' : p.eval y < 0 := lt_of_not_ge (fun h => Bool.false_ne_true (hy.2.mpr h))
    have hz' : p.eval z < 0 := by
      rcases hm with hm | hm
      · exact (hm hzT hy.1 hz.2).trans_lt hy'
      · exact (hm hx.1 hzT hz.1).trans_lt hx'
    exact ⟨fun h => Bool.false_ne_true h |>.elim, fun h => (not_le_of_gt hz' h).elim⟩
  | true =>
    have hz' : 0 ≤ p.eval z := by
      rcases hm with hm | hm
      · exact (hx.2.mp rfl).trans (hm hx.1 hzT hz.1)
      · exact (hy.2.mp rfl).trans (hm hzT hy.1 hz.2)
    exact ⟨fun _ => hz', fun _ => rfl⟩

/-- Fixing all derivative inequality signs through a degree bound gives an actual real interval.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, derivative-sign interval induction step. -/
theorem s2v_t11b_derivative_pattern_ordConnected (k : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ k) (s : ℕ → Bool) :
    Set.OrdConnected {x : ℝ | ∀ j ≤ k,
      s j = true ↔ 0 ≤ ((Polynomial.derivative^[j]) p).eval x} := by
  induction k generalizing p s with
  | zero =>
    refine ⟨?_⟩
    intro x hx y hy z hz j hj
    have hj0 : j = 0 := by omega
    subst j
    have hc := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hp)
    have heval : ∀ t : ℝ, p.eval t = p.coeff 0 := by
      intro t
      simpa only [Polynomial.eval_C] using congrArg (fun q : Polynomial ℝ => q.eval t) hc
    have hx0 := hx 0 (le_refl 0)
    change s 0 = true ↔ 0 ≤ p.eval z
    change s 0 = true ↔ 0 ≤ p.eval x at hx0
    rw [heval] at hx0 ⊢
    exact hx0
  | succ k ih =>
    have hd : p.derivative.natDegree ≤ k := by
      have h := p.natDegree_derivative_le
      omega
    let T : Set ℝ := {x | ∀ j ≤ k,
      s (j + 1) = true ↔ 0 ≤ ((Polynomial.derivative^[j]) p.derivative).eval x}
    have hT : T.OrdConnected := ih p.derivative hd (fun j => s (j + 1))
    have hb : ∀ x ∈ T, s 1 = true ↔ 0 ≤ p.derivative.eval x := by
      intro x hx
      exact hx 0 (Nat.zero_le k)
    have H := s2v_t11b_derivative_sign_interval_refinement p T hT (s 1) (s 0) hb
    have he : {x : ℝ | ∀ j ≤ k + 1,
        s j = true ↔ 0 ≤ ((Polynomial.derivative^[j]) p).eval x} =
        {x : ℝ | x ∈ T ∧ (s 0 = true ↔ 0 ≤ p.eval x)} := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, hx 0 (Nat.zero_le _)⟩
        intro j hj
        simpa only [Function.iterate_succ_apply] using hx (j + 1) (by omega)
      · rintro ⟨ht, h0⟩ j hj
        cases j with
        | zero => exact h0
        | succ j =>
          simpa only [Function.iterate_succ_apply] using ht j (by omega)
    rw [he]
    exact H

/-- Finite derivative inequality tables retain the same interval fibers as the degree-bounded derivative construction.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite derivative table step. -/
theorem s2v_t11b_finite_derivative_pattern_ordConnected (k : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ k) (s : Fin (k + 1) → Bool) :
    Set.OrdConnected {x : ℝ | ∀ j : Fin (k + 1),
      s j = true ↔ 0 ≤ ((Polynomial.derivative^[j.val]) p).eval x} := by
  classical
  let t : ℕ → Bool := fun j => if h : j < k + 1 then s ⟨j, h⟩ else false
  have H := s2v_t11b_derivative_pattern_ordConnected k p hp t
  have he : {x : ℝ | ∀ j ≤ k, t j = true ↔ 0 ≤ ((Polynomial.derivative^[j]) p).eval x} =
      {x : ℝ | ∀ j : Fin (k + 1), s j = true ↔ 0 ≤ ((Polynomial.derivative^[j.val]) p).eval x} := by
    ext x
    constructor
    · intro hx j
      simpa only [t, dif_pos j.isLt] using hx j.val (by omega)
    · intro hx j hj
      have hj' : j < k + 1 := by omega
      simpa only [t, dif_pos hj'] using hx ⟨j, hj'⟩
  rwa [he] at H

/-- Simultaneous specialized derivative inequality patterns of polynomial families have interval fibers even when specialized degrees drop.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, simultaneous derivative fiber step. -/
theorem s2v_t11b_family_derivative_pattern_ordConnected {R ι : Type*} [CommRing R]
    (P : ι → Polynomial R) (a : R →+* ℝ)
    (s : ∀ i, Fin ((P i).natDegree + 1) → Bool) :
    Set.OrdConnected {x : ℝ | ∀ i j,
      s i j = true ↔ 0 ≤ ((Polynomial.derivative^[j.val]) (P i)).eval₂ a x} := by
  have H : ∀ i, Set.OrdConnected {x : ℝ | ∀ j : Fin ((P i).natDegree + 1),
      s i j = true ↔ 0 ≤ ((Polynomial.derivative^[j.val]) (P i)).eval₂ a x} := by
    intro i
    have h := s2v_t11b_finite_derivative_pattern_ordConnected (P i).natDegree
      ((P i).map a) (Polynomial.natDegree_map_le) (s i)
    simpa only [Polynomial.iterate_derivative_map, ← Polynomial.eval₂_eq_eval_map] using h
  refine ⟨?_⟩
  intro x hx y hy z hz i
  exact (H i).out (hx i) (hy i) hz

end HodgeLean.Foundations.Program
