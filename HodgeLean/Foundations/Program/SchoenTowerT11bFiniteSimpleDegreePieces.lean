import HodgeLean.Foundations.Program.SchoenTowerT11bFiniteSquarefreeRepresentatives
import HodgeLean.Foundations.Program.SchoenTowerT11bDegreeStratumRoots

/-! Finite Boolean pieces with simple representatives of constant actual spatial degree.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every nonzero specialized fiber lies on a finite Boolean piece with a simple polynomial representative of fixed actual degree and identical real roots.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite simple degree-piece construction step. -/
theorem s2v_t11b_finite_simple_degree_pieces {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      ∃ H : Fin m → Polynomial (MvPolynomial (Fin n) ℝ), ∃ d : Fin m → ℕ,
      (∀ t : EuclideanSpace ℝ (Fin n), P.map (MvPolynomial.eval (fun j => t j)) ≠ 0 →
        ∃ i, t ∈ (c i).realize) ∧
      ∀ i t, t ∈ (c i).realize →
        P.map (MvPolynomial.eval (fun j => t j)) ≠ 0 ∧
        (H i).map (MvPolynomial.eval (fun j => t j)) ≠ 0 ∧
        ((H i).map (MvPolynomial.eval (fun j => t j))).natDegree = d i ∧
        (∀ x : ℝ, (H i).eval₂ (MvPolynomial.eval (fun j => t j)) x = 0 ↔
          P.eval₂ (MvPolynomial.eval (fun j => t j)) x = 0) ∧
        (∀ x : ℝ, (H i).eval₂ (MvPolynomial.eval (fun j => t j)) x = 0 →
          ((H i).map (MvPolynomial.eval (fun j => t j))).derivative.eval x ≠ 0) := by
  classical
  obtain ⟨m, c, H, hcover, hH⟩ := s2v_t11b_finite_squarefree_representatives P
  let J := (i : Fin m) × Fin ((H i).natDegree + 1)
  let E := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J,
    fun j => .inter (c (E j).1) (s2v_t11b_degreeFormula (H (E j).1) (some (E j).2)),
    fun j => H (E j).1, fun j => (E j).2.val, ?_, ?_⟩
  · intro t hp
    obtain ⟨i, hi⟩ := hcover t
    have hn : (H i).map (MvPolynomial.eval (fun j => t j)) ≠ 0 :=
      fun hz => hp ((hH i t hi).1.mp hz)
    let d : Fin ((H i).natDegree + 1) :=
      ⟨((H i).map (MvPolynomial.eval (fun j => t j))).natDegree,
        Nat.lt_succ_of_le Polynomial.natDegree_map_le⟩
    have hd := (s2v_t11b_degreeFormula_some (H i) d t).mpr ⟨hn, rfl⟩
    refine ⟨E.symm ⟨i, d⟩, ?_⟩
    change t ∈ (c (E (E.symm (⟨i, d⟩ : J))).1).realize ∧
      t ∈ (s2v_t11b_degreeFormula (H (E (E.symm (⟨i, d⟩ : J))).1)
        (some (E (E.symm (⟨i, d⟩ : J))).2)).realize
    rw [E.apply_symm_apply]
    exact ⟨hi, hd⟩
  · intro j t ht
    obtain ⟨hn, hd⟩ := (s2v_t11b_degreeFormula_some (H (E j).1) (E j).2 t).mp ht.2
    have hp : P.map (MvPolynomial.eval (fun j => t j)) ≠ 0 :=
      fun hz => hn ((hH (E j).1 t ht.1).1.mpr hz)
    exact ⟨hp, hn, hd, (hH (E j).1 t ht.1).2.1, (hH (E j).1 t ht.1).2.2 hp⟩


/-- Arbitrary nonzero polynomial fibers have continuous ordered real roots on connected subsets of a constructed finite Boolean cover, without an original simplicity premise.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite-piece root continuation step. -/
theorem s2v_t11b_finite_pieces_ordered_roots {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ t : EuclideanSpace ℝ (Fin n), P.map (MvPolynomial.eval (fun j => t j)) ≠ 0 →
        ∃ i, t ∈ (c i).realize) ∧
      ∀ i (K : Set (EuclideanSpace ℝ (Fin n))), K ⊆ (c i).realize → IsPreconnected K → ∀ a : K,
        ∃ r : ℕ, ∃ ψ : Fin r → K → ℝ,
          (∀ j, Continuous (ψ j)) ∧ (∀ t, StrictMono (fun j => ψ j t)) ∧
          ∀ t : K, ∀ x : ℝ, P.eval₂ (MvPolynomial.eval (fun j => t.val j)) x = 0 ↔
            ∃ j, x = ψ j t := by
  obtain ⟨m, c, H, d, hcover, hpieces⟩ := s2v_t11b_finite_simple_degree_pieces P
  refine ⟨m, c, hcover, ?_⟩
  intro i K hsub hK a
  have hd : ∀ t ∈ K, (H i).map (MvPolynomial.eval (fun j => t j)) ≠ 0 ∧
      ((H i).map (MvPolynomial.eval (fun j => t j))).natDegree = d i :=
    fun t ht => ⟨(hpieces i t (hsub ht)).2.1, (hpieces i t (hsub ht)).2.2.1⟩
  have hs : ∀ t ∈ K, ∀ x : ℝ, (H i).eval₂ (MvPolynomial.eval (fun j => t j)) x = 0 →
      ((H i).map (MvPolynomial.eval (fun j => t j))).derivative.eval x ≠ 0 :=
    fun t ht => (hpieces i t (hsub ht)).2.2.2.2
  obtain ⟨r, ψ, hc, hm, hr⟩ := s2v_t11b_degree_stratum_ordered_roots (H i) (d i) K hK a hd hs
  refine ⟨r, ψ, hc, hm, ?_⟩
  intro t x
  exact ((hpieces i t.val (hsub t.property)).2.2.2.1 x).symm.trans (hr t x)

end HodgeLean.Foundations.Program
