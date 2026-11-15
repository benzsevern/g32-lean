import HodgeLean.Foundations.Program.SchoenTowerHardt1
import HodgeLean.Foundations.Program.SchoenTowerT11bSimultaneousRoots

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Connected Boolean parameter pieces carry an exact ordered enumeration of active roots.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, cylindrical construction, pp. 6–7. -/
theorem s2v_hardt3_active_partition {n k : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ i, IsConnected (c i).realize) ∧
      (∀ a : EuclideanSpace ℝ (Fin n), ∃ i, a ∈ (c i).realize) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      ∀ i, ∃ r : ℕ, ∃ ψ : Fin r → (c i).realize → ℝ,
        (∀ v, Continuous (ψ v)) ∧
        (∀ a, StrictMono (fun v => ψ v a)) ∧
        (∀ j, (∀ a : (c i).realize,
          (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
          (∀ a : (c i).realize,
          (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0)) ∧
        (∀ a : (c i).realize, ∀ x : ℝ,
          (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
            (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) x = 0) ↔
            ∃ v, x = ψ v a) := by
  classical
  choose m c hc hr using fun s : Fin k → Bool =>
    s2v_t11b_finite_pieces_ordered_roots (s2v_t11b_activeCarrier P s)
  let J := (s : Fin k → Bool) × Fin (m s)
  let E := Fintype.equivFin J
  let C : Fin (Fintype.card J) → s2v_t11b_Formula n := fun q =>
    .inter (s2v_t11b_activeAtomFormula P (E.symm q).1) (c (E.symm q).1 (E.symm q).2)
  have hcover : ∀ a : EuclideanSpace ℝ (Fin n), ∃ q, a ∈ (C q).realize := by
    intro a
    obtain ⟨s, hs, _⟩ := s2v_t11b_activeAtomFormula_partition P a
    obtain ⟨i, hi⟩ := hc s a (s2v_t11b_activeCarrier_specialize_ne_zero P s a hs)
    refine ⟨E ⟨s, i⟩, ?_⟩
    change a ∈ (s2v_t11b_activeAtomFormula P (E.symm (E (⟨s, i⟩ : J))).1).realize ∧ _
    rw [E.symm_apply_apply]
    exact ⟨hs, hi⟩
  obtain ⟨l, d, hd, hdc, hdisj, hsub⟩ := s2v_hardt1_connected_boolean_refinement C hcover
  refine ⟨l, d, hd, hdc, hdisj, ?_⟩
  intro q
  obtain ⟨i, hi⟩ := hsub q
  let s := (E.symm i).1
  have hs (a : (d q).realize) :=
    (s2v_t11b_activeAtomFormula_realize P s a.val).mp (hi a.property).1
  obtain ⟨a, ha⟩ := (hd q).nonempty
  obtain ⟨r, ψ, hψ, hmono, hroots⟩ := hr s (E.symm i).2 (d q).realize
    (fun t ht => (hi ht).2) (hd q).isPreconnected ⟨a, ha⟩
  refine ⟨r, ψ, hψ, hmono, ?_, ?_⟩
  · intro j
    by_cases hj : s j = true
    · exact Or.inr (fun a => (hs a j).mp hj)
    · exact Or.inl (fun a => not_ne_iff.mp (fun hn => hj ((hs a j).mpr hn)))
  · intro a x
    rw [← hroots a x, s2v_t11b_activeCarrier_zero_iff]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, (hs a j).mpr hj, hx⟩
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, (hs a j).mp hj, hx⟩

#print axioms s2v_hardt3_active_partition
end HodgeLean.Foundations.Program
