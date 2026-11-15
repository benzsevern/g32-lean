import HodgeLean.Foundations.Program.SchoenTowerT11bDefs

/-! Polynomial carriers of the boundaries of Boolean realizations.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The finite family of polynomial atoms occurring in a Boolean description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite sign decomposition data. -/
def s2v_t11b_Formula.atoms {n : ℕ} : s2v_t11b_Formula n → Finset (MvPolynomial (Fin n) ℝ)
  | .nonneg p => {p}
  | .compl f => f.atoms
  | .inter f g => f.atoms ∪ g.atoms

/-- Every boundary point lies on the zero locus of a nonzero polynomial atom.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, boundaries of sign regions. -/
theorem s2v_t11b_frontier_polynomial {n : ℕ} (f : s2v_t11b_Formula n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ frontier f.realize) :
    ∃ p ∈ f.atoms, p ≠ 0 ∧ MvPolynomial.eval (fun i => x i) p = 0 := by
  classical
  induction f with
  | nonneg p =>
    by_cases hp : p = 0
    · subst p
      simp only [s2v_t11b_Formula.realize, map_zero, le_refl, Set.ofPred_true,
        frontier_univ, Set.mem_empty_iff_false] at hx
    · have hc : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => y i) p) :=
        p.continuous_eval.comp (PiLp.continuous_ofLp 2 _)
      refine ⟨p, Finset.mem_singleton_self p, hp, ?_⟩
      exact (frontier_le_subset_eq continuous_const hc hx).symm
  | compl f ih =>
    exact ih (by simpa only [s2v_t11b_Formula.realize, frontier_compl] using hx)
  | inter f g ihf ihg =>
    rcases frontier_inter_subset f.realize g.realize hx with hf | hg
    · obtain ⟨p, hp, hn, hz⟩ := ihf hf.1
      exact ⟨p, Finset.mem_union_left _ hp, hn, hz⟩
    · obtain ⟨p, hp, hn, hz⟩ := ihg hg.2
      exact ⟨p, Finset.mem_union_right _ hp, hn, hz⟩

/-- A member outside the interior has an actual nonzero vanishing polynomial atom.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, boundaries of sign regions. -/
theorem s2v_t11b_boundary_active_atom {n : ℕ} (f : s2v_t11b_Formula n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ f.realize) (hxi : x ∉ interior f.realize) :
    ∃ p ∈ f.atoms, p ≠ 0 ∧ MvPolynomial.eval (fun i => x i) p = 0 := by
  exact s2v_t11b_frontier_polynomial f x ⟨subset_closure hx, hxi⟩

end HodgeLean.Foundations.Program
