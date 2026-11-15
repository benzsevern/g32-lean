import HodgeLean.Foundations.Program.SchoenTowerT11bBooleanSections

/-! Uniform atom signs determine actual Boolean membership on a nonempty carrier. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_boolean_sign_compatibility {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S.Nonempty)
    (B : s2v_t11b_Formula n)
    (hsign : ∀ p ∈ B.atoms,
      (∀ x ∈ S, MvPolynomial.eval (fun v => x v) p < 0) ∨
      (∀ x ∈ S, MvPolynomial.eval (fun v => x v) p = 0) ∨
      (∀ x ∈ S, 0 < MvPolynomial.eval (fun v => x v) p)) :
    S ⊆ B.realize ∨ Disjoint S B.realize := by
  classical
  obtain ⟨x, hx⟩ := hS
  have constant (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ S) :
      y ∈ B.realize ↔ x ∈ B.realize := by
    apply s2v_t11b_formula_membership_of_atom_signs
    intro p hp
    rcases hsign p hp with h | h | h
    · exact iff_of_false (not_le.mpr (h y hy)) (not_le.mpr (h x hx))
    · rw [h y hy, h x hx]
    · exact iff_of_true (le_of_lt (h y hy)) (le_of_lt (h x hx))
  by_cases hxB : x ∈ B.realize
  · exact Or.inl (fun y hy => (constant y hy).mpr hxB)
  · exact Or.inr (Set.disjoint_left.mpr (fun y hy hB => hxB ((constant y hy).mp hB)))

end HodgeLean.Foundations.Program
