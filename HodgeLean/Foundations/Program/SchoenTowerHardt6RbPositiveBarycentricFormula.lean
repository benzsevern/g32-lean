import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBarycentricFormula

/-! Actual Boolean constraints for strictly positive finite barycentric coordinates. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_positive_barycentric_formula {n m : ℕ}
    (v : Fin m → EuclideanSpace ℝ (Fin n)) :
    ∃ F : s2v_t11b_Formula (n + m), ∀ z, z ∈ F.realize ↔
      (∀ j, 0 < z (s2v_hardt2_boundIndex n m j)) ∧
      (∑ j, z (s2v_hardt2_boundIndex n m j)) = 1 ∧
      (∀ i, z (s2v_hardt2_freeIndex n m i) =
        ∑ j, z (s2v_hardt2_boundIndex n m j) * v j i) := by
  obtain ⟨F, hF⟩ := s2v_hardt6rb_barycentric_relation_formula v
  obtain ⟨P, hP⟩ := s2v_hardt_cad3_finite_inter (fun j : Fin m =>
    (s2v_t11b_Formula.nonneg (-MvPolynomial.X (s2v_hardt2_boundIndex n m j))).compl)
  refine ⟨F.inter P, ?_⟩
  intro z
  change (z ∈ F.realize ∧ z ∈ P.realize) ↔ _
  rw [hF, hP]
  simp only [s2v_t11b_Formula.realize, Set.mem_compl_iff, Set.mem_setOf_eq,
    map_neg, MvPolynomial.eval_X, neg_nonneg, not_le]
  constructor
  · rintro ⟨⟨_, hs, hc⟩, hp⟩
    exact ⟨hp, hs, hc⟩
  · rintro ⟨hp, hs, hc⟩
    exact ⟨⟨fun j => (hp j).le, hs, hc⟩, hp⟩

end HodgeLean.Foundations.Program
