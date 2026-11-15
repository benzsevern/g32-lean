import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Relations

/-! Actual endpoint graphs restrict to any Boolean subdomain without changing their height coordinates. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_endpoint_graph_restriction {n : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : s2v_t11b_Formula (n + 1))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x ∈ A, (∀ i, z i.succ = x i) ∧ z 0 = f x)
    (B : s2v_t11b_Formula n) (hB : B.realize ⊆ A) :
    ∃ H : s2v_t11b_Formula (n + 1), ∀ z, z ∈ H.realize ↔
      ∃ x ∈ B.realize, (∀ i, z i.succ = x i) ∧ z 0 = f x := by
  refine ⟨G.inter (s2v_hardt1_rename Fin.succ B), ?_⟩
  intro z
  change (z ∈ G.realize ∧ z ∈ (s2v_hardt1_rename Fin.succ B).realize) ↔ _
  rw [hG, s2v_hardt1_realize_rename]
  constructor
  · rintro ⟨⟨x, _, hx, ht⟩, hb⟩
    have he : WithLp.toLp 2 (fun i => z i.succ) = x := by ext i; exact hx i
    exact ⟨x, he ▸ hb, hx, ht⟩
  · rintro ⟨x, hb, hx, ht⟩
    refine ⟨⟨x, hB hb, hx, ht⟩, ?_⟩
    have he : WithLp.toLp 2 (fun i => z i.succ) = x := by ext i; exact hx i
    exact he.symm ▸ hb

end HodgeLean.Foundations.Program
