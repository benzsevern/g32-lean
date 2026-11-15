import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Relations

/-! Restricting the actual source of a graph preserves its full coordinate equations. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_graph_source_restriction {n q : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (B : Set (EuclideanSpace ℝ (Fin q)))
    (k : A → B) (G : s2v_t11b_Formula (n + q))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd q i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (k x).val i))
    (C : s2v_t11b_Formula n) (hC : C.realize ⊆ A) :
    ∃ F : s2v_t11b_Formula (n + q), ∀ z, z ∈ F.realize ↔ ∃ x : C.realize,
      (∀ i, z (Fin.castAdd q i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (k ⟨x.val, hC x.property⟩).val i) := by
  refine ⟨G.inter (s2v_hardt1_rename (Fin.castAdd q) C), ?_⟩
  intro z
  change (z ∈ G.realize ∧ z ∈ (s2v_hardt1_rename (Fin.castAdd q) C).realize) ↔ _
  rw [hG, s2v_hardt1_realize_rename]
  constructor
  · rintro ⟨⟨x, hx, hy⟩, hc⟩
    have he : WithLp.toLp 2 (fun i => z (Fin.castAdd q i)) = x.val := by
      ext i
      exact hx i
    rw [he] at hc
    exact ⟨⟨x.val, hc⟩, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    refine ⟨⟨⟨x.val, hC x.property⟩, hx, hy⟩, ?_⟩
    have he : WithLp.toLp 2 (fun i => z (Fin.castAdd q i)) = x.val := by
      ext i
      exact hx i
    rw [he]
    exact x.property

end HodgeLean.Foundations.Program
