import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactBandEndpoints

/-! Every compact-carrier point has a finite graph or adjacent-band label in its prepared cylinder. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_cylinder_labels {n r : ℕ}
    (C : s2v_t11b_Formula n) (hC : C.realize.Nonempty)
    (ψ : Fin r → C.realize → ℝ) (hm : ∀ x, StrictMono (fun i => ψ i x))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (band : Fin (r + 1) → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ i, y i.succ = a.val i) ∧ y 0 = ψ q a)
    (hb : ∀ q y, y ∈ (band q).realize ↔ ∃ a : C.realize,
      (∀ i, y i.succ = a.val i) ∧
      (∀ j : Fin r, j.val < q.val → ψ j a < y 0) ∧
      (∀ j : Fin r, q.val ≤ j.val → y 0 < ψ j a))
    (F : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hF : IsCompact F)
    (hband : ∀ q, (band q).realize ⊆ F ∨ Disjoint (band q).realize F)
    (x : C.realize) (z : EuclideanSpace ℝ (Fin (n + 1)))
    (hxz : ∀ i, z i.succ = x.val i) (hz : z ∈ F) :
    ∃ a : Fin r ⊕ {p : Fin r × Fin r // p.1.val + 1 = p.2.val},
      match a with
      | .inl i => z 0 = ψ i x
      | .inr p => ψ p.val.1 x < z 0 ∧ z 0 < ψ p.val.2 x := by
  obtain ⟨_, _, _, _, _, hcover, _⟩ :=
    s2v_hardt_cad3_cylinder_partition C ψ hm hC g hg band hb
  rcases (hcover z).mpr ⟨x, hxz⟩ with ⟨q, hq⟩ | ⟨q, hq⟩
  · have hsub : (band q).realize ⊆ F := by
      rcases hband q with h | h
      · exact h
      · exact False.elim (Set.disjoint_left.mp h hq hz)
    obtain ⟨lo, hi, hadj, hhi, horder, hcell⟩ :=
      s2v_hardt6rb_compact_band_endpoints C.realize hC ψ hm F hF band hb q hsub
    obtain ⟨y, hy, hlo, hup⟩ := (hcell z).mp hq
    have he : y = x := by
      apply Subtype.ext
      ext i
      exact (hy i).symm.trans (hxz i)
    subst y
    exact ⟨.inr ⟨(lo, hi), hadj⟩, hlo, hup⟩
  · obtain ⟨y, hy, ht⟩ := (hg q z).mp hq
    have he : y = x := by
      apply Subtype.ext
      ext i
      exact (hy i).symm.trans (hxz i)
    subst y
    exact ⟨.inl q, ht⟩

end HodgeLean.Foundations.Program
