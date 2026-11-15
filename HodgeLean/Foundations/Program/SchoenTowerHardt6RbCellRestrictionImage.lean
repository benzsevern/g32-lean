import HodgeLean.Foundations.Program.SchoenTowerT11bDefs

/-! An extended root cell is exactly the original cylindrical cell restricted to its actual base image. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_cell_restriction_image {n : ℕ}
    (C D : Set (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hmaps : ∀ x ∈ D, β x ∈ C)
    (l₀ u₀ : C → ℝ) (l u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hl : ∀ x (hx : x ∈ D), l x = l₀ ⟨β x, hmaps x hx⟩)
    (hu : ∀ x (hx : x ∈ D), u x = u₀ ⟨β x, hmaps x hx⟩)
    (graph : Bool) (S : s2v_t11b_Formula (n + 1))
    (hS : ∀ z, z ∈ S.realize ↔ ∃ a : C, (∀ i, z i.succ = a.val i) ∧
      (if graph then z 0 = l₀ a else l₀ a < z 0 ∧ z 0 < u₀ a))
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
    (c : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hc : c = e '' {z | ∃ x ∈ D, (∀ i, z i.succ = β x i) ∧
      (if graph then z 0 = l x else l x < z 0 ∧ z 0 < u x)}) :
    c = e '' (S.realize ∩ {z | ∃ x ∈ D, ∀ i, z i.succ = β x i}) := by
  rw [hc]
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, hz, ht⟩
    refine ⟨(hS z).mpr ⟨⟨β x, hmaps x hx⟩, hz, ?_⟩, ⟨x, hx, hz⟩⟩
    rwa [← hl x hx, ← hu x hx]
  · rintro ⟨hzS, x, hx, hz⟩
    obtain ⟨a, ha, ht⟩ := (hS z).mp hzS
    have he : a = ⟨β x, hmaps x hx⟩ := by
      apply Subtype.ext
      ext i
      exact (ha i).symm.trans (hz i)
    subst a
    refine ⟨x, hx, hz, ?_⟩
    rwa [hl x hx, hu x hx]

end HodgeLean.Foundations.Program
