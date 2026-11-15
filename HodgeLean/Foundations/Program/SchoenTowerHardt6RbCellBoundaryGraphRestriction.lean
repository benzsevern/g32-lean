import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAmbientRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGraphSourceRestriction

/-! Restriction of the existing homeomorphism to corresponding actual Boolean boundary carriers. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_cell_boundary_graph_restriction {n m : ℕ}
    (A S : Set (EuclideanSpace ℝ (Fin n))) (B T : Set (EuclideanSpace ℝ (Fin m)))
    (hSA : S ⊆ A) (hTB : T ⊆ B) (e : A ≃ₜ B)
    (hmem : ∀ x : A, x.val ∈ S ↔ (e x).val ∈ T)
    (F : s2v_t11b_Formula n) (hF : F.realize = S)
    (G : s2v_t11b_Formula (n + m))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (e x).val i)) :
    ∃ h : S ≃ₜ T, ∃ R : s2v_t11b_Formula (n + m),
      (∀ x : S, (h x).val = (e ⟨x.val, hSA x.property⟩).val) ∧
      (∀ z, z ∈ R.realize ↔ ∃ x : S,
        (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (h x).val i)) := by
  obtain ⟨h, hh, _⟩ := s2v_hardt6rb_ambient_restriction A S B T hSA hTB e hmem
  have hFA : F.realize ⊆ A := fun x hx => hSA (hF ▸ hx)
  obtain ⟨R, hR⟩ := s2v_hardt6rb_graph_source_restriction A B e G hG F hFA
  refine ⟨h, R, hh, ?_⟩
  intro z
  rw [hR]
  constructor
  · rintro ⟨x, hx, hy⟩
    refine ⟨⟨x.val, hF ▸ x.property⟩, hx, ?_⟩
    rw [hh]
    exact hy
  · rintro ⟨x, hx, hy⟩
    rw [hh] at hy
    exact ⟨⟨x.val, hF.symm ▸ x.property⟩, hx, hy⟩

end HodgeLean.Foundations.Program
