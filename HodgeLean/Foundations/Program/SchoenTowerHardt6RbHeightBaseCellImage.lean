import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandCoordinates

/-! Height-preserving base changes give the actual ambient graph and band cell image equations. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_height_base_cell_image {n : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin n))) (R : EuclideanSpace ℝ (Fin n) → ℝ → Prop)
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (he0 : ∀ p, e p 0 = p.2) (hes : ∀ p i, e p i.succ = p.1 i) :
    (fun z => e (β (e.symm z).1, (e.symm z).2)) ''
      (e '' {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 ∈ B ∧ R p.1 p.2}) =
      {z | ∃ x ∈ B, (∀ i, z i.succ = β x i) ∧ R x (z 0)} := by
  ext z
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    simp only [e.symm_apply_apply]
    exact ⟨p.1, hp.1, fun i => hes (β p.1, p.2) i, (he0 (β p.1, p.2)).symm ▸ hp.2⟩
  · rintro ⟨x, hx, hb, hr⟩
    refine ⟨e (x, z 0), ⟨(x, z 0), ⟨hx, hr⟩, rfl⟩, ?_⟩
    dsimp only
    rw [e.symm_apply_apply]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact he0 (β x, z 0)
    · exact (hes (β x, z 0) j).trans (hb j).symm

end HodgeLean.Foundations.Program
