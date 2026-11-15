import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPositiveChainFace

/-! Equal nested indicator mixtures share every face with positive coefficient. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_common_chain_support {ι : Type*} [DecidableEq ι]
    (C D : Finset (Finset ι))
    (hC : ∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S)
    (hD : ∀ S ∈ D, ∀ T ∈ D, S ⊆ T ∨ T ⊆ S)
    (a b : Finset ι → ℝ) (ha : ∀ S ∈ C, 0 ≤ a S) (hb : ∀ S ∈ D, 0 ≤ b S)
    (he : ∀ i, (∑ S ∈ C, if i ∈ S then a S else 0) =
      ∑ S ∈ D, if i ∈ S then b S else 0)
    (T : Finset ι) (hT : T ∈ C) (hne : T.Nonempty) (hpos : 0 < a T) : T ∈ D := by
  classical
  obtain ⟨r, hr, hTi⟩ := s2v_hardt6rb_positive_chain_face_superlevel C hC a ha T hT hpos
  obtain ⟨U, hU, hUi⟩ := s2v_hardt6rb_chain_superlevel D hD b hb r hr
  have hTU : T = U := by
    ext i
    rw [hTi i, hUi i, he i]
  rcases hU with hU | hU
  · exact False.elim (hne.ne_empty (hTU.trans hU))
  · exact hTU.symm ▸ hU

end HodgeLean.Foundations.Program
