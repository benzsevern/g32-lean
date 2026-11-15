import HodgeLean.Foundations.Program.BraidBridgesCrossing12Piece2

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65x_piece_crossings_0_0 :
    (∀ m m' : Fin (b65x_crossings 0 0).length, m < m' →
      (b65x_crossings 0 0)[m].hi < (b65x_crossings 0 0)[m'].lo) ∧
    (∀ c ∈ b65x_crossings 0 0,
      (c.lo : ℝ) ∈ b65x_dom 0 ∧ (c.hi : ℝ) ∈ b65x_dom 0 ∧ c.lo < c.hi ∧
      (c.dir = 1 ∨ c.dir = -1) ∧
      (∀ t ∈ Set.Icc (c.lo : ℝ) c.hi, (b65x_down 0 0 t).im < 0) ∧
      (∃! t, t ∈ Set.Icc (c.lo : ℝ) c.hi ∧
        (b65x_down 0 0 t).re = b65x_cutPoint c.cut) ∧
      (c.dir : ℝ) * ((b65x_down 0 0 c.lo).re - b65x_cutPoint c.cut) < 0 ∧
      0 < (c.dir : ℝ) * ((b65x_down 0 0 c.hi).re - b65x_cutPoint c.cut)) ∧
    ∀ t ∈ b65x_dom 0, ∀ j : Fin 3, b65x_OnCut j (b65x_down 0 0 t) →
      ∃ c ∈ b65x_crossings 0 0, c.cut = j ∧ t ∈ Set.Icc (c.lo : ℝ) c.hi := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    exact m.elim0
  · intro c hc
    norm_num [b65x_crossings] at hc
  · intro t ht j hcut
    have he : b65x_piece 0 0 t = b65x_piece 0 1 (-1) := by
      norm_num [b65x_piece, b65x_centre, b65x_radius, b65x_et, mr_basePoint, mr_centre]
      <;> ring
    have hd : b65x_down 0 0 t = b65x_down 0 1 (-1) := by
      unfold b65x_down
      rw [he]
    rw [hd] at hcut
    obtain ⟨c, hc, hj, hr⟩ := b65x_piece_crossings_0_1.2.2 (-1) (by norm_num [b65x_dom]) j hcut
    norm_num [b65x_crossings] at hc
    subst c
    norm_num at hr

end HodgeLean.Foundations.Program
