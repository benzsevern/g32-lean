import HodgeLean.Foundations.Program.SchoenTowerHardtCad4SubProofs

/-! Adjacent root labels give the actual two-endpoint equation of the corresponding cylindrical band. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_adjacent_band_formula {n r : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (hm : ∀ x, StrictMono (fun i => ψ i x))
    (band : Fin (r + 1) → s2v_t11b_Formula (n + 1))
    (hb : ∀ q z, z ∈ (band q).realize ↔ ∃ x : C.realize,
      (∀ i, z i.succ = x.val i) ∧
      (∀ j : Fin r, j.val < q.val → ψ j x < z 0) ∧
      (∀ j : Fin r, q.val ≤ j.val → z 0 < ψ j x))
    (lo hi : Fin r) (hadj : lo.val + 1 = hi.val) :
    ∀ z, z ∈ (band hi.castSucc).realize ↔ ∃ x : C.realize,
      (∀ i, z i.succ = x.val i) ∧ ψ lo x < z 0 ∧ z 0 < ψ hi x := by
  intro z
  rw [hb]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨hlo, hup⟩
    exact ⟨hlo lo (by change lo.val < hi.val; omega), hup hi le_rfl⟩
  · rintro ⟨hlo, hup⟩
    constructor
    · intro j hj
      exact lt_of_le_of_lt ((hm x).monotone (by
        change j.val ≤ lo.val
        change j.val < hi.val at hj
        omega)) hlo
    · intro j hj
      exact lt_of_lt_of_le hup ((hm x).monotone hj)

end HodgeLean.Foundations.Program
