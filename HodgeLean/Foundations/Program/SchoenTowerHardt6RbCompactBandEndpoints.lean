import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactBandIndices
import HodgeLean.Foundations.Program.SchoenTowerHardtCad4SubProofs

/-! Selected compact bands are exactly the intervals between adjacent ordered root sections. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_band_endpoints {n r : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : C.Nonempty)
    (ψ : Fin r → C → ℝ) (hm : ∀ a, StrictMono (fun q => ψ q a))
    (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hK : IsCompact K)
    (band : Fin (r + 1) → s2v_t11b_Formula (n + 1))
    (hb : ∀ i y, y ∈ (band i).realize ↔ ∃ a : C,
      (∀ v, y v.succ = a.val v) ∧
      (∀ j : Fin r, j.val < i.val → ψ j a < y 0) ∧
      (∀ j : Fin r, i.val ≤ j.val → y 0 < ψ j a))
    (i : Fin (r + 1)) (hsub : (band i).realize ⊆ K) :
    ∃ lo hi : Fin r, lo.val + 1 = hi.val ∧ hi.val = i.val ∧
      (∀ a, ψ lo a < ψ hi a) ∧
      ∀ y, y ∈ (band i).realize ↔ ∃ a : C,
        (∀ v, y v.succ = a.val v) ∧ ψ lo a < y 0 ∧ y 0 < ψ hi a := by
  obtain ⟨hlo, hhi⟩ := s2v_hardt6rb_compact_band_indices C hC ψ K hK band hb i hsub
  let lo : Fin r := ⟨i.val - 1, by omega⟩
  let hi : Fin r := ⟨i.val, hhi⟩
  refine ⟨lo, hi, by dsimp [lo, hi]; omega, rfl, ?_, ?_⟩
  · intro a
    exact hm a (by change i.val - 1 < i.val; omega)
  · intro y
    rw [hb i y]
    apply exists_congr
    intro a
    exact and_congr_right (fun _ => and_congr
      (s2v_hardt_cad4_sub_lower ψ hm i hlo a (y 0))
      (s2v_hardt_cad4_sub_upper ψ hm i hhi a (y 0)))

end HodgeLean.Foundations.Program
