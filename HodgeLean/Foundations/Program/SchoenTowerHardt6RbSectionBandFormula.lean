import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSectionSubstitution
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandFormula

/-! Boolean interpolation relations for sections specified by actual graphs. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_section_band_relation {n N : ℕ}
    (f : s2v_t11b_Formula n) (s : Fin 4 → f.realize → ℝ)
    (g : Fin 4 → s2v_t11b_Formula (n + 1))
    (hg : ∀ i z, z ∈ (g i).realize ↔ ∃ x : f.realize,
      (∀ v, z v.succ = x.val v) ∧ z 0 = s i x)
    (idx : Fin n → Fin N) (iy iv : Fin N) :
    ∃ G : s2v_t11b_Formula N, ∀ z, z ∈ G.realize ↔
      ∃ x : f.realize, (∀ v, z (idx v) = x.val v) ∧
        s 0 x ≤ z iy ∧ z iy ≤ s 1 x ∧ s 2 x ≤ z iv ∧ z iv ≤ s 3 x ∧
        (z iy - s 0 x) * (s 3 x - s 2 x) =
          (z iv - s 2 x) * (s 1 x - s 0 x) := by
  let A : MvPolynomial (Fin (N + 4)) ℝ := MvPolynomial.X (s2v_hardt2_boundIndex N 4 0)
  let B : MvPolynomial (Fin (N + 4)) ℝ := MvPolynomial.X (s2v_hardt2_boundIndex N 4 1)
  let C : MvPolynomial (Fin (N + 4)) ℝ := MvPolynomial.X (s2v_hardt2_boundIndex N 4 2)
  let D : MvPolynomial (Fin (N + 4)) ℝ := MvPolynomial.X (s2v_hardt2_boundIndex N 4 3)
  let top : s2v_t11b_Formula (N + 4) := .nonneg 0
  obtain ⟨R, hR⟩ := s2v_hardt6rb_polynomial_band_relation top A B C D id
    (s2v_hardt2_freeIndex N 4 iy) (s2v_hardt2_freeIndex N 4 iv)
  obtain ⟨G, hG⟩ := s2v_hardt6rb_section_substitution f s g hg idx R
  refine ⟨G, ?_⟩
  intro z
  rw [hG]
  constructor
  · rintro ⟨x, hx, hRx⟩
    have hz := (hR _).mp hRx
    simp only [A, B, C, D, MvPolynomial.eval_X, id_eq,
      s2v_hardt2_insert_bound, s2v_hardt2_insert_free] at hz
    exact ⟨x, hx, hz.2⟩
  · rintro ⟨x, hx, ha, hb, hc, hd, hrel⟩
    refine ⟨x, hx, (hR _).mpr ?_⟩
    simp only [A, B, C, D, MvPolynomial.eval_X, id_eq,
      s2v_hardt2_insert_bound, s2v_hardt2_insert_free]
    refine ⟨?_, ha, hb, hc, hd, hrel⟩
    simp only [top, s2v_t11b_Formula.realize, Set.mem_setOf_eq, map_zero, le_refl]

end HodgeLean.Foundations.Program
