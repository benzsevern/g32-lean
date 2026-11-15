import HodgeLean.Foundations.Program.SchoenTowerHardt2Coordinates
import HodgeLean.Foundations.Program.SchoenTowerHardt2Metric

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Elimination of the witness coordinates in a squared-distance polynomial inequality.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, metric consequence. -/
theorem s2v_hardt2_distance_exists {n : ℕ} (f : s2v_t11b_Formula n) :
    ∃ d : s2v_t11b_Formula (n + 1), ∀ a : EuclideanSpace ℝ (Fin (n + 1)),
      a ∈ d.realize ↔ ∃ y ∈ f.realize,
        (∑ i : Fin n, (a i.succ - y i)^2) < (a 0)^2 := by
  let b := s2v_hardt2_boundIndex (n + 1) n
  let u := s2v_hardt2_freeIndex (n + 1) n
  let p : MvPolynomial (Fin ((n + 1) + n)) ℝ :=
    (MvPolynomial.X (u 0))^2 - ∑ i : Fin n,
      (MvPolynomial.X (u i.succ) - MvPolynomial.X (b i))^2
  let F : s2v_t11b_Formula ((n + 1) + n) :=
    .inter (s2v_hardt1_rename b f) (.compl (.nonneg (-p)))
  have hF (y : Fin n → ℝ) (a : EuclideanSpace ℝ (Fin (n + 1))) :
      s2v_hardt2_insert n y a ∈ F.realize ↔
        WithLp.toLp 2 y ∈ f.realize ∧
        (∑ i : Fin n, (a i.succ - y i)^2) < (a 0)^2 := by
    change (_ ∈ (s2v_hardt1_rename b f).realize ∧ _) ↔ _
    rw [s2v_hardt1_realize_rename]
    have hb : WithLp.toLp 2 (fun i => s2v_hardt2_insert n y a (b i)) =
        WithLp.toLp 2 y := by
      ext i
      exact s2v_hardt2_insert_bound y a i
    rw [hb]
    apply and_congr_right
    intro _
    simp only [s2v_t11b_Formula.realize, Set.mem_compl_iff, Set.mem_setOf_eq,
      p, map_neg, map_sub, map_pow, map_sum, MvPolynomial.eval_X,
      b, u, s2v_hardt2_insert_free, s2v_hardt2_insert_bound, not_le, neg_lt_zero,
      sub_pos]
  obtain ⟨d, hd⟩ := s2v_hardt2_repeated_projection F
  refine ⟨d, ?_⟩
  intro a
  rw [hd]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨WithLp.toLp 2 y, (hF y a).mp hy⟩
  · rintro ⟨y, hy, hdist⟩
    exact ⟨fun i => y i, (hF _ a).mpr ⟨hy, hdist⟩⟩

#print axioms s2v_hardt2_distance_exists
end HodgeLean.Foundations.Program
