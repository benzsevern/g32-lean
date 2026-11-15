import HodgeLean.Foundations.Program.SchoenTowerHardt1Cells

/-! Polynomial graphs of coordinate restrictions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A supplied Boolean stage has the actual graph of any selected coordinate.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, elementary graph
restriction; Bochnak–Coste–Roy, Real Algebraic Geometry, Chapter 9, preparation. -/
theorem s2v_hardt_coordinate_graph {n : ℕ} (f : s2v_t11b_Formula n)
    (a : Fin n) :
    ∃ g : s2v_t11b_Formula (n + 1), ∀ z,
      z ∈ g.realize ↔
        WithLp.toLp 2 (fun i : Fin n => z i.castSucc) ∈ f.realize ∧
        z (Fin.last n) = z a.castSucc := by
  let p : MvPolynomial (Fin (n + 1)) ℝ :=
    MvPolynomial.X (Fin.last n) - MvPolynomial.X a.castSucc
  refine ⟨.inter (s2v_hardt1_rename Fin.castSucc f)
    (.inter (.nonneg p) (.nonneg (-p))), ?_⟩
  intro z
  rw [show z ∈ (s2v_t11b_Formula.inter (s2v_hardt1_rename Fin.castSucc f)
      (.inter (.nonneg p) (.nonneg (-p)))).realize ↔
      z ∈ (s2v_hardt1_rename Fin.castSucc f).realize ∧
        (0 ≤ MvPolynomial.eval (fun i => z i) p ∧
        0 ≤ MvPolynomial.eval (fun i => z i) (-p)) from Iff.rfl]
  rw [s2v_hardt1_realize_rename]
  simp only [p, map_sub, map_neg, MvPolynomial.eval_X]
  constructor
  · rintro ⟨hf, h₁, h₂⟩
    exact ⟨hf, by linarith⟩
  · rintro ⟨hf, he⟩
    exact ⟨hf, by rw [he]; norm_num, by rw [he]; norm_num⟩

/-- Every supplied stage carries its actual coordinate graph, with agreement on overlaps.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, elementary graph restriction;
Bochnak–Coste–Roy, Real Algebraic Geometry, Chapter 9, preparation. -/
theorem s2v_hardt_stage_graphs {n : ℕ} {ι : Type*}
    (stage : ι → s2v_t11b_Formula (n + 1)) :
    ∃ graph : ι → s2v_t11b_Formula ((n + 1) + 1),
      (∀ r z, z ∈ (graph r).realize ↔
        WithLp.toLp 2 (fun i : Fin (n + 1) => z i.castSucc) ∈ (stage r).realize ∧
        z (Fin.last (n + 1)) = z (Fin.castSucc (Fin.last n))) ∧
      (∀ r s z, z ∈ (graph r).realize →
        (z ∈ (graph s).realize ↔
          WithLp.toLp 2 (fun i : Fin (n + 1) => z i.castSucc) ∈ (stage s).realize)) := by
  choose graph hg using fun r => s2v_hardt_coordinate_graph (stage r) (Fin.last n)
  refine ⟨graph, hg, ?_⟩
  intro r s z hz
  rw [hg s z]
  exact and_iff_left ((hg r z).mp hz).2

end HodgeLean.Foundations.Program
