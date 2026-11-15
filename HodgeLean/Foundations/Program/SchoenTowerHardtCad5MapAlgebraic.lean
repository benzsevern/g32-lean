import HodgeLean.Foundations.Program.SchoenTowerHardtCad5CoordinateFibers

/-! Coefficient-field control of the coordinates of actual Boolean-graph maps. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_graph_map_algebraic {n q : ℕ}
    (S : s2v_t11b_Formula n) (f : S.realize → EuclideanSpace ℝ (Fin q))
    (G : s2v_t11b_Formula (n + q))
    (hG : ∀ (x : S.realize) (y : EuclideanSpace ℝ (Fin q)),
      WithLp.toLp 2 (Fin.append (fun i => x.val i) (fun i => y i)) ∈ G.realize ↔ y = f x) :
    ∃ K : Subfield ℝ, Countable K ∧
      ∀ L : Subfield ℝ, K ≤ L → ∀ a : Fin n → L,
        ∀ ha : WithLp.toLp 2 (fun i => (a i : ℝ)) ∈ S.realize,
        ∀ j, IsAlgebraic L ((f ⟨WithLp.toLp 2 (fun i => (a i : ℝ)), ha⟩) j) := by
  let R : s2v_t11b_Formula (n + q) :=
    .inter (s2v_hardt1_rename (Fin.castAdd q) S) G
  have hR (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin q)) :
      WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => y i)) ∈ R.realize ↔
        x ∈ S.realize ∧
        WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => y i)) ∈ G.realize := by
    change (_ ∧ _) ↔ _
    rw [s2v_hardt1_realize_rename]
    have hx : WithLp.toLp 2 (fun i =>
        Fin.append (fun j => x j) (fun j => y j) (Fin.castAdd q i)) = x := by
      ext i
      simp
    rw [hx]
  obtain ⟨K, hK, hAlg⟩ := s2v_hardt_cad5_finite_graph_fiber_algebraic R
  refine ⟨K, hK, ?_⟩
  intro L hKL a ha
  let x : S.realize := ⟨WithLp.toLp 2 (fun i => (a i : ℝ)), ha⟩
  have hfin : {y : EuclideanSpace ℝ (Fin q) | WithLp.toLp 2
      (Fin.append (fun i => (a i : ℝ)) (fun i => y i)) ∈ R.realize}.Finite := by
    apply (Set.finite_singleton (f x)).subset
    intro y hy
    exact (hG x y).mp ((hR x.val y).mp hy).2
  exact hAlg L hKL a hfin (f x) ((hR x.val (f x)).mpr ⟨ha, (hG x _).mpr rfl⟩)

end HodgeLean.Foundations.Program
