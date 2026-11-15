import HodgeLean.Foundations.Program.SchoenTowerT11bConnectedRefinement

/-! Finite connected parameter covers with actual Euclidean projection coordinates.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every Boolean cylindrical projection has a finite connected parameter cover with specified actual fibers and the original projection equation.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite connected cylindrical chart step. -/
theorem s2v_t11b_euclidean_finite_connected_charts {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ m : ℕ, ∃ K : Fin m → Set (EuclideanSpace ℝ (Fin n)), ∃ a : ∀ i, K i,
      (∀ i, IsConnected (K i)) ∧
      (∀ t : EuclideanSpace ℝ (Fin n), ∃ i, t ∈ K i) ∧
      ∀ i, ∃ e : {y : EuclideanSpace ℝ (Fin (n + 1)) |
          y ∈ f.realize ∧ WithLp.toLp 2 (fun v => y v.succ) ∈ K i} ≃ₜ
        ({y : EuclideanSpace ℝ (Fin (n + 1)) |
          y ∈ f.realize ∧ WithLp.toLp 2 (fun v => y v.succ) = (a i).val} × K i),
        ∀ y, (e y).2.val = WithLp.toLp 2 (fun v => y.val v.succ) := by
  classical
  obtain ⟨m, c, hc, hcharts⟩ := s2v_t11b_euclidean_finite_subregion_charts f
  choose k U hU hUcover using fun i => s2v_t11b_formula_finite_preconnected_cover n (c i)
  let J := {z : (i : Fin m) × Fin (k i) | (U z.1 z.2).Nonempty}
  let E := Fintype.equivFin J
  let K : Fin (Fintype.card J) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun q => U (E.symm q).val.1 (E.symm q).val.2
  let a : ∀ q, K q := fun q => ⟨(E.symm q).property.choose, (E.symm q).property.choose_spec⟩
  refine ⟨Fintype.card J, K, a, ?_, ?_, ?_⟩
  · intro q
    exact ⟨(E.symm q).property, (hU _ _).1⟩
  · intro t
    obtain ⟨i, hi⟩ := hc t
    obtain ⟨j, hj⟩ := hUcover i t hi
    let z : J := ⟨⟨i, j⟩, ⟨t, hj⟩⟩
    refine ⟨E z, ?_⟩
    change t ∈ U (E.symm (E z)).val.1 (E.symm (E z)).val.2
    rw [E.symm_apply_apply]
    exact hj
  · intro q
    exact hcharts (E.symm q).val.1 (K q) (hU _ _).2 (hU _ _).1 (a q)

/-- The original cylindrical projection has actual-fiber charts over a finite disjoint connected partition of its entire parameter space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, disjoint connected cylindrical chart step. -/
theorem s2v_t11b_euclidean_finite_disjoint_connected_charts {n : ℕ}
    (f : s2v_t11b_Formula (n + 1)) :
    ∃ m : ℕ, ∃ K : Fin m → Set (EuclideanSpace ℝ (Fin n)), ∃ a : ∀ i, K i,
      (∀ i, IsConnected (K i)) ∧
      (∀ t : EuclideanSpace ℝ (Fin n), ∃ i, t ∈ K i) ∧
      Pairwise (fun i j => Disjoint (K i) (K j)) ∧
      ∀ i, ∃ e : {y : EuclideanSpace ℝ (Fin (n + 1)) |
          y ∈ f.realize ∧ WithLp.toLp 2 (fun v => y v.succ) ∈ K i} ≃ₜ
        ({y : EuclideanSpace ℝ (Fin (n + 1)) |
          y ∈ f.realize ∧ WithLp.toLp 2 (fun v => y v.succ) = (a i).val} × K i),
        ∀ y, (e y).2.val = WithLp.toLp 2 (fun v => y.val v.succ) := by
  classical
  obtain ⟨m, c, hc, hcharts⟩ := s2v_t11b_euclidean_finite_subregion_charts f
  obtain ⟨l, K, hK, hcover, hdisj, hparent⟩ := s2v_t11b_finite_connected_refinement c hc
  let a : ∀ q, K q := fun q => ⟨(hK q).nonempty.choose, (hK q).nonempty.choose_spec⟩
  refine ⟨l, K, a, hK, hcover, hdisj, ?_⟩
  intro q
  obtain ⟨i, hi⟩ := hparent q
  exact hcharts i (K q) hi (hK q).isPreconnected (a q)

end HodgeLean.Foundations.Program
