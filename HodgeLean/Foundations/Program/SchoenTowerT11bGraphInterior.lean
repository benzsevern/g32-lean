import HodgeLean.Foundations.Program.SchoenTowerT11bGraphTransport
import HodgeLean.Foundations.Program.SchoenTowerT11bBoundary

/-! Empty interior of actual graphs in Euclidean coordinates.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A Boolean realization that is an actual graph has empty ambient interior.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, graph-dimension step. -/
theorem s2v_t11b_graph_realize_empty_interior {n : ℕ} (f : s2v_t11b_Formula n)
    (p : EuclideanSpace ℝ (Fin n) → ℝ) (g : s2v_t11b_Formula (n + 1))
    (hg : ∀ z : EuclideanSpace ℝ (Fin (n + 1)), z ∈ g.realize ↔
      WithLp.toLp 2 (fun i : Fin n => z i.castSucc) ∈ f.realize ∧
        z (Fin.last n) = p (WithLp.toLp 2 (fun i : Fin n => z i.castSucc))) :
    interior g.realize = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let w := z + PiLp.single 2 (Fin.last n) (ε / 2)
  have hw : w ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa only [w, add_sub_cancel_left, PiLp.norm_single, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)] using half_lt_self hε
  have hfirst : WithLp.toLp 2 (fun i : Fin n => w i.castSucc) =
      WithLp.toLp 2 (fun i : Fin n => z i.castSucc) := by
    ext i
    simp [w, PiLp.single_apply, Fin.castSucc_ne_last]
  have hzlast := ((hg z).mp (interior_subset hz)).2
  have hwlast := ((hg w).mp (interior_subset (hball hw))).2
  rw [hfirst, ← hzlast] at hwlast
  have hlast : w (Fin.last n) = z (Fin.last n) + ε / 2 := by
    simp [w, PiLp.single_apply]
  rw [hlast] at hwlast
  linarith

end HodgeLean.Foundations.Program
