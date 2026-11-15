import HodgeLean.Foundations.Program.SchoenTowerHardtCad5BoxPartition
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Comparison
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Restriction

/-! Ambient bounds for supplied Boolean-graph box charts. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_chart_dimension_le_ambient {n d : ℕ}
    (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (J : s2v_t11b_Formula (d + n))
    (hJ : ∀ (z : {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
      (x : EuclideanSpace ℝ (Fin n)),
      WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ J.realize ↔ x = (e.symm z).val) :
    d ≤ n := by
  obtain ⟨PB, hPB⟩ := s2v_hardt_cad5_box_partition d
  obtain ⟨PC⟩ := s2v_hardt_cad5_partition_exists C
  have h := s2v_hardt_cad5_dimension_le_of_graph_injective PB PC e.symm e.symm.injective J hJ
  rw [hPB] at h
  exact_mod_cast h.trans (s2v_hardt_cad5_dimension_le_ambient PC)

end HodgeLean.Foundations.Program
