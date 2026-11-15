import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Defs

/-! Connectedness of actual partition cells from their supplied box charts. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_cell_connected {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (i : Fin P.count) : IsConnected (P.cell i).realize := by
  have hconv : Convex ℝ {z : EuclideanSpace ℝ (Fin (P.dim i)) |
      ∀ v, -1 < z v ∧ z v < 1} := by
    apply convex_iff_forall_pos.mpr
    intro x hx y hy a b ha hb hab v
    change -1 < a * x v + b * y v ∧ a * x v + b * y v < 1
    constructor
    · nlinarith [mul_pos ha (sub_pos.mpr (hx v).1), mul_pos hb (sub_pos.mpr (hy v).1)]
    · nlinarith [mul_pos ha (sub_pos.mpr (hx v).2), mul_pos hb (sub_pos.mpr (hy v).2)]
  have hb := hconv.isConnected ⟨0, by intro v; simp⟩
  exact isConnected_iff_connectedSpace.mpr
    ((P.chart i).connectedSpace_iff.mpr (Subtype.connectedSpace hb))

end HodgeLean.Foundations.Program
