import HodgeLean.Foundations.Program.SchoenTowerHardtCad5AlgebraicRank

/-! Independent ambient coordinate tuples of any bounded finite size. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_independent_coordinate_projection_of_le {n e d : ℕ}
    (K : Subfield ℝ) (x : Fin n → ℝ) (z : Fin e → ℝ)
    (hz : AlgebraicIndependent K z)
    (ha : ∀ i, IsAlgebraic (Algebra.adjoin K (Set.range x)) (z i))
    (hde : d ≤ e) : ∃ r : Fin d → Fin n, AlgebraicIndependent K (fun i => x (r i)) := by
  cases d with
  | zero => exact ⟨Fin.elim0, algebraicIndependent_empty_type⟩
  | succ d =>
    exact s2v_hardt_cad5_independent_coordinate_projection K x z hz ha (by omega)

end HodgeLean.Foundations.Program
