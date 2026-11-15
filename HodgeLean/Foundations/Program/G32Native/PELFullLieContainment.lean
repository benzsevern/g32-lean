import HodgeLean.Foundations.MatrixAlgGroupLie

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations
variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}

/-- A subgroup whose tangent space contains the ambient tangent space
contains the ambient identity component.
Source: Borel, Linear Algebraic Groups, second edition, §7.1. -/
theorem pel_identityComponent_subset_of_lie_le (G H : MatrixAlgGroup k n)
    (hLie : g1_lieAlgebra G ≤ g1_lieAlgebra H) :
    g1_identityComponent G ⊆ (H.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) := by
  obtain ⟨C, hC⟩ := g1_exists_identityComponent G
  have hconn : g1_IsConnected C := by
    change @IsConnected _ (g1_zariski k n) (C.carrier : Set _)
    rw [hC]
    exact (@isConnected_connectedComponentIn_iff _ (g1_zariski k n) _ _).mpr G.carrier.one_mem
  have hCLie : g1_lieAlgebra C = g1_lieAlgebra G :=
    (congrArg g1_lieOfSet hC).trans (g1_lie_identityComponent G)
  have hILie : g1_lieAlgebra (g1_inter C H) = g1_lieAlgebra C := by
    rw [g1_lie_inf C H (g1_inter C H) rfl, inf_eq_left]
    exact hCLie ▸ hLie
  have hle := g1_le_of_lie_eq_of_dim C (g1_inter C H) hconn inf_le_left hILie
    (g1_finrank_lie_eq_krullDim C) (g1_finrank_lie_eq_krullDim (g1_inter C H))
  rw [← hC]
  exact hle.trans inf_le_right

#print axioms pel_identityComponent_subset_of_lie_le
end HodgeLean.Foundations.Program.GeneralTypeIII
