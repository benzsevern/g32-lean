import HodgeLean.Foundations.MatrixAlgGroupLie
import HodgeLean.Foundations.MatrixAlgGroupLieRecovery

noncomputable section
namespace HodgeLean.Foundations
open HodgeLean.Foundations.Program

/-- A closed set containing a nonempty relative open part of a connected
matrix algebraic group contains the whole group. -/
theorem pel_connected_group_subset_closed_of_patch {k : Type*} [Field k] {n : ℕ}
    (G : MatrixAlgGroup k n) (hG : g1_IsConnected G)
    (Z U : Set (Matrix.GeneralLinearGroup (Fin n) k))
    (hZ : @IsClosed _ (g1_zariski k n) Z)
    (hU : @IsOpen _ (g1_zariski k n) U)
    (hne : ((G.carrier : Set _) ∩ U).Nonempty)
    (hUZ : (G.carrier : Set _) ∩ U ⊆ Z) :
    (G.carrier : Set _) ⊆ Z := by
  letI := g1_zariski k n
  exact (subset_closure_inter_of_isPreirreducible_of_isOpen
    (g1_isIrreducible_of_isConnected G hG).2 hU hne).trans
      (closure_minimal hUZ hZ)

#print axioms pel_connected_group_subset_closed_of_patch
end HodgeLean.Foundations
