import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Bounds

/-! Single-cell partitions retaining the recorded chart and dimension. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_cell_partition {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (i : Fin P.count) :
    ∃ Q : s2v_hardt_cad5_Partition (P.cell i).realize,
      Q.dimension = (P.dim i : ℤ) := by
  let Q : s2v_hardt_cad5_Partition (P.cell i).realize :=
    { count := 1
      cell := fun _ => P.cell i
      dim := fun _ => P.dim i
      chart := fun _ => P.chart i
      forward := fun _ => P.forward i
      inverse := fun _ => P.inverse i
      nonempty := fun _ => P.nonempty i
      disjoint := by intro a b h; exact (h (Subsingleton.elim a b)).elim
      cover := by
        ext x
        constructor
        · intro hx
          obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
          exact ha
        · intro hx
          exact Set.mem_iUnion.mpr ⟨0, hx⟩
      bound := fun _ => P.bound i
      forward_eq := fun _ => P.forward_eq i
      inverse_eq := fun _ => P.inverse_eq i }
  refine ⟨Q, le_antisymm ?_ ?_⟩
  · exact s2v_hardt_cad5_max_le Q.dim _ (by omega) (fun _ => le_rfl)
  · exact s2v_hardt_cad5_le_max Q.dim 0

end HodgeLean.Foundations.Program
