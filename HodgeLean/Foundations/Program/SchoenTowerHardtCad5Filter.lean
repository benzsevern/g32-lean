import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Finite

/-! Exact finite subfamily partitions and dimension bounds for their recorded cells. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_filter_cells {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (keep : Fin P.count → Prop) :
    ∃ Q : s2v_hardt_cad5_Partition (⋃ i : {i : Fin P.count // keep i}, (P.cell i.val).realize),
    ∃ p : Fin Q.count ≃ {i : Fin P.count // keep i},
      (∀ j, Q.cell j = P.cell (p j).val) ∧ (∀ j, Q.dim j = P.dim (p j).val) := by
  classical
  let A := {i : Fin P.count // keep i}
  let enum := (Fintype.equivFin A).symm
  have hc : (⋃ j : Fin (Fintype.card A), (P.cell (enum j).val).realize) =
      ⋃ i : A, (P.cell i.val).realize := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨enum j, hj⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨(Fintype.equivFin A) i, ?_⟩
      have he : enum ((Fintype.equivFin A) i) = i := (Fintype.equivFin A).symm_apply_apply i
      rw [he]
      exact hi
  let Q : s2v_hardt_cad5_Partition (⋃ i : A, (P.cell i.val).realize) :=
    { count := Fintype.card A
      cell := fun j => P.cell (enum j).val
      dim := fun j => P.dim (enum j).val
      chart := fun j => P.chart (enum j).val
      forward := fun j => P.forward (enum j).val
      inverse := fun j => P.inverse (enum j).val
      nonempty := fun j => P.nonempty (enum j).val
      disjoint := fun _ _ h => P.disjoint (fun he => h (enum.injective (Subtype.ext he)))
      cover := hc
      bound := fun j => P.bound (enum j).val
      forward_eq := fun j => P.forward_eq (enum j).val
      inverse_eq := fun j => P.inverse_eq (enum j).val }
  exact ⟨Q, enum, fun _ => rfl, fun _ => rfl⟩

end HodgeLean.Foundations.Program
