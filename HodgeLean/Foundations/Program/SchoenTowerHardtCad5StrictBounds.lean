import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Unions
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5PartitionCast

/-! Strict integer bounds inherited from finite cell dimensions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_dimension_lt_of_cells {n d : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (h : ∀ i, P.dim i < d) : P.dimension < (d : ℤ) := by
  have hle : P.dimension ≤ (d : ℤ) - 1 := s2v_hardt_cad5_max_le P.dim _ (by omega) (by
    intro i
    have hi := h i
    omega)
  omega

theorem s2v_hardt_cad5_union_dimension_lt {n k d : ℕ}
    (B : Fin k → s2v_t11b_Formula n)
    (P : (i : Fin k) → s2v_hardt_cad5_Partition (B i).realize)
    (U : s2v_hardt_cad5_Partition (⋃ i, (B i).realize))
    (hP : ∀ i, (P i).dimension < (d : ℤ)) : U.dimension < (d : ℤ) := by
  classical
  rw [s2v_hardt_cad5_partition_union_dimension B P U]
  apply lt_of_le_of_lt (b := (d : ℤ) - 1)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      have hi := hP i
      omega
    · have he := Finset.mem_singleton.mp hx
      omega
  · omega

theorem s2v_hardt_cad5_fintype_union_dimension_lt {n d : ℕ} {ι : Type*} [Fintype ι]
    (B : ι → s2v_t11b_Formula n)
    (P : (i : ι) → s2v_hardt_cad5_Partition (B i).realize)
    (U : s2v_hardt_cad5_Partition (⋃ i, (B i).realize))
    (hP : ∀ i, (P i).dimension < (d : ℤ)) : U.dimension < (d : ℤ) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have h : (⋃ j : Fin (Fintype.card ι), (B (e j)).realize) = ⋃ i, (B i).realize := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨e j, hj⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨(Fintype.equivFin ι) i, ?_⟩
      have he : e ((Fintype.equivFin ι) i) = i := (Fintype.equivFin ι).symm_apply_apply i
      rw [he]
      exact hi
  let V : s2v_hardt_cad5_Partition (⋃ j : Fin (Fintype.card ι), (B (e j)).realize) := h.symm ▸ U
  have hv : V.dimension = U.dimension := s2v_hardt_cad5_cast_dimension h.symm U
  rw [← hv]
  exact s2v_hardt_cad5_union_dimension_lt (fun j => B (e j)) (fun j => P (e j)) V
    (fun j => hP (e j))

end HodgeLean.Foundations.Program
