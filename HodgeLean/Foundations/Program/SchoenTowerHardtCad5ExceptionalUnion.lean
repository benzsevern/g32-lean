import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Boolean
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5CellPartition
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5BoundaryDimension
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ClosureDimension
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5StrictBounds
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5FiniteBooleanFamilies

/-! The finite exceptional union of cell boundaries and lower-dimensional cell limits. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_exceptional_union {n d : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (hd : P.dimension = (d : ℤ)) :
    ∃ Z : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition Z.realize,
      Z.realize =
        (⋃ i, closure (P.cell i).realize \ (P.cell i).realize) ∪
        (⋃ i : {i : Fin P.count // (P.dim i : ℤ) < P.dimension},
          closure (P.cell i.val).realize) ∧ Q.dimension < (d : ℤ) := by
  classical
  have hc (i : Fin P.count) := s2v_hardt_cad5_cell_partition P i
  choose PC hPC using hc
  have hb (i : Fin P.count) := s2v_hardt_cad5_boundary_partition (P.cell i)
  choose B PB hB using hb
  have hbDim (i : Fin P.count) : (PB i).dimension < (d : ℤ) := by
    have h := s2v_hardt_cad5_boundary_dimension_lt (P.cell i) (PC i) (B i) (PB i)
      (hB i) (P.nonempty i)
    rw [hPC i] at h
    exact h.trans_le ((s2v_hardt_cad5_le_max P.dim i).trans_eq hd)
  have hc (i : Fin P.count) := s2v_hardt_cad5_closure_partition (P.cell i)
  choose C QC hC using hc
  have hcDim (i : Fin P.count) : (QC i).dimension ≤ (P.dim i : ℤ) := by
    have h := s2v_hardt_cad5_closure_dimension_le (P.cell i) (PC i) (C i) (QC i) (hC i)
    rwa [hPC i] at h
  let I := Fin P.count ⊕ {i : Fin P.count // (P.dim i : ℤ) < P.dimension}
  let F : I → s2v_t11b_Formula n := Sum.elim B (fun i => C i.val)
  let PF : (i : I) → s2v_hardt_cad5_Partition (F i).realize :=
    fun i => match i with
      | .inl j => PB j
      | .inr j => QC j.val
  have hPF (i : I) : (PF i).dimension < (d : ℤ) := by
    cases i with
    | inl j => exact hbDim j
    | inr j => exact (hcDim j.val).trans_lt (j.property.trans_eq hd)
  obtain ⟨Z, hZ⟩ := s2v_hardt_cad5_finite_union_formula F
  obtain ⟨Q⟩ := s2v_hardt_cad5_partition_exists Z
  let Q' : s2v_hardt_cad5_Partition (⋃ i, (F i).realize) := hZ ▸ Q
  have hQ' := s2v_hardt_cad5_fintype_union_dimension_lt F PF Q' hPF
  refine ⟨Z, Q, ?_, (s2v_hardt_cad5_cast_dimension hZ Q).symm.trans_lt hQ'⟩
  rw [hZ]
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    cases i with
    | inl i =>
      left
      exact Set.mem_iUnion.mpr ⟨i, (hB i) ▸ hi⟩
    | inr i =>
      right
      exact Set.mem_iUnion.mpr ⟨i, (hC i.val) ▸ hi⟩
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨Sum.inl i, (hB i).symm ▸ hi⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨Sum.inr i, (hC i.val).symm ▸ hi⟩

end HodgeLean.Foundations.Program
