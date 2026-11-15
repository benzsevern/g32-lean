import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Filter
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5PartitionCast
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5StrictBounds
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5FiniteBooleanFamilies

/-! Top-cell selection and the smaller remainder in an adapted chart refinement. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_chart_top_from_refinement {n d k : ℕ}
    (C : s2v_t11b_Formula n) (Z : Fin k → s2v_t11b_Formula n)
    (PZ : s2v_hardt_cad5_Partition (⋃ j, (Z j).realize)) (hZ : PZ.dimension < (d : ℤ))
    (Q₀ : s2v_hardt_cad5_Partition C.realize) (hbound : ∀ i, Q₀.dim i ≤ d)
    (ha : ∀ i j, (Q₀.cell i).realize ⊆ (Z j).realize ∨ Disjoint (Q₀.cell i).realize (Z j).realize)
    (hopen : ∀ i, Q₀.dim i = d → IsOpen {x : C.realize | x.val ∈ (Q₀.cell i).realize}) :
    ∃ P : s2v_hardt_cad5_Partition (C.realize \ ⋃ j, (Z j).realize),
    ∃ R : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition R.realize,
      (∀ i, P.dim i ≤ d) ∧
      (∀ i, P.dim i = d → IsOpen {x : C.realize | x.val ∈ (P.cell i).realize}) ∧
      R.realize = C.realize \ (⋃ i : {i : Fin P.count // P.dim i = d}, (P.cell i.val).realize) ∧
      Q.dimension < (d : ℤ) := by
  classical
  have hsub (i : Fin Q₀.count) : (Q₀.cell i).realize ⊆ C.realize := by
    intro x hx
    have hu : x ∈ ⋃ j, (Q₀.cell j).realize := Set.mem_iUnion.mpr ⟨i, hx⟩
    simpa only [Q₀.cover] using hu
  have hAdapt (i : Fin Q₀.count) :
      (Q₀.cell i).realize ⊆ (C.realize \ ⋃ j, (Z j).realize) ∨
      Disjoint (Q₀.cell i).realize (C.realize \ ⋃ j, (Z j).realize) := by
    by_cases hz : ∃ j, (Q₀.cell i).realize ⊆ (Z j).realize
    · right
      obtain ⟨j, hj⟩ := hz
      exact Set.disjoint_left.mpr (fun x hxi hx => hx.2 (Set.mem_iUnion.mpr ⟨j, hj hxi⟩))
    · left
      intro x hx
      refine ⟨hsub i hx, ?_⟩
      intro hxZ
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxZ
      rcases ha i j with h | h
      · exact hz ⟨j, h⟩
      · exact Set.disjoint_left.mp h hx hj
  obtain ⟨P, parent, _, hcell, hdim, _⟩ := s2v_hardt_cad5_select Q₀
    (fun _ h => h.1) hAdapt
  have hPbound (i : Fin P.count) : P.dim i ≤ d := (hdim i).trans_le (hbound (parent i))
  have hPopen (i : Fin P.count) (hi : P.dim i = d) :
      IsOpen {x : C.realize | x.val ∈ (P.cell i).realize} := by
    rw [hcell i]
    exact hopen (parent i) ((hdim i).symm.trans hi)
  obtain ⟨topF, hTop⟩ := s2v_hardt_cad5_finite_union_formula
    (fun i : {i : Fin P.count // P.dim i = d} => P.cell i.val)
  let R : s2v_t11b_Formula n := .inter C (.compl topF)
  have hR : R.realize = C.realize \ (⋃ i : {i : Fin P.count // P.dim i = d}, (P.cell i.val).realize) := by
    change C.realize ∩ topF.realizeᶜ = _
    rw [hTop]
    rfl
  obtain ⟨QR⟩ := s2v_hardt_cad5_partition_exists R
  obtain ⟨PL, pL, hcellL, hdimL⟩ := s2v_hardt_cad5_filter_cells P (fun i => P.dim i < d)
  have hPL : PL.dimension < (d : ℤ) := s2v_hardt_cad5_dimension_lt_of_cells PL (by
    intro i
    rw [hdimL i]
    exact (pL i).property)
  obtain ⟨ZF, hZF⟩ := s2v_hardt_cad5_finite_union_formula Z
  obtain ⟨LF, hLF⟩ := s2v_hardt_cad5_finite_union_formula
    (fun i : {i : Fin P.count // P.dim i < d} => P.cell i.val)
  let PZF : s2v_hardt_cad5_Partition ZF.realize := hZF.symm ▸ PZ
  let PLF : s2v_hardt_cad5_Partition LF.realize := hLF.symm ▸ PL
  have hPZF : PZF.dimension < (d : ℤ) :=
    (s2v_hardt_cad5_cast_dimension hZF.symm PZ).trans_lt hZ
  have hPLF : PLF.dimension < (d : ℤ) :=
    (s2v_hardt_cad5_cast_dimension hLF.symm PL).trans_lt hPL
  let B : Fin 2 → s2v_t11b_Formula n := Fin.cases ZF (fun _ : Fin 1 => LF)
  let PB : (i : Fin 2) → s2v_hardt_cad5_Partition (B i).realize :=
    Fin.cases PZF (fun _ : Fin 1 => PLF)
  have hPB : ∀ i, (PB i).dimension < (d : ℤ) :=
    Fin.cases hPZF (fun _ : Fin 1 => hPLF)
  obtain ⟨UF, hUF⟩ := s2v_hardt_cad5_finite_union_formula B
  obtain ⟨PU⟩ := s2v_hardt_cad5_partition_exists UF
  let PU' : s2v_hardt_cad5_Partition (⋃ i, (B i).realize) := hUF ▸ PU
  have hPU' := s2v_hardt_cad5_union_dimension_lt B PB PU' hPB
  have hPU : PU.dimension < (d : ℤ) :=
    (s2v_hardt_cad5_cast_dimension hUF PU).symm.trans_lt hPU'
  have hsubR : R.realize ⊆ UF.realize := by
    intro x hx
    have hxR : x ∈ C.realize \ (⋃ i : {i : Fin P.count // P.dim i = d}, (P.cell i.val).realize) := by
      simpa only [hR] using hx
    rw [hUF]
    by_cases hxZ : x ∈ ⋃ j, (Z j).realize
    · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
      change x ∈ ZF.realize
      rw [hZF]
      exact hxZ
    · have hxP : x ∈ ⋃ i, (P.cell i).realize := by
        simpa only [P.cover] using (show x ∈ C.realize \ ⋃ j, (Z j).realize from ⟨hxR.1, hxZ⟩)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxP
      have hlow : P.dim i < d := by
        have hb := hPbound i
        by_contra h
        have he : P.dim i = d := by omega
        exact hxR.2 (Set.mem_iUnion.mpr ⟨⟨i, he⟩, hi⟩)
      refine Set.mem_iUnion.mpr ⟨1, ?_⟩
      change x ∈ LF.realize
      rw [hLF]
      exact Set.mem_iUnion.mpr ⟨⟨i, hlow⟩, hi⟩
  exact ⟨P, R, QR, hPbound, hPopen, hR,
    (s2v_hardt_cad5_partition_dimension_mono QR PU hsubR).trans_lt hPU⟩

end HodgeLean.Foundations.Program
