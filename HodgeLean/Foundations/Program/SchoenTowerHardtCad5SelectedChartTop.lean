import HodgeLean.Foundations.Program.SchoenTowerHardtCad5OpenChartRefinement
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ChartTopRefinement
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5UnionAssembly

/-! Selection of full-dimensional cells in a recorded chart outside one exceptional set. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_selected_chart_top {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (i : Fin P.count) (Z : s2v_t11b_Formula n)
    (PZ : s2v_hardt_cad5_Partition Z.realize) (hZ : PZ.dimension < (P.dim i : ℤ)) :
    ∃ T : Set (EuclideanSpace ℝ (Fin n)), ∃ PT : s2v_hardt_cad5_Partition T,
    ∃ R : s2v_t11b_Formula n, ∃ PR : s2v_hardt_cad5_Partition R.realize,
      T ⊆ (P.cell i).realize \ Z.realize ∧
      (∀ j, PT.dim j = P.dim i) ∧
      (∀ j, IsOpen {x : (P.cell i).realize | x.val ∈ (PT.cell j).realize}) ∧
      R.realize = (P.cell i).realize \ T ∧ PR.dimension < (P.dim i : ℤ) := by
  classical
  let Zs : Fin 1 → s2v_t11b_Formula n := fun _ => Z
  have hz : (⋃ j, (Zs j).realize) = Z.realize := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact hj
    · intro hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
  let PZs : s2v_hardt_cad5_Partition (⋃ j, (Zs j).realize) := hz.symm ▸ PZ
  have hZs : PZs.dimension < (P.dim i : ℤ) :=
    (s2v_hardt_cad5_cast_dimension hz.symm PZ).trans_lt hZ
  obtain ⟨Q₀, hbound, ha, hopen⟩ := s2v_hardt_cad5_open_chart_refinement
    (P.cell i) (P.chart i) (P.forward i) (P.forward_eq i) (P.inverse i) (P.inverse_eq i) Zs
  obtain ⟨Q, R, PR, _, ho, hR, hPR⟩ := s2v_hardt_cad5_chart_top_from_refinement
    (P.cell i) Zs PZs hZs Q₀ hbound ha hopen
  obtain ⟨PT, e, hec, hed⟩ := s2v_hardt_cad5_filter_cells Q (fun j => Q.dim j = P.dim i)
  refine ⟨_, PT, R, PR, ?_, ?_, ?_, hR, hPR⟩
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    have hu : x ∈ ⋃ l, (Q.cell l).realize := Set.mem_iUnion.mpr ⟨j.val, hj⟩
    have h : x ∈ (P.cell i).realize \ ⋃ j, (Zs j).realize := by
      simpa only [Q.cover] using hu
    simpa only [hz] using h
  · intro j
    exact (hed j).trans (e j).property
  · intro j
    rw [hec j]
    exact ho (e j).val (e j).property

end HodgeLean.Foundations.Program
