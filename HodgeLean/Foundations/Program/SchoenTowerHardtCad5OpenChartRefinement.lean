import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ChartDimension
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ChartTransport
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5OpenCad

/-! Adapted chart refinements with relatively open top-dimensional cells. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_open_chart_refinement {n d k : ℕ}
    (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ (x : C.realize) (z : EuclideanSpace ℝ (Fin d)),
      WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ G.realize ↔ z = (e x).val)
    (J : s2v_t11b_Formula (d + n))
    (hJ : ∀ (z : {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
      (x : EuclideanSpace ℝ (Fin n)),
      WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ J.realize ↔ x = (e.symm z).val)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ Q : s2v_hardt_cad5_Partition C.realize,
      (∀ i, Q.dim i ≤ d) ∧
      (∀ i j, (Q.cell i).realize ⊆ (B j).realize ∨ Disjoint (Q.cell i).realize (B j).realize) ∧
      (∀ i, Q.dim i = d → IsOpen {x : C.realize | x.val ∈ (Q.cell i).realize}) := by
  classical
  have hdn := s2v_hardt_cad5_chart_dimension_le_ambient C e J hJ
  obtain ⟨box, hbox⟩ := s2v_hardt_cad5_box_formula d
  obtain ⟨A, hA⟩ := s2v_hardt_cad4_pre_images C e G hG B
  let marks : Fin (k + 1) → s2v_t11b_Formula d := Fin.cases box A
  obtain ⟨P, ha, hopen⟩ := s2v_hardt_cad5_adapted_open_cad marks
  obtain ⟨PB, p, _, hcell, hdim, _⟩ := s2v_hardt_cad5_select P
    (Set.subset_univ {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1}) (by
      intro i
      simpa only [marks, Fin.cases_zero, hbox] using ha i 0)
  have haPB (i : Fin PB.count) (j : Fin k) :
      (PB.cell i).realize ⊆ (A j).realize ∨ Disjoint (PB.cell i).realize (A j).realize := by
    rw [hcell i]
    simpa only [marks, Fin.cases_succ] using ha (p i) j.succ
  have hOpenPB (i : Fin PB.count) (hi : PB.dim i = d) : IsOpen (PB.cell i).realize := by
    rw [hcell i]
    exact hopen (p i) ((hdim i).symm.trans hi)
  obtain ⟨Q, f, hdimQ, hmembership, hDim, hOpenQ⟩ :=
    s2v_hardt_cad5_chart_partition_transport C e G hG J hJ hdn PB
  have hsub (i : Fin Q.count) : (Q.cell i).realize ⊆ C.realize := by
    intro x hx
    have hu : x ∈ ⋃ j, (Q.cell j).realize := Set.mem_iUnion.mpr ⟨i, hx⟩
    simpa only [Q.cover] using hu
  refine ⟨Q, fun i => (hdimQ i).trans_le (PB.bound (f i)), ?_, ?_⟩
  · intro i j
    rcases haPB (f i) j with h | h
    · left
      intro x hx
      let a : C.realize := ⟨x, hsub i hx⟩
      have hmem := h ((hmembership i a).mp hx)
      obtain ⟨b, hb, he⟩ := (hA j (e a).val).mp hmem
      have hab : a = b := e.injective (Subtype.ext he)
      change a.val ∈ (B j).realize
      rw [hab]
      exact hb
    · right
      apply Set.disjoint_left.mpr
      intro x hx hxB
      let a : C.realize := ⟨x, hsub i hx⟩
      have hmem := (hmembership i a).mp hx
      have hA' : (e a).val ∈ (A j).realize := (hA j _).mpr ⟨a, hxB, rfl⟩
      exact Set.disjoint_left.mp h hmem hA'
  · intro i hi
    exact hOpenQ i (hOpenPB (f i) ((hdimQ i).symm.trans hi))

end HodgeLean.Foundations.Program
