import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ExceptionalUnion
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5SelectedChartTop
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5RelativeOpens
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Separation

/-! Assembly of top cells from the maximal-dimensional parents. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_partition_top_assembly {n d : ℕ}
    (S : s2v_t11b_Formula n) (P : s2v_hardt_cad5_Partition S.realize)
    (hd : P.dimension = (d : ℤ))
    (Z : s2v_t11b_Formula n) (PZ : s2v_hardt_cad5_Partition Z.realize)
    (hZ : Z.realize =
      (⋃ i, closure (P.cell i).realize \ (P.cell i).realize) ∪
      (⋃ i : {i : Fin P.count // (P.dim i : ℤ) < P.dimension}, closure (P.cell i.val).realize))
    (hPZ : PZ.dimension < (d : ℤ)) :
    ∃ U : s2v_t11b_Formula n, ∃ PU : s2v_hardt_cad5_Partition U.realize,
    ∃ R : s2v_t11b_Formula n, ∃ PR : s2v_hardt_cad5_Partition R.realize,
    ∃ parent : Fin PU.count → Fin P.count,
      (∀ i, (PU.dim i : ℤ) = P.dimension ∧ (P.dim (parent i) : ℤ) = P.dimension) ∧
      (∀ i, (PU.cell i).realize ⊆ (P.cell (parent i)).realize \ Z.realize) ∧
      (∀ i, IsOpen {x : S.realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i, IsOpen {x : (P.cell (parent i)).realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i j, i ≠ j → Disjoint (PU.cell j).realize (closure (PU.cell i).realize)) ∧
      R.realize = S.realize \ U.realize ∧ PR.dimension < P.dimension := by
  classical
  let Top := {i : Fin P.count // P.dim i = d}
  have hlocal (t : Top) :
      ∃ T : Set (EuclideanSpace ℝ (Fin n)), ∃ PT : s2v_hardt_cad5_Partition T,
      ∃ R : s2v_t11b_Formula n, ∃ PR : s2v_hardt_cad5_Partition R.realize,
        T ⊆ (P.cell t.val).realize \ Z.realize ∧
        (∀ j, PT.dim j = P.dim t.val) ∧
        (∀ j, IsOpen {x : (P.cell t.val).realize | x.val ∈ (PT.cell j).realize}) ∧
        R.realize = (P.cell t.val).realize \ T ∧ PR.dimension < (P.dim t.val : ℤ) := by
    apply s2v_hardt_cad5_selected_chart_top P t.val Z PZ
    simpa only [t.property] using hPZ
  choose T PT RT PRT hsub hdim hopen hrem hsmall using hlocal
  have hTdis : Pairwise (fun t u : Top => Disjoint (T t) (T u)) := by
    intro t u htu
    exact (P.disjoint (fun h => htu (Subtype.ext h))).mono
      (fun _ hx => (hsub t hx).1) (fun _ hx => (hsub u hx).1)
  obtain ⟨U, PU, e, hec, hed, hU⟩ := s2v_hardt_cad5_assemble_disjoint_partitions T PT hTdis
  let parent (i : Fin PU.count) : Fin P.count := (e i).1.val
  have hPTsub (t : Top) (j : Fin (PT t).count) : ((PT t).cell j).realize ⊆ T t := by
    intro x hx
    have hu : x ∈ ⋃ l, ((PT t).cell l).realize := Set.mem_iUnion.mpr ⟨j, hx⟩
    simpa only [(PT t).cover] using hu
  have hPUsub (i : Fin PU.count) :
      (PU.cell i).realize ⊆ (P.cell (parent i)).realize \ Z.realize := by
    rw [hec i]
    exact (hPTsub (e i).1 (e i).2).trans (hsub (e i).1)
  have hPUopen (i : Fin PU.count) :
      IsOpen {x : (P.cell (parent i)).realize | x.val ∈ (PU.cell i).realize} := by
    rw [hec i]
    exact hopen (e i).1 (e i).2
  have hPsub (i : Fin P.count) : (P.cell i).realize ⊆ S.realize := by
    intro x hx
    have hu : x ∈ ⋃ l, (P.cell l).realize := Set.mem_iUnion.mpr ⟨i, hx⟩
    simpa only [P.cover] using hu
  have hPUambient (i : Fin PU.count) : (PU.cell i).realize ⊆ S.realize :=
    (fun _ hx => hPsub (parent i) (hPUsub i hx).1)
  have hPUwhole (i : Fin PU.count) :
      IsOpen {x : S.realize | x.val ∈ (PU.cell i).realize} := by
    apply s2v_hardt_cad5_relative_open_in_union (fun j => (P.cell j).realize)
      P.cover (parent i) (fun _ hx => (hPUsub i hx).1) (hPUopen i)
    intro j hji
    apply s2v_hardt_cad5_cross_parent_separation (A := (P.cell j).realize)
      (C := (P.cell j).realize) Set.Subset.rfl
    · exact (P.disjoint hji.symm).mono_left (fun _ hx => (hPUsub i hx).1)
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      apply (hPUsub i hxi).2
      rw [hZ]
      exact Or.inl (Set.mem_iUnion.mpr ⟨j, hxj⟩)
  let R : s2v_t11b_Formula n := .inter S (.compl U)
  have hR : R.realize = S.realize \ U.realize := rfl
  obtain ⟨PR⟩ := s2v_hardt_cad5_partition_exists R
  let B : Option Top → s2v_t11b_Formula n := fun o => match o with
    | none => Z
    | some t => RT t
  let PB : (o : Option Top) → s2v_hardt_cad5_Partition (B o).realize := fun o => match o with
    | none => PZ
    | some t => PRT t
  have hPB (o : Option Top) : (PB o).dimension < (d : ℤ) := by
    cases o with
    | none => exact hPZ
    | some t => simpa only [t.property] using hsmall t
  obtain ⟨V, hV⟩ := s2v_hardt_cad5_finite_union_formula B
  obtain ⟨PV⟩ := s2v_hardt_cad5_partition_exists V
  let PV' : s2v_hardt_cad5_Partition (⋃ o, (B o).realize) := hV ▸ PV
  have hPV' := s2v_hardt_cad5_fintype_union_dimension_lt B PB PV' hPB
  have hPV : PV.dimension < (d : ℤ) :=
    (s2v_hardt_cad5_cast_dimension hV PV).symm.trans_lt hPV'
  have hRV : R.realize ⊆ V.realize := by
    intro x hx
    have hxR : x ∈ S.realize \ U.realize := hx
    have hxP : x ∈ ⋃ i, (P.cell i).realize := by simpa only [P.cover] using hxR.1
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxP
    rw [hV]
    by_cases hlow : (P.dim i : ℤ) < P.dimension
    · refine Set.mem_iUnion.mpr ⟨none, ?_⟩
      change x ∈ Z.realize
      rw [hZ]
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, hlow⟩, subset_closure hi⟩)
    · have he : P.dim i = d := by
        have hle : (P.dim i : ℤ) ≤ P.dimension := s2v_hardt_cad5_le_max P.dim i
        rw [hd] at hle hlow
        omega
      let t : Top := ⟨i, he⟩
      refine Set.mem_iUnion.mpr ⟨some t, ?_⟩
      change x ∈ (RT t).realize
      rw [hrem t]
      refine ⟨hi, ?_⟩
      intro ht
      apply hxR.2
      rw [hU]
      exact Set.mem_iUnion.mpr ⟨t, ht⟩
  refine ⟨U, PU, R, PR, parent, ?_, hPUsub, hPUwhole, hPUopen, ?_, hR, ?_⟩
  · intro i
    have hdpar : P.dim (parent i) = d := (e i).1.property
    constructor
    · rw [hed i, hdim (e i).1 (e i).2, (e i).1.property, hd]
    · rw [hdpar, hd]
  · intro i j hij
    exact s2v_hardt_cad5_relative_separation (hPUambient i) (hPUambient j)
      (hPUwhole j) (PU.disjoint hij.symm)
  · rw [hd]
    exact (s2v_hardt_cad5_partition_dimension_mono PR PV hRV).trans_lt hPV

end HodgeLean.Foundations.Program
