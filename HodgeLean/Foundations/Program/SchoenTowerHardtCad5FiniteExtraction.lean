import HodgeLean.Foundations.Program.SchoenTowerHardtCad5FiniteCases

/-! Top-cell extraction for finite Boolean carriers. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_finite_partition_top {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) (hS : S.realize.Finite) :
    ∃ Z : s2v_t11b_Formula n, ∃ PZ : s2v_hardt_cad5_Partition Z.realize,
    ∃ U : s2v_t11b_Formula n, ∃ PU : s2v_hardt_cad5_Partition U.realize,
    ∃ R : s2v_t11b_Formula n, ∃ PR : s2v_hardt_cad5_Partition R.realize,
    ∃ parent : Fin PU.count → Fin P.count,
      Z.realize =
        (⋃ i, closure (P.cell i).realize \ (P.cell i).realize) ∪
        (⋃ i : {i : Fin P.count // (P.dim i : ℤ) < P.dimension},
          closure (P.cell i.val).realize) ∧
      (S.realize.Nonempty → PZ.dimension < P.dimension) ∧
      (∀ i, (PU.dim i : ℤ) = P.dimension ∧
        (P.dim (parent i) : ℤ) = P.dimension) ∧
      (∀ i, (PU.cell i).realize ⊆ (P.cell (parent i)).realize \ Z.realize) ∧
      (∀ i, IsOpen {x : S.realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i, IsOpen {x : (P.cell (parent i)).realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i j, i ≠ j → Disjoint (PU.cell j).realize (closure (PU.cell i).realize)) ∧
      R.realize = S.realize \ U.realize ∧
      (S.realize.Nonempty → PR.dimension < P.dimension) ∧
      (S.realize = ∅ → PU.count = 0 ∧ R.realize = ∅ ∧ PR.dimension = -1) := by
  classical
  let E : s2v_t11b_Formula n := .compl (.nonneg 0)
  have hE : E.realize = ∅ := by ext x; simp [E, s2v_t11b_Formula.realize]
  obtain ⟨PE⟩ := s2v_hardt_cad5_partition_exists E
  have hPE : PE.dimension = -1 := s2v_hardt_cad5_dimension_empty PE hE
  have hcell (i : Fin P.count) : (P.cell i).realize.Finite := by
    apply hS.subset
    intro x hx
    rw [← P.cover]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have hdim (i : Fin P.count) : (P.dim i : ℤ) = P.dimension := by
    have hn : S.realize.Nonempty := by
      obtain ⟨x, hx⟩ := P.nonempty i
      exact ⟨x, P.cover ▸ Set.mem_iUnion.mpr ⟨i, hx⟩⟩
    rw [s2v_hardt_cad5_finite_cell_dim P hS i,
      s2v_hardt_cad5_finite_dimension P hS hn]
    rfl
  have hz :
      (⋃ i, closure (P.cell i).realize \ (P.cell i).realize) ∪
      (⋃ i : {i : Fin P.count // (P.dim i : ℤ) < P.dimension},
        closure (P.cell i.val).realize) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rw [(hcell i).isClosed.closure_eq] at hi
      exact hi.2 hi.1
    · obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
      have hi := i.property
      rw [hdim i.val] at hi
      exact (lt_irrefl P.dimension) hi
  have hsmall : S.realize.Nonempty → PE.dimension < P.dimension := by
    intro hn
    rw [hPE, s2v_hardt_cad5_finite_dimension P hS hn]
    norm_num
  letI : Finite S.realize := hS.to_subtype
  refine ⟨E, PE, S, P, E, PE, id, hE.trans hz.symm, hsmall,
    fun i => ⟨hdim i, hdim i⟩, ?_, ?_, ?_, ?_, ?_, hsmall, ?_⟩
  · intro i x hx
    exact ⟨hx, by simp [hE]⟩
  · intro i
    exact isOpen_discrete _
  · intro i
    change IsOpen {x : (P.cell i).realize | x.val ∈ (P.cell i).realize}
    have : {x : (P.cell i).realize | x.val ∈ (P.cell i).realize} = Set.univ := by
      ext x; simp
    rw [this]
    exact isOpen_univ
  · intro i j hij
    rw [(hcell i).isClosed.closure_eq]
    exact (P.disjoint hij).symm
  · rw [hE, Set.sdiff_self]
  · intro hs
    exact ⟨(s2v_hardt_cad5_count_eq_zero_iff P).mpr hs, hE, hPE⟩

end HodgeLean.Foundations.Program
