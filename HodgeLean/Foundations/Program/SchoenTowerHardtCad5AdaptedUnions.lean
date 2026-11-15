import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Restriction

/-! Integer maxima for subfamilies selected from one adapted partition. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_adapted_union_max {n k : ℕ}
    (B : Fin k → Set (EuclideanSpace ℝ (Fin n)))
    (U : s2v_hardt_cad5_Partition (⋃ i, B i))
    (ha : ∀ i j, (U.cell i).realize ⊆ B j ∨ Disjoint (U.cell i).realize (B j)) :
    ∃ P : (j : Fin k) → s2v_hardt_cad5_Partition (B j),
    ∃ parent : (j : Fin k) → Fin (P j).count → Fin U.count,
      (∀ j, Function.Injective (parent j)) ∧
      (∀ j i, (P j).cell i = U.cell (parent j i)) ∧
      (∀ j i, (P j).dim i = U.dim (parent j i)) ∧
      U.dimension =
        (Finset.univ.image (fun j => (P j).dimension) ∪ {-1}).max' (by simp) := by
  classical
  choose P parent hinj hcell hdim hle using fun j =>
    s2v_hardt_cad5_select U (Set.subset_iUnion B j) (fun i => ha i j)
  refine ⟨P, parent, hinj, hcell, hdim, ?_⟩
  let D := (Finset.univ.image (fun j => (P j).dimension) ∪ {-1}).max' (by simp)
  have hm (j : Fin k) : (P j).dimension ≤ D := by
    apply Finset.le_max'
    simp
  have hn : -1 ≤ D := by apply Finset.le_max'; simp
  apply le_antisymm
  · apply s2v_hardt_cad5_max_le U.dim D hn
    intro i
    obtain ⟨x, hx⟩ := U.nonempty i
    have hxU : x ∈ ⋃ j, B j := U.cover ▸ Set.mem_iUnion.mpr ⟨i, hx⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxU
    rw [← (P j).cover] at hj
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hj
    rw [hcell j l] at hl
    have heq : parent j l = i := by
      by_contra hne
      exact Set.disjoint_left.mp (U.disjoint hne) hl hx
    have hd : (U.dim i : ℤ) ≤ (P j).dimension := by
      rw [← heq, ← hdim j l]
      exact s2v_hardt_cad5_le_max (P j).dim l
    exact hd.trans (hm j)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact hle j
    · rw [Finset.mem_singleton.mp hx]
      exact s2v_hardt_cad5_max_ge_neg_one U.dim

end HodgeLean.Foundations.Program
