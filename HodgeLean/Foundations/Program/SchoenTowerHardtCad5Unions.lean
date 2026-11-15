import HodgeLean.Foundations.Program.SchoenTowerHardtCad5PartitionComparison
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5AdaptedUnions

/-! Finite union dimensions from a common adapted cylindrical partition. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_partition_union_dimension {n k : ℕ}
    (B : Fin k → s2v_t11b_Formula n)
    (P : (i : Fin k) → s2v_hardt_cad5_Partition (B i).realize)
    (U : s2v_hardt_cad5_Partition (⋃ i, (B i).realize)) :
    U.dimension =
      (Finset.univ.image (fun i => (P i).dimension) ∪ {-1}).max' (by simp) := by
  classical
  obtain ⟨m, c, d, e, F, I, hn, hd, hc, hb, hF, hI, ha⟩ := s2v_hardt_cad4_adapted B
  let A : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    { count := m, cell := c, dim := d, chart := e, forward := F, inverse := I
      nonempty := hn, disjoint := hd, cover := hc, bound := hb
      forward_eq := hF, inverse_eq := hI }
  have hUnion (i : Fin m) : (c i).realize ⊆ (⋃ j, (B j).realize) ∨
      Disjoint (c i).realize (⋃ j, (B j).realize) := by
    by_cases hj : ∃ j, (c i).realize ⊆ (B j).realize
    · obtain ⟨j, hj⟩ := hj
      exact Or.inl (hj.trans (Set.subset_iUnion (fun j => (B j).realize) j))
    · right
      rw [Set.disjoint_iUnion_right]
      intro j
      rcases ha i j with h | h
      · exact (hj ⟨j, h⟩).elim
      · exact h
  obtain ⟨U₀, p, _, hcell, _, _⟩ := s2v_hardt_cad5_select A
    (Set.subset_univ (⋃ j, (B j).realize)) hUnion
  have hAdapt (i : Fin U₀.count) (j : Fin k) :
      (U₀.cell i).realize ⊆ (B j).realize ∨ Disjoint (U₀.cell i).realize (B j).realize := by
    rw [hcell i]
    exact ha (p i) j
  obtain ⟨P₀, _, _, _, _, heq⟩ :=
    s2v_hardt_cad5_adapted_union_max (fun j => (B j).realize) U₀ hAdapt
  have hdims : (fun j => (P₀ j).dimension) = (fun j => (P j).dimension) := by
    funext j
    exact s2v_hardt_cad5_partition_dimension_eq (P₀ j) (P j)
  rw [hdims] at heq
  exact (s2v_hardt_cad5_partition_dimension_eq U U₀).trans heq

end HodgeLean.Foundations.Program
