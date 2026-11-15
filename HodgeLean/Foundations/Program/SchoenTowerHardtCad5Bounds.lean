import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Finite

/-! Bounds and inhabited maximal cells for the integer dimension record. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_dimension_nonneg {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (hS : S.Nonempty) : 0 ≤ P.dimension := by
  obtain ⟨x, hx⟩ := hS
  rw [← P.cover] at hx
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
  exact le_trans (Int.natCast_nonneg _) (s2v_hardt_cad5_le_max P.dim i)

theorem s2v_hardt_cad5_dimension_le_ambient {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S) :
    P.dimension ≤ (n : ℤ) := by
  apply s2v_hardt_cad5_max_le
  · omega
  · intro i
    exact_mod_cast P.bound i

theorem s2v_hardt_cad5_dimension_eq_neg_one_iff {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S) :
    P.dimension = -1 ↔ S = ∅ := by
  constructor
  · intro h
    by_contra hn
    have := s2v_hardt_cad5_dimension_nonneg P (Set.nonempty_iff_ne_empty.mpr hn)
    omega
  · exact s2v_hardt_cad5_dimension_empty P

theorem s2v_hardt_cad5_maximal_cell {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (hS : S.Nonempty) : ∃ i, (P.dim i : ℤ) = P.dimension := by
  classical
  have hm : P.dimension ∈
      Finset.univ.image (fun i => (P.dim i : ℤ)) ∪ {-1} := Finset.max'_mem _ (by simp)
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    exact ⟨i, hi⟩
  · have h := s2v_hardt_cad5_dimension_nonneg P hS
    have := Finset.mem_singleton.mp hm
    omega

end HodgeLean.Foundations.Program
