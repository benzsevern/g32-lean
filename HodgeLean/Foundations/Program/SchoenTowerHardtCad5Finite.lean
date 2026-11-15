import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Defs

/-! Finite maxima and restriction of concrete chart partitions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_max_ge_neg_one {m : ℕ} (d : Fin m → ℕ) :
    -1 ≤ s2v_hardt_cad5_max d := by
  apply Finset.le_max'
  simp

theorem s2v_hardt_cad5_le_max {m : ℕ} (d : Fin m → ℕ) (i : Fin m) :
    (d i : ℤ) ≤ s2v_hardt_cad5_max d := by
  apply Finset.le_max'
  simp

theorem s2v_hardt_cad5_max_le {m : ℕ} (d : Fin m → ℕ) (b : ℤ)
    (hb : -1 ≤ b) (hd : ∀ i, (d i : ℤ) ≤ b) :
    s2v_hardt_cad5_max d ≤ b := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hd i
  · simpa using (Finset.mem_singleton.mp hx) ▸ hb

theorem s2v_hardt_cad5_count_eq_zero_iff {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S) :
    P.count = 0 ↔ S = ∅ := by
  constructor
  · intro h
    rw [← P.cover]
    exact Set.eq_empty_iff_forall_notMem.mpr (by simpa [h])
  · intro h
    by_contra hn
    have i : Fin P.count := ⟨0, Nat.pos_of_ne_zero hn⟩
    obtain ⟨x, hx⟩ := P.nonempty i
    have : x ∈ S := P.cover ▸ Set.mem_iUnion.mpr ⟨i, hx⟩
    simpa [h] using this

theorem s2v_hardt_cad5_dimension_empty {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (h : S = ∅) : P.dimension = -1 := by
  have hc := (s2v_hardt_cad5_count_eq_zero_iff P).mpr h
  unfold s2v_hardt_cad5_Partition.dimension s2v_hardt_cad5_max
  have : IsEmpty (Fin P.count) := by rw [hc]; infer_instance
  simp

end HodgeLean.Foundations.Program
