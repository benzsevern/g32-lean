import HodgeLean.Foundations.Program.SchoenTowerHardtCad7

/-! Finite selection of compatible cells. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_select_cells {X : Type*} {k : ℕ}
    (A B : Set X) (c : Fin k → Set X)
    (hcover : (⋃ i, c i) = A)
    (hcompat : ∀ i, c i ⊆ B ∨ Disjoint (c i) B) :
    ∃ I : Finset (Fin k), A ∩ B = ⋃ i ∈ I, c i := by
  classical
  refine ⟨Finset.univ.filter (fun i => c i ⊆ B), ?_⟩
  ext x
  constructor
  · rintro ⟨hxA, hxB⟩
    rw [← hcover] at hxA
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxA
    have hiB : c i ⊆ B := by
      rcases hcompat i with hi | hi
      · exact hi
      · exact False.elim (Set.disjoint_left.mp hi hxi hxB)
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiB⟩, hxi⟩⟩
  · intro hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hx
    exact ⟨hcover ▸ Set.mem_iUnion.mpr ⟨i, hxi⟩,
      (Finset.mem_filter.mp hi).2 hxi⟩

theorem s2v_hardt6rb_cad7_mark_selection {n m : ℕ}
    (f d : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (hd : IsCompact d.realize) (hdf : d.realize ⊆ f.realize)
    (b : Fin m → s2v_t11b_Formula n) :
    ∃ k : ℕ, ∃ c : Fin k → s2v_t11b_Formula n,
      (∀ i, (c i).realize.Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = f.realize ∧
      ∀ j, ∃ I : Finset (Fin k),
        f.realize ∩ (b j).realize = ⋃ i ∈ I, (c i).realize := by
  obtain ⟨k, c, dim, hdim, hne, hdis, hcover, hchart, hdcell, hb, hrest⟩ :=
    s2v_hardt_cad7_pair f d hf hd hdf b
  refine ⟨k, c, hne, hdis, hcover, ?_⟩
  intro j
  exact s2v_hardt6rb_select_cells _ _ _ hcover (fun i => hb i j)

end HodgeLean.Foundations.Program
