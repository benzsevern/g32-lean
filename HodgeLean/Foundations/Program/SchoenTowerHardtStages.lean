import HodgeLean.Foundations.Program.SchoenTowerT11bRealImageFormula

/-! Dimension stages of a supplied finite frontier partition. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Frontier incidence makes each dimension stage compact.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.5, stage consequence;
Bochnak–Coste–Roy, Real Algebraic Geometry, Chapter 9, stratification. -/
theorem s2v_hardt_stage_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    {k : ℕ} (A D : Set X) (c : Fin k → Set X) (dim : Fin k → ℕ)
    (hA : IsCompact A) (hD : IsCompact D) (hDA : D ⊆ A)
    (hc : (⋃ i, c i) = A)
    (hcompat : ∀ i, c i ⊆ D ∨ Disjoint (c i) D)
    (hfront : ∀ i j, (c j ∩ closure (c i)).Nonempty →
      c j ⊆ closure (c i) ∧ (j = i ∨ dim j < dim i)) (r : ℕ) :
    IsCompact (D ∪ ⋃ i ∈ {i | Disjoint (c i) D ∧ dim i < r}, c i) := by
  let S := D ∪ ⋃ i ∈ {i | Disjoint (c i) D ∧ dim i < r}, c i
  have hsub : S ⊆ A := by
    rintro x (hx | hx)
    · exact hDA hx
    · obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp hx
      rw [← hc]
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hboundary : ∀ i, Disjoint (c i) D ∧ dim i < r → closure (c i) ⊆ S := by
    intro i hi x hx
    have hxiA : x ∈ A := (closure_minimal (by
      intro y hy
      rw [← hc]
      exact Set.mem_iUnion.mpr ⟨i, hy⟩) hA.isClosed) hx
    rw [← hc] at hxiA
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxiA
    rcases hcompat j with hDj | hDj
    · exact Or.inl (hDj hj)
    · apply Or.inr
      apply Set.mem_iUnion₂.mpr
      refine ⟨j, ⟨hDj, ?_⟩, hj⟩
      rcases (hfront i j ⟨x, hj, hx⟩).2 with he | he
      · simpa [he] using hi.2
      · exact lt_trans he hi.2
  have hclosed : IsClosed S := by
    apply isClosed_of_closure_subset
    dsimp [S]
    rw [closure_union, hD.isClosed.closure_eq, closure_iUnion_of_finite]
    rintro x (hx | hx)
    · exact Or.inl hx
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rw [closure_iUnion_of_finite] at hi
      obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hi
      exact hboundary i h hh
  exact hA.of_isClosed_subset hclosed hsub

/-- Boolean syntax for a supplied dimension stage, without geometric assumptions.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite Boolean operations;
Bochnak–Coste–Roy, Real Algebraic Geometry, Chapter 9, preparation. -/
theorem s2v_hardt_stage_formula {n k : ℕ} (d : s2v_t11b_Formula n)
    (c : Fin k → s2v_t11b_Formula n) (dim : Fin k → ℕ) (r : ℕ) :
    ∃ s : s2v_t11b_Formula n,
      s.realize = d.realize ∪
        ⋃ i ∈ {i | Disjoint (c i).realize d.realize ∧ dim i < r}, (c i).realize := by
  classical
  let e : s2v_t11b_Formula n := .compl (.nonneg 0)
  let a : Fin k → s2v_t11b_Formula n := fun i =>
    if Disjoint (c i).realize d.realize ∧ dim i < r then c i else e
  obtain ⟨u, hu⟩ := s2v_t11b_finite_union_formula a
  refine ⟨.compl (.inter (.compl d) (.compl u)), ?_⟩
  ext x
  change (¬ (x ∉ d.realize ∧ x ∉ u.realize)) ↔ _
  rw [not_and_or, not_not, not_not, hu]
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : Disjoint (c i).realize d.realize ∧ dim i < r
    · exact ⟨i, h, by simpa only [a, if_pos h] using hi⟩
    · simp [a, h, e, s2v_t11b_Formula.realize] at hi
  · rintro ⟨i, h, hi⟩
    exact ⟨i, by simpa only [a, if_pos h] using hi⟩

/-- The stage indexing starts at the designated subset and reaches the carrier.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.5, finite stage consequence;
Bochnak–Coste–Roy, Real Algebraic Geometry, Chapter 9, stratification. -/
theorem s2v_hardt_stage_endpoints {X : Type*} {n k : ℕ}
    (A D : Set X) (c : Fin k → Set X) (dim : Fin k → ℕ)
    (hDA : D ⊆ A) (hc : (⋃ i, c i) = A)
    (hcompat : ∀ i, c i ⊆ D ∨ Disjoint (c i) D)
    (hdim : ∀ i, dim i ≤ n) :
    (D ∪ ⋃ i ∈ {i | Disjoint (c i) D ∧ dim i < 0}, c i) = D ∧
    (D ∪ ⋃ i ∈ {i | Disjoint (c i) D ∧ dim i < n + 1}, c i) = A := by
  constructor
  · simp
  · apply Set.Subset.antisymm
    · rintro x (hx | hx)
      · exact hDA hx
      · obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp hx
        rw [← hc]
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro x hx
      rw [← hc] at hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rcases hcompat i with h | h
      · exact Or.inl (h hi)
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, ⟨h, Nat.lt_succ_of_le (hdim i)⟩, hi⟩)

/-- Boolean compact stages assembled from a supplied finite frontier partition.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.5, dimension-stage consequence;
Bochnak–Coste–Roy, Real Algebraic Geometry, Chapter 9, stratification. -/
theorem s2v_hardt_stages_of_partition {n k : ℕ}
    (f d : s2v_t11b_Formula n) (c : Fin k → s2v_t11b_Formula n)
    (dim : Fin k → ℕ) (hf : IsCompact f.realize) (hd : IsCompact d.realize)
    (hdf : d.realize ⊆ f.realize) (hdim : ∀ i, dim i ≤ n)
    (hc : (⋃ i, (c i).realize) = f.realize)
    (hcompat : ∀ i, (c i).realize ⊆ d.realize ∨ Disjoint (c i).realize d.realize)
    (hfront : ∀ i j, ((c j).realize ∩ closure (c i).realize).Nonempty →
      (c j).realize ⊆ closure (c i).realize ∧ (j = i ∨ dim j < dim i)) :
    ∃ stage : Fin (n + 2) → s2v_t11b_Formula n,
      (∀ r, (stage r).realize = d.realize ∪
        ⋃ i ∈ {i | Disjoint (c i).realize d.realize ∧ dim i < r.val}, (c i).realize) ∧
      (∀ r, IsCompact (stage r).realize) ∧
      (stage 0).realize = d.realize ∧
      (stage (Fin.last (n + 1))).realize = f.realize := by
  choose stage hs using fun r : Fin (n + 2) => s2v_hardt_stage_formula d c dim r.val
  refine ⟨stage, hs, ?_, ?_, ?_⟩
  · intro r
    rw [hs r]
    exact s2v_hardt_stage_compact f.realize d.realize (fun i => (c i).realize)
      dim hf hd hdf hc hcompat hfront r.val
  · rw [hs 0]
    exact (s2v_hardt_stage_endpoints f.realize d.realize (fun i => (c i).realize)
      dim hdf hc hcompat hdim).1
  · rw [hs (Fin.last (n + 1))]
    exact (s2v_hardt_stage_endpoints f.realize d.realize (fun i => (c i).realize)
      dim hdf hc hcompat hdim).2

end HodgeLean.Foundations.Program
