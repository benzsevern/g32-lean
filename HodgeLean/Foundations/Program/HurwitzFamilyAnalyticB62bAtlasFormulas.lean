import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bAtlas

noncomputable section

namespace HodgeLean.Foundations.Program

variable (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (G U C : Type) [Group G] [TopologicalSpace U] [MulAction G U]
    [TopologicalSpace C] [Nonempty U] [MulAction G C] [ChartedSpace ℂ C]
    (π : U → b6t_punctured b) (hπ : IsQuotientCoveringMap π G)
    (f : C → OnePoint ℂ) (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
    (hrange : Set.range ι = f ⁻¹' (Set.range (b6_branch b))ᶜ) (n : C → ℕ)
    (hn : ∀ x, 0 < n x)
    (hlocal : ∀ x (j : Fin 13), f x = b6_branch b j →
      ∃ P : OpenPartialHomeomorph C ℂ,
        x ∈ P.source ∧ P ∈ atlas ℂ C ∧ P x = 0 ∧
        (∀ y ∈ P.source, f y = b6a_value b j (P y ^ n x)) ∧
        ∀ g : MulAction.stabilizer G x, ∃ ζ : ℂ, ζ ^ n x = 1 ∧
          Set.MapsTo (fun y : C ↦ (g : G) • y) P.source P.source ∧
          ∀ y ∈ P.source, P ((g : G) • y) = ζ * P y)

local notation "A" => b6a_familyChart b hb G U C π hπ f ι hι hrange n hn hlocal

theorem b6a_familyChart_free (hproj : ∀ u, f (ι u) = π u)
    (q : b6t_polydisc b × C) (hq : f q.2 ∉ Set.range (b6_branch b))
    (y : b6t_polydisc b × C) (hy : y ∈ (A q).source) :
    b6a_map b f y = ((A q y).2 : OnePoint ℂ) := by
  classical
  have hx : ¬ b6a_IsMarked b f q.2 := by
    rintro ⟨j, hj⟩
    exact hq ⟨j, hj.symm⟩
  rw [b6a_familyChart, dif_neg hx] at hy ⊢
  exact b6a_totalUnramifiedChart_map b hb G U C π hπ ι hι f hproj _ y hy

theorem b6a_familyChart_mark_zero (q : b6t_polydisc b × C)
    (hq : b6a_IsMarked b f q.2) : (A q q).2 = 0 := by
  classical
  rw [b6a_familyChart, dif_pos hq]
  dsimp only
  split
  · exact b6a_totalMovingMarkChart_self b hb C _ _ _ _ _ q.2
      (b6a_restrictedMarkChart_self b G C f n hlocal q.2 hq)
  · simpa [b6a_productChart, b6a_fixedMarkChart] using
      b6a_restrictedMarkChart_self b G C f n hlocal q.2 hq

theorem b6a_familyChart_mark_power (q : b6t_polydisc b × C)
    (hq : b6a_IsMarked b f q.2) (y : b6t_polydisc b × C)
    (hy : y ∈ (A q).source) :
    b6a_map b f y = b6a_value y.1.val (b6a_markIndex b f q.2 hq)
      ((A q y).2 ^ n q.2) := by
  classical
  let j := b6a_markIndex b f q.2 hq
  let P := b6a_restrictedMarkChart b G C f n hlocal q.2 hq
  have hPf : ∀ x ∈ P.source, f x = b6a_value b j (P x ^ n q.2) := by
    intro x hx
    exact (b6a_markChart_spec b G C f n hlocal q.2 hq).2.2.2.1 x hx.1
  have hPr : ∀ x ∈ P.source, ‖P x‖ ^ n q.2 < b6t_radius b := by
    intro x hx
    exact hx.2
  rw [b6a_familyChart, dif_pos hq] at hy ⊢
  dsimp only at hy ⊢
  by_cases hj : j.val < 10
  · rw [dif_pos hj] at hy ⊢
    have h := b6a_totalMovingMarkChart_power b hb C P f q.1 ⟨j.val, hj⟩
      (n q.2) (hn q.2) (by simpa [b6a_value, hj] using hPf) hPr y hy
    dsimp only [j, P] at hj h
    simpa only [b6a_value, dif_pos hj] using h
  · rw [dif_neg hj] at hy ⊢
    exact b6a_fixedMarkChart_power b hb j hj (n q.2) P f hPf y.1 y.2 hy.2

theorem b6a_familyChart_mark (q : b6t_polydisc b × C) (j : Fin 13)
    (hj : f q.2 = b6_branch b j) :
    (A q q).2 = 0 ∧ ∀ y ∈ (A q).source,
      b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2) := by
  have hq : b6a_IsMarked b f q.2 := ⟨j, hj⟩
  have heq : b6a_markIndex b f q.2 hq = j :=
    hb ((b6a_markIndex_eq b f q.2 hq).symm.trans hj)
  refine ⟨b6a_familyChart_mark_zero b hb G U C π hπ f ι hι hrange n hn hlocal q hq, ?_⟩
  intro y hy
  simpa only [heq] using
    b6a_familyChart_mark_power b hb G U C π hπ f ι hι hrange n hn hlocal q hq y hy

noncomputable def b6a_isolatedFamilyChart (hf : Continuous f) (q : b6t_polydisc b × C) :
    OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ) := by
  classical
  exact if hq : b6a_IsMarked b f q.2 then
    (A q).restrOpen ((fun y : b6t_polydisc b × C ↦ f y.2) ⁻¹'
      b6a_markValueOpen b (b6a_markIndex b f q.2 hq))
      ((b6a_markValueOpen_isOpen b _).preimage (hf.comp continuous_snd))
  else A q

theorem b6a_mem_isolatedFamilyChart_source (hf : Continuous f) (q : b6t_polydisc b × C) :
    q ∈ (b6a_isolatedFamilyChart b hb G U C π hπ f ι hι hrange n hn hlocal hf q).source := by
  classical
  have hA := b6a_mem_familyChart_source b hb G U C π hπ f ι hι hrange n hn hlocal q
  by_cases hq : b6a_IsMarked b f q.2
  · rw [b6a_isolatedFamilyChart, dif_pos hq]
    refine ⟨hA, ?_⟩
    change f q.2 ∈ b6a_markValueOpen b (b6a_markIndex b f q.2 hq)
    rw [b6a_markIndex_eq b f q.2 hq]
    exact (b6a_branch_mem_markValueOpen b hb _ _).2 rfl
  · simpa [b6a_isolatedFamilyChart, hq] using hA

theorem b6a_isolatedFamilyChart_apply (hf : Continuous f) (q y : b6t_polydisc b × C) :
    b6a_isolatedFamilyChart b hb G U C π hπ f ι hι hrange n hn hlocal hf q y = A q y := by
  classical
  unfold b6a_isolatedFamilyChart
  split <;> rfl

theorem b6a_isolatedFamilyChart_source_subset (hf : Continuous f) (q : b6t_polydisc b × C) :
    (b6a_isolatedFamilyChart b hb G U C π hπ f ι hι hrange n hn hlocal hf q).source ⊆
      (A q).source := by
  classical
  unfold b6a_isolatedFamilyChart
  split
  · exact Set.inter_subset_left
  · exact Set.Subset.rfl

theorem b6a_familyChart_eq_of_snd_eq (q q' y : b6t_polydisc b × C)
    (hqq' : q.2 = q'.2) (hy : y ∈ (A q).source) (hy' : y ∈ (A q').source) :
    A q y = A q' y := by
  classical
  rcases q with ⟨t, x⟩
  rcases q' with ⟨t', x'⟩
  dsimp only at hqq'
  subst x'
  by_cases hx : b6a_IsMarked b f x
  · simp only [b6a_familyChart, dif_pos hx] at hy hy' ⊢
    by_cases hj : (b6a_markIndex b f x hx).val < 10
    · simp only [dif_pos hj] at hy hy' ⊢
      rw [b6a_totalMovingMarkChart_apply_of_mem b hb C _ _ _ _ _ y hy,
        b6a_totalMovingMarkChart_apply_of_mem b hb C _ _ _ _ _ y hy']
    · simp only [dif_neg hj]
  · simp [b6a_familyChart, hx]

theorem b6a_familyChart_mark_fibre_eq (q y : b6t_polydisc b × C)
    (hq : b6a_IsMarked b f q.2) (hy : y ∈ (A q).source)
    (hfy : f y.2 = f q.2) : y.2 = q.2 := by
  classical
  let j := b6a_markIndex b f q.2 hq
  let P := b6a_restrictedMarkChart b G C f n hlocal q.2 hq
  have hyP : y.2 ∈ P.source := by
    rw [b6a_familyChart, dif_pos hq] at hy
    dsimp only at hy
    by_cases hj : j.val < 10
    · rw [dif_pos hj, b6a_totalMovingMarkChart_source] at hy
      exact hy.2
    · rw [dif_neg hj] at hy
      exact hy.2.1
  have hPy : f y.2 = b6a_value b j (P y.2 ^ n q.2) :=
    (b6a_markChart_spec b G C f n hlocal q.2 hq).2.2.2.1 y.2 hyP.1
  have hpow : P y.2 ^ n q.2 = 0 := by
    apply b6a_value_injective b j
    rw [← hPy, hfy, b6a_value_zero]
    exact b6a_markIndex_eq b f q.2 hq
  have hzero : P y.2 = 0 := (pow_eq_zero_iff (hn q.2).ne').1 hpow
  apply P.injOn hyP (b6a_mem_restrictedMarkChart_source b hb G C f n hlocal hn q.2 hq)
  exact hzero.trans (b6a_restrictedMarkChart_self b G C f n hlocal q.2 hq).symm

theorem b6a_isolatedFamilyChart_marked_point (hf : Continuous f)
    (q y : b6t_polydisc b × C)
    (hy : y ∈ (b6a_isolatedFamilyChart b hb G U C π hπ f ι hι hrange n hn hlocal hf q).source)
    (hym : b6a_IsMarked b f y.2) : y.2 = q.2 := by
  classical
  obtain ⟨j, hj⟩ := hym
  by_cases hq : b6a_IsMarked b f q.2
  · have hyA := b6a_isolatedFamilyChart_source_subset b hb G U C π hπ f ι hι
      hrange n hn hlocal hf q hy
    rw [b6a_isolatedFamilyChart, dif_pos hq] at hy
    have hval : f y.2 ∈ b6a_markValueOpen b (b6a_markIndex b f q.2 hq) := hy.2
    rw [hj] at hval
    have heq := (b6a_branch_mem_markValueOpen b hb _ j).1 hval
    apply b6a_familyChart_mark_fibre_eq b hb G U C π hπ f ι hι hrange n hn hlocal q y hq hyA
    rw [hj, heq]
    exact (b6a_markIndex_eq b f q.2 hq).symm
  · rw [b6a_isolatedFamilyChart, dif_neg hq, b6a_familyChart, dif_neg hq] at hy
    have hyι : y.2 ∈ Set.range ι := by
      have h := hy.1.1.2.1.1
      change y.2 ∈ (b6a_openEmbeddingInverse U C ι hι).source at h
      simpa only [b6a_openEmbeddingInverse_source] using h
    rw [hrange] at hyι
    exact False.elim (hyι ⟨j, hj.symm⟩)

local notation "B" => b6a_isolatedFamilyChart b hb G U C π hπ f ι hι hrange n hn hlocal

theorem b6a_isolatedFamilyChart_formulas (hf : Continuous f) (hproj : ∀ u, f (ι u) = π u) :
    (∀ q y, y ∈ (B hf q).source → (B hf q y).1 = y.1.val) ∧
    (∀ q, f q.2 ∉ Set.range (b6_branch b) → ∀ y ∈ (B hf q).source,
      b6a_map b f y = ((B hf q y).2 : OnePoint ℂ)) ∧
    (∀ q (j : Fin 13), f q.2 = b6_branch b j →
      (B hf q q).2 = 0 ∧ ∀ y ∈ (B hf q).source,
        b6a_map b f y = b6a_value y.1.val j ((B hf q y).2 ^ n q.2)) := by
  constructor
  · intro q y hy
    rw [b6a_isolatedFamilyChart_apply]
    exact b6a_familyChart_fst b hb G U C π hπ f ι hι hrange n hn hlocal q y
      (b6a_isolatedFamilyChart_source_subset b hb G U C π hπ f ι hι hrange n hn hlocal hf q hy)
  constructor
  · intro q hq y hy
    rw [b6a_isolatedFamilyChart_apply]
    exact b6a_familyChart_free b hb G U C π hπ f ι hι hrange n hn hlocal hproj q hq y
      (b6a_isolatedFamilyChart_source_subset b hb G U C π hπ f ι hι hrange n hn hlocal hf q hy)
  · intro q j hj
    constructor
    · rw [b6a_isolatedFamilyChart_apply]
      exact (b6a_familyChart_mark b hb G U C π hπ f ι hι hrange n hn hlocal q j hj).1
    · intro y hy
      rw [b6a_isolatedFamilyChart_apply]
      exact (b6a_familyChart_mark b hb G U C π hπ f ι hι hrange n hn hlocal q j hj).2 y
        (b6a_isolatedFamilyChart_source_subset b hb G U C π hπ f ι hι hrange n hn hlocal hf q hy)

theorem b6a_isolatedFamilyChart_zero_fibre_eq (hf : Continuous f)
    (q y : b6t_polydisc b × C) (hq : b6a_IsMarked b f q.2)
    (hy : y ∈ (B hf q).source) (hzero : (B hf q y).2 = 0) : y.2 = q.2 := by
  have hyA := b6a_isolatedFamilyChart_source_subset b hb G U C π hπ f ι hι
    hrange n hn hlocal hf q hy
  rw [b6a_isolatedFamilyChart_apply] at hzero
  have hm := b6a_familyChart_mark_power b hb G U C π hπ f ι hι hrange n hn hlocal q hq y hyA
  rw [hzero, zero_pow (hn q.2).ne', b6a_value_zero] at hm
  have hbranch : f y.2 = b6_branch b (b6a_markIndex b f q.2 hq) := by
    obtain ⟨e, he⟩ := b6t_homeomorph b hb y.1.val y.1.property
    apply e.injective
    rw [he, he]
    exact hm.trans (b6t_marks b hb y.1.val y.1.property _).symm
  exact b6a_isolatedFamilyChart_marked_point b hb G U C π hπ f ι hι hrange n hn hlocal
    hf q y hy ⟨_, hbranch⟩

end HodgeLean.Foundations.Program
