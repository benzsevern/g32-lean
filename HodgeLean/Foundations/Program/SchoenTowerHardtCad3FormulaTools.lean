import HodgeLean.Foundations.Program.SchoenTowerHardt2Coordinates

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad3_finite_inter {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → s2v_t11b_Formula n) :
    ∃ F : s2v_t11b_Formula n, ∀ y, y ∈ F.realize ↔ ∀ i, y ∈ (f i).realize := by
  classical
  refine ⟨.conjunction (Finset.univ.toList.map f), ?_⟩
  intro y
  rw [s2v_t11b_realize_conjunction]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]

theorem s2v_hardt_cad3_graph_substitution {n N : ℕ}
    (C : s2v_t11b_Formula n) (s : C.realize → ℝ)
    (g : s2v_t11b_Formula (n + 1))
    (hg : ∀ y, y ∈ g.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = s a)
    (idx : Fin n → Fin N) (f : s2v_t11b_Formula (N + 1)) :
    ∃ F : s2v_t11b_Formula N, ∀ y, y ∈ F.realize ↔
      ∃ a : C.realize, (∀ v, y (idx v) = a.val v) ∧
        WithLp.toLp 2 (Fin.cons (s a) (fun v => y v)) ∈ f.realize := by
  let ρ : Fin (n + 1) → Fin (N + 1) := Fin.cases 0 (fun v => (idx v).succ)
  obtain ⟨F, hF⟩ := s2v_hardt2_project_coordinate
    (.inter (s2v_hardt1_rename ρ g) f)
  refine ⟨F, ?_⟩
  intro y
  rw [hF]
  constructor
  · rintro ⟨t, hgraph, hf⟩
    rw [s2v_hardt1_realize_rename, hg] at hgraph
    obtain ⟨a, ha, ht⟩ := hgraph
    have hta : t = s a := ht
    exact ⟨a, ha, hta ▸ hf⟩
  · rintro ⟨a, ha, hf⟩
    refine ⟨s a, ?_, hf⟩
    rw [s2v_hardt1_realize_rename, hg]
    exact ⟨a, ha, rfl⟩

theorem s2v_hardt_cad3_inverse_graph {n d : ℕ}
    (b : s2v_t11b_Formula n) (B : Set (EuclideanSpace ℝ (Fin d)))
    (E : b.realize ≃ₜ B) (F₀ : s2v_t11b_Formula (n + d))
    (hF₀ : ∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F₀.realize ↔
        z = (E y).val) :
    ∃ F : s2v_t11b_Formula (n + d), ∃ I : s2v_t11b_Formula (d + n),
      (∀ y : b.realize, ∀ z : EuclideanSpace ℝ (Fin d),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : B, ∀ y : EuclideanSpace ℝ (Fin n),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) := by
  let F : s2v_t11b_Formula (n + d) :=
    .inter (s2v_hardt1_rename (Fin.castAdd d) b) F₀
  let ρ : Fin (n + d) → Fin (d + n) :=
    Fin.addCases (Fin.natAdd d) (Fin.castAdd n)
  refine ⟨F, s2v_hardt1_rename ρ F, ?_, ?_⟩
  · intro y z
    change (_ ∧ _) ↔ _
    rw [s2v_hardt1_realize_rename]
    have he : WithLp.toLp 2 (fun i =>
        Fin.append (fun v => y.val v) (fun v => z v) (Fin.castAdd d i)) = y.val := by
      ext i
      simp
    rw [he]
    exact (and_iff_right y.property).trans (hF₀ y z)
  · intro z y
    rw [s2v_hardt1_realize_rename]
    have he : WithLp.toLp 2 (fun i =>
        Fin.append (fun v => z.val v) (fun v => y v) (ρ i)) =
        WithLp.toLp 2 (Fin.append (fun v => y v) (fun v => z.val v)) := by
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [ρ]
    rw [he]
    change (_ ∧ _) ↔ _
    rw [s2v_hardt1_realize_rename]
    have he' : WithLp.toLp 2 (fun i =>
        Fin.append (fun v => y v) (fun v => z.val v) (Fin.castAdd d i)) = y := by
      ext i
      simp
    rw [he']
    constructor
    · rintro ⟨hy, h⟩
      have hz := (hF₀ ⟨y, hy⟩ z.val).mp h
      have hsub : z = E ⟨y, hy⟩ := Subtype.ext hz
      exact congrArg Subtype.val (((congrArg E.symm hsub).trans (E.symm_apply_apply _)).symm)
    · intro hy
      subst y
      refine ⟨(E.symm z).property, ?_⟩
      exact (hF₀ (E.symm z) z.val).mpr (congrArg Subtype.val (E.apply_symm_apply z)).symm

theorem s2v_hardt_cad3_boolean_refinement {n m : ℕ}
    (C : s2v_t11b_Formula n) (A : Fin m → s2v_t11b_Formula n) :
    ∃ l : ℕ, ∃ c : Fin l → s2v_t11b_Formula n,
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = C.realize ∧
      ∀ i j, (∀ x ∈ (c i).realize, x ∈ (A j).realize) ∨
        (∀ x ∈ (c i).realize, x ∉ (A j).realize) := by
  classical
  let R : (Fin m → Bool) → s2v_t11b_Formula n :=
    fun s => .inter C (s2v_t11b_refinementFormula A s)
  let J := {s : Fin m → Bool // (R s).realize.Nonempty}
  let E := Fintype.equivFin J
  let c : Fin (Fintype.card J) → s2v_t11b_Formula n := fun i => R (E.symm i).val
  refine ⟨Fintype.card J, c, fun i => (E.symm i).property, ?_, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi : x ∈ (s2v_t11b_refinementFormula A (E.symm i).val).realize := hxi.2
    have hj : x ∈ (s2v_t11b_refinementFormula A (E.symm j).val).realize := hxj.2
    obtain ⟨s, hs, hu⟩ := s2v_t11b_refinement_partition A x
    have he : (E.symm i).val = (E.symm j).val := (hu _ hi).trans (hu _ hj).symm
    exact hij (E.symm.injective (Subtype.ext he))
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hi.1
    · intro hx
      obtain ⟨s, hs, _⟩ := s2v_t11b_refinement_partition A x
      let j : J := ⟨s, ⟨x, hx, hs⟩⟩
      refine Set.mem_iUnion.mpr ⟨E j, ?_⟩
      change x ∈ (R (E.symm (E j)).val).realize
      rw [E.symm_apply_apply]
      exact ⟨hx, hs⟩
  · intro i j
    by_cases h : (E.symm i).val j = true
    · left
      intro x hx
      exact ((s2v_t11b_realize_refinementFormula A _ x).mp hx.2 j).mp h
    · right
      intro x hx ha
      exact h (((s2v_t11b_realize_refinementFormula A _ x).mp hx.2 j).mpr ha)

end HodgeLean.Foundations.Program
