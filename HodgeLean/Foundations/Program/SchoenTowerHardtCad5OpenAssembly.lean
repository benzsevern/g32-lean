import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Defs

/-! Finite assembly of cylinder partitions retaining full-dimensional openness. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_assemble_open_cylinders {n h : ℕ}
    (Q : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin n))))
    (L : (i : Fin Q.count) → s2v_hardt_cad5_Partition
      {y : EuclideanSpace ℝ (Fin (n + 1)) | ∃ a : (Q.cell i).realize,
        ∀ v, y v.succ = a.val v})
    (B : Fin h → s2v_t11b_Formula (n + 1))
    (ha : ∀ i l j, ((L i).cell l).realize ⊆ (B j).realize ∨
      Disjoint ((L i).cell l).realize (B j).realize)
    (hopen : ∀ i l, (L i).dim l = n + 1 → IsOpen ((L i).cell l).realize) :
    ∃ P : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      (∀ i j, (P.cell i).realize ⊆ (B j).realize ∨ Disjoint (P.cell i).realize (B j).realize) ∧
      (∀ i, P.dim i = n + 1 → IsOpen (P.cell i).realize) := by
  classical
  let T := (i : Fin Q.count) × Fin (L i).count
  let enum := (Fintype.equivFin T).symm
  have hdisj : Pairwise (fun a b : T =>
      Disjoint ((L a.1).cell a.2).realize ((L b.1).cell b.2).realize) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    by_cases hij : i = j
    · subst j
      exact (L i).disjoint (fun h => hab (congrArg (Sigma.mk i) h))
    · apply Set.disjoint_left.mpr
      intro y hyi hyj
      have hi : y ∈ {y : EuclideanSpace ℝ (Fin (n + 1)) |
          ∃ x : (Q.cell i).realize, ∀ v, y v.succ = x.val v} := by
        have hu : y ∈ ⋃ l, ((L i).cell l).realize := Set.mem_iUnion.mpr ⟨a, hyi⟩
        simpa only [(L i).cover] using hu
      have hj : y ∈ {y : EuclideanSpace ℝ (Fin (n + 1)) |
          ∃ x : (Q.cell j).realize, ∀ v, y v.succ = x.val v} := by
        have hu : y ∈ ⋃ l, ((L j).cell l).realize := Set.mem_iUnion.mpr ⟨b, hyj⟩
        simpa only [(L j).cover] using hu
      obtain ⟨x, hx⟩ := hi
      obtain ⟨z, hz⟩ := hj
      have he : x.val = z.val := by
        ext v
        exact (hx v).symm.trans (hz v)
      exact Set.disjoint_left.mp (Q.disjoint hij) x.property (he.symm ▸ z.property)
  have hcover : (⋃ t : Fin (Fintype.card T),
      ((L (enum t).1).cell (enum t).2).realize) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun v => y v.succ)
    have hx : x ∈ ⋃ i, (Q.cell i).realize := by rw [Q.cover]; exact Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hy : y ∈ ⋃ l, ((L i).cell l).realize := by
      rw [(L i).cover]
      exact ⟨⟨x, hi⟩, fun _ => rfl⟩
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨(Fintype.equivFin T) ⟨i, l⟩, ?_⟩
    have hen : enum ((Fintype.equivFin T) ⟨i, l⟩) = ⟨i, l⟩ :=
      (Fintype.equivFin T).symm_apply_apply ⟨i, l⟩
    rw [hen]
    exact hl
  let P : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    { count := Fintype.card T
      cell := fun t => (L (enum t).1).cell (enum t).2
      dim := fun t => (L (enum t).1).dim (enum t).2
      chart := fun t => (L (enum t).1).chart (enum t).2
      forward := fun t => (L (enum t).1).forward (enum t).2
      inverse := fun t => (L (enum t).1).inverse (enum t).2
      nonempty := fun t => (L (enum t).1).nonempty (enum t).2
      disjoint := fun _ _ h => hdisj (fun he => h (enum.injective he))
      cover := hcover
      bound := fun t => (L (enum t).1).bound (enum t).2
      forward_eq := fun t => (L (enum t).1).forward_eq (enum t).2
      inverse_eq := fun t => (L (enum t).1).inverse_eq (enum t).2 }
  exact ⟨P, fun i j => ha (enum i).1 (enum i).2 j,
    fun i => hopen (enum i).1 (enum i).2⟩

end HodgeLean.Foundations.Program
