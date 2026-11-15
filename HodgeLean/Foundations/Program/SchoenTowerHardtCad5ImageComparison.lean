import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Comparison

/-! Dimension bounds for Boolean-graph images without injectivity. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_dimension_le_of_graph_surjective {n q : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {T : Set (EuclideanSpace ℝ (Fin q))}
    (P : s2v_hardt_cad5_Partition S) (R : s2v_hardt_cad5_Partition T)
    (f : S → T) (hf : Function.Surjective f) (G : s2v_t11b_Formula (n + q))
    (hG : ∀ (x : S) (y : EuclideanSpace ℝ (Fin q)),
      WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => y v)) ∈ G.realize ↔
        y = (f x).val) : R.dimension ≤ P.dimension := by
  classical
  have hsub (j : Fin R.count) : (R.cell j).realize ⊆ T := by
    intro x hx
    rw [← R.cover]
    exact Set.mem_iUnion.mpr ⟨j, hx⟩
  apply s2v_hardt_cad5_max_le R.dim P.dimension
    (s2v_hardt_cad5_max_ge_neg_one P.dim)
  intro j
  obtain ⟨Grev, hGrev⟩ := s2v_hardt_cad5_relation_reverse G
  obtain ⟨D, hD⟩ := s2v_hardt_cad5_relation_restricted_reverse (R.cell j) Grev
  have hrel (i : Fin P.count) :
      ∃ H : s2v_t11b_Formula (P.dim i + R.dim j),
      ∀ (y : EuclideanSpace ℝ (Fin (P.dim i))) (z : EuclideanSpace ℝ (Fin (R.dim j))),
        WithLp.toLp 2 (Fin.append (fun v => y v) (fun v => z v)) ∈ H.realize ↔
          ∃ a : EuclideanSpace ℝ (Fin n), ∃ b : EuclideanSpace ℝ (Fin q),
            WithLp.toLp 2 (Fin.append (fun v => y v) (fun v => a v)) ∈ (P.inverse i).realize ∧
            b ∈ (R.cell j).realize ∧
            WithLp.toLp 2 (Fin.append (fun v => a v) (fun v => b v)) ∈ G.realize ∧
            WithLp.toLp 2 (Fin.append (fun v => b v) (fun v => z v)) ∈ (R.forward j).realize := by
    obtain ⟨A, hA⟩ := s2v_hardt_cad5_relation_compose (P.inverse i) D
    obtain ⟨H, hH⟩ := s2v_hardt_cad5_relation_compose A (R.forward j)
    refine ⟨H, ?_⟩
    intro y z
    rw [hH]
    constructor
    · rintro ⟨b, hb, hbz⟩
      obtain ⟨a, ha, hab⟩ := (hA y b).mp hb
      rw [hD b a, hGrev a b] at hab
      exact ⟨a, b, ha, hab.1, hab.2, hbz⟩
    · rintro ⟨a, b, ha, hbj, hab, hbz⟩
      refine ⟨b, (hA y b).mpr ⟨a, ha, ?_⟩, hbz⟩
      rw [hD b a, hGrev a b]
      exact ⟨hbj, hab⟩
  choose H hH using hrel
  obtain ⟨i, hi⟩ := s2v_hardt_cad5_box_finite_relations_bound P.dim
    (fun i => {y | ∀ v, -1 < y v ∧ y v < 1}) H (by
      intro i y hy
      apply Set.Subsingleton.finite
      intro z hz z' hz'
      obtain ⟨a, b, ha, hbj, hab, hbz⟩ := (hH i y z).mp hz
      obtain ⟨a', b', ha', hbj', hab', hbz'⟩ := (hH i y z').mp hz'
      let sx : S := ⟨((P.chart i).symm ⟨y, hy⟩).val, by
        have h : ((P.chart i).symm ⟨y, hy⟩).val ∈ ⋃ l, (P.cell l).realize :=
          Set.mem_iUnion.mpr ⟨i, ((P.chart i).symm ⟨y, hy⟩).property⟩
        simpa only [P.cover] using h⟩
      have haa : a = sx.val := (P.inverse_eq i ⟨y, hy⟩ a).mp ha
      have haa' : a' = sx.val := (P.inverse_eq i ⟨y, hy⟩ a').mp ha'
      subst a
      subst a'
      have hbb : b = b' := ((hG sx b).mp hab).trans ((hG sx b').mp hab').symm
      subst b'
      exact ((R.forward_eq j ⟨b, hbj⟩ z).mp hbz).trans
        ((R.forward_eq j ⟨b, hbj'⟩ z').mp hbz').symm) (by
      intro z hz
      let b := (R.chart j).symm ⟨z, hz⟩
      let tx : T := ⟨b.val, hsub j b.property⟩
      obtain ⟨sx, hsx⟩ := hf tx
      have haS : sx.val ∈ ⋃ i, (P.cell i).realize := by
        simpa only [P.cover] using sx.property
      obtain ⟨i, ha⟩ := Set.mem_iUnion.mp haS
      let y := P.chart i ⟨sx.val, ha⟩
      refine ⟨i, y.val, y.property, (hH i y.val z).mpr
        ⟨sx.val, b.val, ?_, b.property, ?_, ?_⟩⟩
      · apply (P.inverse_eq i y sx.val).mpr
        exact (congrArg Subtype.val ((P.chart i).symm_apply_apply ⟨sx.val, ha⟩)).symm
      · apply (hG sx b.val).mpr
        exact (congrArg Subtype.val hsx).symm
      · apply (R.forward_eq j b z).mpr
        exact (congrArg Subtype.val ((R.chart j).apply_symm_apply ⟨z, hz⟩)).symm)
  exact le_trans (by exact_mod_cast hi) (s2v_hardt_cad5_le_max P.dim i)

end HodgeLean.Foundations.Program
