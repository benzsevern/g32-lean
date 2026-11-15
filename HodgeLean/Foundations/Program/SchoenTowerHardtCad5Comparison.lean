import HodgeLean.Foundations.Program.SchoenTowerHardtCad5BoxBounds
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Relations
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Bounds

/-! Comparing arbitrary chart partitions through actual Boolean graph injections. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_dimension_le_of_graph_injective {n q : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {T : Set (EuclideanSpace ℝ (Fin q))}
    (P : s2v_hardt_cad5_Partition S) (R : s2v_hardt_cad5_Partition T)
    (f : S → T) (hf : Function.Injective f) (G : s2v_t11b_Formula (n + q))
    (hG : ∀ (x : S) (y : EuclideanSpace ℝ (Fin q)),
      WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => y v)) ∈ G.realize ↔
        y = (f x).val) : P.dimension ≤ R.dimension := by
  classical
  have hsub (i : Fin P.count) : (P.cell i).realize ⊆ S := by
    intro x hx
    rw [← P.cover]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  apply s2v_hardt_cad5_max_le P.dim R.dimension
    (s2v_hardt_cad5_max_ge_neg_one R.dim)
  intro i
  have hrel (j : Fin R.count) :
      ∃ H : s2v_t11b_Formula (R.dim j + P.dim i),
      ∀ (y : EuclideanSpace ℝ (Fin (R.dim j))) (z : EuclideanSpace ℝ (Fin (P.dim i))),
        WithLp.toLp 2 (Fin.append (fun v => y v) (fun v => z v)) ∈ H.realize ↔
          ∃ a : EuclideanSpace ℝ (Fin n), ∃ b : EuclideanSpace ℝ (Fin q),
            WithLp.toLp 2 (Fin.append (fun v => y v) (fun v => b v)) ∈ (R.inverse j).realize ∧
            a ∈ (P.cell i).realize ∧
            WithLp.toLp 2 (Fin.append (fun v => a v) (fun v => b v)) ∈ G.realize ∧
            WithLp.toLp 2 (Fin.append (fun v => a v) (fun v => z v)) ∈ (P.forward i).realize := by
    obtain ⟨J, hJ⟩ := s2v_hardt_cad5_relation_restricted_reverse (P.cell i) G
    obtain ⟨A, hA⟩ := s2v_hardt_cad5_relation_compose (R.inverse j) J
    obtain ⟨H, hH⟩ := s2v_hardt_cad5_relation_compose A (P.forward i)
    refine ⟨H, ?_⟩
    intro y z
    rw [hH]
    constructor
    · rintro ⟨a, ha, haz⟩
      obtain ⟨b, hb, hba⟩ := (hA y a).mp ha
      obtain ⟨hai, hab⟩ := (hJ a b).mp hba
      exact ⟨a, b, hb, hai, hab, haz⟩
    · rintro ⟨a, b, hb, hai, hab, haz⟩
      exact ⟨a, (hA y a).mpr ⟨b, hb, (hJ a b).mpr ⟨hai, hab⟩⟩, haz⟩
  choose H hH using hrel
  obtain ⟨j, hj⟩ := s2v_hardt_cad5_box_finite_relations_bound R.dim
    (fun j => {y | ∀ v, -1 < y v ∧ y v < 1}) H (by
      intro j y hy
      apply Set.Subsingleton.finite
      intro z hz z' hz'
      obtain ⟨a, b, hb, hai, hab, haz⟩ := (hH j y z).mp hz
      obtain ⟨a', b', hb', hai', hab', haz'⟩ := (hH j y z').mp hz'
      have hbb : b = b' := ((R.inverse_eq j ⟨y, hy⟩ b).mp hb).trans
        ((R.inverse_eq j ⟨y, hy⟩ b').mp hb').symm
      have hfa := (hG ⟨a, hsub i hai⟩ b).mp hab
      have hfa' := (hG ⟨a', hsub i hai'⟩ b').mp hab'
      have haa : a = a' := congrArg Subtype.val (hf (Subtype.ext
        (hfa.symm.trans (hbb.trans hfa'))))
      subst a'
      exact ((P.forward_eq i ⟨a, hai⟩ z).mp haz).trans
        ((P.forward_eq i ⟨a, hai'⟩ z').mp haz').symm) (by
      intro z hz
      let a := (P.chart i).symm ⟨z, hz⟩
      let sx : S := ⟨a.val, hsub i a.property⟩
      have hbT : (f sx).val ∈ ⋃ j, (R.cell j).realize := by
        simpa only [R.cover] using (f sx).property
      obtain ⟨j, hb⟩ := Set.mem_iUnion.mp hbT
      let y := R.chart j ⟨(f sx).val, hb⟩
      refine ⟨j, y.val, y.property, (hH j y.val z).mpr
        ⟨a.val, (f sx).val, ?_, a.property, (hG sx _).mpr rfl, ?_⟩⟩
      · apply (R.inverse_eq j y _).mpr
        exact (congrArg Subtype.val ((R.chart j).symm_apply_apply ⟨(f sx).val, hb⟩)).symm
      · apply (P.forward_eq i a z).mpr
        exact (congrArg Subtype.val ((P.chart i).apply_symm_apply ⟨z, hz⟩)).symm)
  exact le_trans (by exact_mod_cast hj) (s2v_hardt_cad5_le_max R.dim j)

end HodgeLean.Foundations.Program
