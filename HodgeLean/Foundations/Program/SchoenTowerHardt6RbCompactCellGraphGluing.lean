import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactCellMapGluing
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5FiniteBooleanFamilies

/-! The assembled compact cell homeomorphism has the actual finite union of its constituent Boolean graphs. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_cell_graph_gluing {n m : ℕ} {ι : Type*} [Finite ι]
    (C : ι → Set (EuclideanSpace ℝ (Fin n))) (D : ι → Set (EuclideanSpace ℝ (Fin m)))
    (hC : ∀ i, IsCompact (C i)) (e : ∀ i, C i ≃ₜ D i)
    (hagree : ∀ i j (x : EuclideanSpace ℝ (Fin n)) (hi : x ∈ C i) (hj : x ∈ C j),
      (e i ⟨x, hi⟩).val = (e j ⟨x, hj⟩).val)
    (hinj : ∀ i j (x : C i) (y : C j), (e i x).val = (e j y).val → x.val = y.val)
    (G : ι → s2v_t11b_Formula (n + m))
    (hG : ∀ i z, z ∈ (G i).realize ↔ ∃ x : C i,
      (∀ j, z (Fin.castAdd m j) = x.val j) ∧
      (∀ j, z (Fin.natAdd n j) = (e i x).val j)) :
    ∃ H : (⋃ i, C i) ≃ₜ (⋃ i, D i), ∃ R : s2v_t11b_Formula (n + m),
      (∀ i (x : C i), (H ⟨x.val, Set.mem_iUnion.mpr ⟨i, x.property⟩⟩).val = (e i x).val) ∧
      (∀ z, z ∈ R.realize ↔ ∃ x : (⋃ i, C i),
        (∀ j, z (Fin.castAdd m j) = x.val j) ∧
        (∀ j, z (Fin.natAdd n j) = (H x).val j)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨H, hH⟩ := s2v_hardt6rb_compact_cell_map_gluing C D hC e hagree hinj
  obtain ⟨R, hR⟩ := s2v_hardt_cad5_finite_union_formula G
  refine ⟨H, R, hH, ?_⟩
  intro z
  rw [hR, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨x, hx, hy⟩ := (hG i z).mp hi
    refine ⟨⟨x.val, Set.mem_iUnion.mpr ⟨i, x.property⟩⟩, hx, ?_⟩
    rw [hH i x]
    exact hy
  · rintro ⟨x, hx, hy⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.property
    refine ⟨i, (hG i z).mpr ⟨⟨x.val, hi⟩, hx, ?_⟩⟩
    rw [← hH i ⟨x.val, hi⟩]
    exact hy

end HodgeLean.Foundations.Program
