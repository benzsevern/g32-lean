import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellBoundaryCover
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellRankSeparation

/-! Actual root carrier incidence gives the full ranked boundary system for each parametrized cell family. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_root_cell_boundary_system {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) (r : L.faces → ℕ)
    (f : (s : L.faces) → Fin (r s) → E → ℝ)
    (hm : ∀ s x, x ∈ convexHull ℝ (s.val : Set E) → Monotone (fun i => f s i x))
    (hs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) → StrictMono (fun i => f s i x))
    (ρ : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρ : ∀ s t hts i x, x ∈ convexHull ℝ (t.val : Set E) → f s i x = f t (ρ s t hts i) x)
    (C O : (s : L.faces) → s2v_hardt6rb_RootLabel (r s) → Set (E × ℝ))
    (hC : ∀ s a, C s a = {p | p.1 ∈ convexHull ℝ (s.val : Set E) ∧
      f s (s2v_hardt6rb_rootLabelLower a) p.1 ≤ p.2 ∧ p.2 ≤ f s (s2v_hardt6rb_rootLabelUpper a) p.1})
    (hO : ∀ s a, O s a = {p | p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) ∧
      match a with | .inl i => p.2 = f s i p.1 | .inr q => f s q.val.1 p.1 < p.2 ∧ p.2 < f s q.val.2 p.1})
    (D : ((s : L.faces) × s2v_hardt6rb_RootLabel (r s)) →
      Finset ((s : L.faces) × s2v_hardt6rb_RootLabel (r s)))
    (hD : ∀ i j, j ∈ D i ↔
      2 * j.1.val.card + s2v_hardt6rb_rootLabelStep j.2 < 2 * i.1.val.card + s2v_hardt6rb_rootLabelStep i.2 ∧
      C j.1 j.2 ⊆ C i.1 i.2) :
    (∀ i, C i.1 i.2 \ O i.1 i.2 = ⋃ j : D i, C j.val.1 j.val.2) ∧
    (∀ i j : (s : L.faces) × s2v_hardt6rb_RootLabel (r s), j ≠ i →
      2 * j.1.val.card + s2v_hardt6rb_rootLabelStep j.2 ≤ 2 * i.1.val.card + s2v_hardt6rb_rootLabelStep i.2 →
      C j.1 j.2 ∩ C i.1 i.2 ⊆ C i.1 i.2 \ O i.1 i.2) := by
  have hsep : ∀ i j : (s : L.faces) × s2v_hardt6rb_RootLabel (r s), j ≠ i →
      2 * j.1.val.card + s2v_hardt6rb_rootLabelStep j.2 ≤ 2 * i.1.val.card + s2v_hardt6rb_rootLabelStep i.2 →
      C j.1 j.2 ∩ C i.1 i.2 ⊆ C i.1 i.2 \ O i.1 i.2 := by
    rintro ⟨s, a⟩ ⟨t, b⟩ hne hrank p ⟨hpj, hpi⟩
    refine ⟨hpi, ?_⟩
    intro hpin
    obtain ⟨hx, ho⟩ := (Set.ext_iff.mp (hO s a) p).mp hpin
    have hpjt := (Set.ext_iff.mp (hC t b) p).mp hpj
    exact hne (s2v_hardt6rb_root_cell_rank_separation L r f hs s t a b hrank p hx hpjt.1
      (by cases a <;> exact ho) hpjt.2)
  refine ⟨?_, hsep⟩
  intro i
  ext p
  constructor
  · intro hp
    obtain ⟨t, b, hrank, hpb, hsub⟩ := s2v_hardt6rb_root_cell_boundary_cover L r f hm hs ρ hρ C hC O hO i.1 i.2 p hp
    exact Set.mem_iUnion.mpr ⟨⟨⟨t, b⟩, (hD i ⟨t, b⟩).mpr ⟨hrank, hsub⟩⟩, hpb⟩
  · intro hp
    obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hp
    have hd := (hD i j.val).mp j.property
    have hjne : j.val ≠ i := by
      intro he
      have heq := congrArg (fun k => 2 * k.1.val.card + s2v_hardt6rb_rootLabelStep k.2) he
      exact (ne_of_lt hd.1) heq
    exact hsep i j.val hjne hd.1.le ⟨hpj, hd.2 hpj⟩

end HodgeLean.Foundations.Program
