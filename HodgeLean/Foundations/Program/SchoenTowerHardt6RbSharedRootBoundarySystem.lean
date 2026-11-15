import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellBoundarySystem
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellCarrierInclusion

/-! Shared root restrictions give identical finite boundary systems for both actual carrier families. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_shared_root_boundary_system {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) (r : L.faces → ℕ)
    (f g : (s : L.faces) → Fin (r s) → E → ℝ)
    (hm : ∀ s x, x ∈ convexHull ℝ (s.val : Set E) → Monotone (fun i => f s i x))
    (hs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) → StrictMono (fun i => f s i x))
    (hgm : ∀ s x, x ∈ convexHull ℝ (s.val : Set E) → Monotone (fun i => g s i x))
    (hgs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) → StrictMono (fun i => g s i x))
    (ρ : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρ : ∀ s t hts i x, x ∈ convexHull ℝ (t.val : Set E) → f s i x = f t (ρ s t hts i) x)
    (hρg : ∀ s t hts i x, x ∈ convexHull ℝ (t.val : Set E) → g s i x = g t (ρ s t hts i) x)
    (C O T P : (s : L.faces) → s2v_hardt6rb_RootLabel (r s) → Set (E × ℝ))
    (hC : ∀ s a, C s a = {p | p.1 ∈ convexHull ℝ (s.val : Set E) ∧
      f s (s2v_hardt6rb_rootLabelLower a) p.1 ≤ p.2 ∧ p.2 ≤ f s (s2v_hardt6rb_rootLabelUpper a) p.1})
    (hO : ∀ s a, O s a = {p | p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) ∧
      match a with | .inl i => p.2 = f s i p.1 | .inr q => f s q.val.1 p.1 < p.2 ∧ p.2 < f s q.val.2 p.1})
    (hT : ∀ s a, T s a = {p | p.1 ∈ convexHull ℝ (s.val : Set E) ∧
      g s (s2v_hardt6rb_rootLabelLower a) p.1 ≤ p.2 ∧ p.2 ≤ g s (s2v_hardt6rb_rootLabelUpper a) p.1})
    (hP : ∀ s a, P s a = {p | p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) ∧
      match a with | .inl i => p.2 = g s i p.1 | .inr q => g s q.val.1 p.1 < p.2 ∧ p.2 < g s q.val.2 p.1})
    (D : ((s : L.faces) × s2v_hardt6rb_RootLabel (r s)) →
      Finset ((s : L.faces) × s2v_hardt6rb_RootLabel (r s)))
    (hD : ∀ i j, j ∈ D i ↔
      2 * j.1.val.card + s2v_hardt6rb_rootLabelStep j.2 < 2 * i.1.val.card + s2v_hardt6rb_rootLabelStep i.2 ∧
      C j.1 j.2 ⊆ C i.1 i.2) :
    (∀ i, C i.1 i.2 \ O i.1 i.2 = ⋃ j : D i, C j.val.1 j.val.2) ∧
    (∀ i, T i.1 i.2 \ P i.1 i.2 = ⋃ j : D i, T j.val.1 j.val.2) ∧
    (∀ i j : (s : L.faces) × s2v_hardt6rb_RootLabel (r s), j ≠ i →
      2 * j.1.val.card + s2v_hardt6rb_rootLabelStep j.2 ≤ 2 * i.1.val.card + s2v_hardt6rb_rootLabelStep i.2 →
      T j.1 j.2 ∩ T i.1 i.2 ⊆ T i.1 i.2 \ P i.1 i.2) := by
  have hinc (i j : (s : L.faces) × s2v_hardt6rb_RootLabel (r s)) :
      C j.1 j.2 ⊆ C i.1 i.2 ↔ T j.1 j.2 ⊆ T i.1 i.2 := by
    rw [hC, hC, hT, hT]
    exact (s2v_hardt6rb_root_cell_carrier_inclusion L r f hm hs ρ hρ i.1 j.1 i.2 j.2).trans
      (s2v_hardt6rb_root_cell_carrier_inclusion L r g hgm hgs ρ hρg i.1 j.1 i.2 j.2).symm
  have hDT : ∀ i j, j ∈ D i ↔
      2 * j.1.val.card + s2v_hardt6rb_rootLabelStep j.2 < 2 * i.1.val.card + s2v_hardt6rb_rootLabelStep i.2 ∧
      T j.1 j.2 ⊆ T i.1 i.2 := fun i j => (hD i j).trans (and_congr_right fun _ => hinc i j)
  exact ⟨(s2v_hardt6rb_root_cell_boundary_system L r f hm hs ρ hρ C O hC hO D hD).1,
    s2v_hardt6rb_root_cell_boundary_system L r g hgm hgs ρ hρg T P hT hP D hDT⟩

end HodgeLean.Foundations.Program
