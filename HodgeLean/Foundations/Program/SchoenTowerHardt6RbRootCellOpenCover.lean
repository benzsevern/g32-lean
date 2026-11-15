import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCellBoundarySystem
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRankedOpenCellCover
import Mathlib.Data.Fintype.Sigma

/-! Actual graph and adjacent band open cells cover every closed coherent root carrier. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_root_cell_open_cover {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) (hL : L.faces.Finite) (r : L.faces → ℕ)
    (f : (s : L.faces) → Fin (r s) → E → ℝ)
    (hm : ∀ s x, x ∈ convexHull ℝ (s.val : Set E) → Monotone (fun i => f s i x))
    (hs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) → StrictMono (fun i => f s i x))
    (ρ : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρ : ∀ s t hts i x, x ∈ convexHull ℝ (t.val : Set E) → f s i x = f t (ρ s t hts i) x)
    (C O : (s : L.faces) → s2v_hardt6rb_RootLabel (r s) → Set (E × ℝ))
    (hC : ∀ s a, C s a = {p | p.1 ∈ convexHull ℝ (s.val : Set E) ∧
      f s (s2v_hardt6rb_rootLabelLower a) p.1 ≤ p.2 ∧ p.2 ≤ f s (s2v_hardt6rb_rootLabelUpper a) p.1})
    (hO : ∀ s a, O s a = {p | p.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) ∧
      match a with | .inl i => p.2 = f s i p.1 | .inr q => f s q.val.1 p.1 < p.2 ∧ p.2 < f s q.val.2 p.1}) :
    (⋃ i : (s : L.faces) × s2v_hardt6rb_RootLabel (r s), C i.1 i.2) =
      ⋃ i : (s : L.faces) × s2v_hardt6rb_RootLabel (r s), O i.1 i.2 := by
  classical
  let I := (s : L.faces) × s2v_hardt6rb_RootLabel (r s)
  letI : Fintype L.faces := hL.fintype
  letI (s : L.faces) : Fintype (s2v_hardt6rb_RootLabel (r s)) := Fintype.ofFinite _
  letI : Fintype I := inferInstance
  let rank : I → ℕ := fun i => 2 * i.1.val.card + s2v_hardt6rb_rootLabelStep i.2
  let D : I → Finset I := fun i => Finset.univ.filter (fun j => rank j < rank i ∧ C j.1 j.2 ⊆ C i.1 i.2)
  have hD (i j : I) : j ∈ D i ↔ rank j < rank i ∧ C j.1 j.2 ⊆ C i.1 i.2 := by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbd := (s2v_hardt6rb_root_cell_boundary_system L r f hm hs ρ hρ C O hC hO D hD).1
  apply s2v_hardt6rb_ranked_open_cell_cover (fun i : I => C i.1 i.2) (fun i : I => O i.1 i.2) D rank
    (fun i j hj => ((hD i j).mp hj).1) ?_ hbd
  rintro ⟨s, a⟩ p hp
  rw [hO] at hp
  rw [hC]
  refine ⟨intrinsicInterior_subset hp.1, ?_⟩
  cases a with
  | inl a => exact ⟨hp.2.ge, hp.2.le⟩
  | inr q => exact ⟨hp.2.1.le, hp.2.2.le⟩

end HodgeLean.Foundations.Program
