import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismSubface
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbComplexAssembly

/-! Cross-face intersection from a shared geometric boundary complex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_intersection_of_boundary_complex {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (s t : Finset (E × ℝ)) (A B C V : Set E)
    (L : Geometry.SimplicialComplex ℝ (E × ℝ))
    (hsA : convexHull ℝ (↑s : Set (E × ℝ)) ⊆ Prod.fst ⁻¹' A)
    (htB : convexHull ℝ (↑t : Set (E × ℝ)) ⊆ Prod.fst ⁻¹' B)
    (hAB : A ∩ B ⊆ C)
    (hsC : convexHull ℝ (↑s : Set (E × ℝ)) ∩ Prod.fst ⁻¹' C =
      convexHull ℝ ((↑s : Set (E × ℝ)) ∩ Prod.fst ⁻¹' V))
    (htC : convexHull ℝ (↑t : Set (E × ℝ)) ∩ Prod.fst ⁻¹' C =
      convexHull ℝ ((↑t : Set (E × ℝ)) ∩ Prod.fst ⁻¹' V))
    (hsL : ∀ r : Finset (E × ℝ),
      (↑r : Set (E × ℝ)) = (↑s : Set (E × ℝ)) ∩ Prod.fst ⁻¹' V →
      r.Nonempty → r ∈ L.faces)
    (htL : ∀ r : Finset (E × ℝ),
      (↑r : Set (E × ℝ)) = (↑t : Set (E × ℝ)) ∩ Prod.fst ⁻¹' V →
      r.Nonempty → r ∈ L.faces) :
    convexHull ℝ (↑s : Set (E × ℝ)) ∩ convexHull ℝ (↑t : Set (E × ℝ)) ⊆
      convexHull ℝ ((↑s : Set (E × ℝ)) ∩ ↑t) := by
  classical
  rintro p ⟨hps, hpt⟩
  have hpC : p ∈ Prod.fst ⁻¹' C := hAB ⟨hsA hps, htB hpt⟩
  let r := s.filter (fun q => q.1 ∈ V)
  let q := t.filter (fun q => q.1 ∈ V)
  have hr : (↑r : Set (E × ℝ)) = (↑s : Set (E × ℝ)) ∩ Prod.fst ⁻¹' V := by
    ext x
    simp only [r, Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff,
      Set.mem_preimage]
  have hq : (↑q : Set (E × ℝ)) = (↑t : Set (E × ℝ)) ∩ Prod.fst ⁻¹' V := by
    ext x
    simp only [q, Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff,
      Set.mem_preimage]
  have hpr : p ∈ convexHull ℝ (↑r : Set (E × ℝ)) := by
    rw [hr, ← hsC]
    exact ⟨hps, hpC⟩
  have hpq : p ∈ convexHull ℝ (↑q : Set (E × ℝ)) := by
    rw [hq, ← htC]
    exact ⟨hpt, hpC⟩
  have hrne : r.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨p, hpr⟩)
  have hqne : q.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨p, hpq⟩)
  have hp := L.inter_subset_convexHull (hsL r hr hrne) (htL q hq hqne) ⟨hpr, hpq⟩
  apply convexHull_mono ?_ hp
  rintro x ⟨hx, hy⟩
  exact ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hy).1⟩

end HodgeLean.Foundations.Program
