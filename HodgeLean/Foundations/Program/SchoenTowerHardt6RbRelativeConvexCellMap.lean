import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCellBoundaryGraphRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConvexModelExtensionGraph

/-! A convex cell model extends the already assigned boundary map with an actual Boolean graph. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_relative_convex_cell_map {n m : ℕ}
    (A C : Set (EuclideanSpace ℝ (Fin n))) (B T S : Set (EuclideanSpace ℝ (Fin m)))
    (hC : IsCompact C) (hc : Convex ℝ C) (hneC : C.Nonempty)
    (hCA : C \ intrinsicInterior ℝ C ⊆ A) (hSB : S ⊆ B) (hST : S ⊆ T)
    (e : A ≃ₜ B) (hmem : ∀ x : A, x.val ∈ C \ intrinsicInterior ℝ C ↔ (e x).val ∈ S)
    (model : C ≃ₜ T)
    (hmodel : ∀ x : C, x.val ∉ intrinsicInterior ℝ C ↔ (model x).val ∈ S)
    (F : s2v_t11b_Formula n) (hF : F.realize = C \ intrinsicInterior ℝ C)
    (G J : s2v_t11b_Formula (n + m))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (e x).val i))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ x : C,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (model x).val i)) :
    ∃ k : C ≃ₜ T, ∃ R : s2v_t11b_Formula (n + m),
      (∀ x : ↥(C \ intrinsicInterior ℝ C),
        (k ⟨x.val, x.property.1⟩).val = (e ⟨x.val, hCA x.property⟩).val) ∧
      (∀ x : C, (k x).val ∉ S ↔ x.val ∈ intrinsicInterior ℝ C) ∧
      (∀ z, z ∈ R.realize ↔ ∃ x : C,
        (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (k x).val i)) := by
  classical
  by_cases hne : (C \ intrinsicInterior ℝ C).Nonempty
  · obtain ⟨h, Q, hh, hQ⟩ := s2v_hardt6rb_cell_boundary_graph_restriction
      A (C \ intrinsicInterior ℝ C) B S hCA hSB e hmem F hF G hG
    obtain ⟨a, ha⟩ := hneC.intrinsicInterior hc
    obtain ⟨k, R, hk, hki, hR⟩ := s2v_hardt6rb_convex_model_extension_graph C C T S hST
      hC hC hc hc a a ha ha model hmodel h hne Q J hQ hJ
    exact ⟨k, R, fun x => (hk x).trans (hh x), hki, hR⟩
  · refine ⟨model, J, ?_, ?_, hJ⟩
    · intro x
      exact False.elim (hne ⟨x.val, x.property⟩)
    · intro x
      simpa only [not_not] using (hmodel x).not.symm

end HodgeLean.Foundations.Program
