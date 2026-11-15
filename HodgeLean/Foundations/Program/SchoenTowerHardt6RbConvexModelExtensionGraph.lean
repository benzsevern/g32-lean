import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBoundaryModelGraph
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRadialHomeomorphGraph
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAmbientRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRadialBoundaryRestriction

/-! Actual Boolean graphs for relative extensions through convex target models. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_convex_model_extension_graph {n m r : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (D : Set (EuclideanSpace ℝ (Fin m)))
    (A B : Set (EuclideanSpace ℝ (Fin r))) (hBA : B ⊆ A)
    (hC : IsCompact C) (hD : IsCompact D) (hc : Convex ℝ C) (hd : Convex ℝ D)
    (a : EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin m)) (ha : a ∈ intrinsicInterior ℝ C) (hb : b ∈ intrinsicInterior ℝ D)
    (e : D ≃ₜ A) (he : ∀ x : D, x.val ∉ intrinsicInterior ℝ D ↔ (e x).val ∈ B)
    (h : ↥(C \ intrinsicInterior ℝ C) ≃ₜ B)
    (hne : (C \ intrinsicInterior ℝ C).Nonempty)
    (G : s2v_t11b_Formula (n + r)) (J : s2v_t11b_Formula (m + r))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : ↥(C \ intrinsicInterior ℝ C),
      (∀ i, z (Fin.castAdd r i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (h x).val i))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ x : D,
      (∀ i, z (Fin.castAdd r i) = x.val i) ∧
      (∀ i, z (Fin.natAdd m i) = (e x).val i)) :
    ∃ H : C ≃ₜ A, ∃ R : s2v_t11b_Formula (n + r),
      (∀ x : ↥(C \ intrinsicInterior ℝ C), (H ⟨x.val, x.property.1⟩).val = (h x).val) ∧
      (∀ x : C, (H x).val ∉ B ↔ x.val ∈ intrinsicInterior ℝ C) ∧
      (∀ z, z ∈ R.realize ↔ ∃ x : C,
        (∀ i, z (Fin.castAdd r i) = x.val i) ∧
        (∀ i, z (Fin.natAdd n i) = (H x).val i)) := by
  obtain ⟨q, hq, _⟩ := s2v_hardt6rb_ambient_restriction D (D \ intrinsicInterior ℝ D) A B
    (fun _ hx => hx.1) hBA e (fun x => by simpa only [Set.mem_diff, x.property, true_and] using he x)
  let k := h.trans q.symm
  obtain ⟨I, hI⟩ := s2v_hardt6rb_boundary_model_graph (C \ intrinsicInterior ℝ C)
    D (D \ intrinsicInterior ℝ D) A B (fun _ hx => hx.1) hBA e q h hq G J hG hJ
  obtain ⟨H, R, hH, hR⟩ := s2v_hardt6rb_radial_homeomorph_graph C D hC hD hc hd a b ha hb k hne I hI
  obtain ⟨W, hW⟩ := s2v_hardt6rb_actual_graph_compose C D A H e R J hR hJ
  obtain ⟨hbd, hint⟩ := s2v_hardt6rb_radial_boundary_restriction C D hc a b ha k H hH
  refine ⟨H.trans e, W, ?_, ?_, hW⟩
  · intro x
    have hx : H ⟨x.val, x.property.1⟩ = ⟨(k x).val, (k x).property.1⟩ := Subtype.ext (hbd x)
    change (e (H ⟨x.val, x.property.1⟩)).val = (h x).val
    rw [hx]
    exact (hq (q.symm (h x))).symm.trans (congrArg Subtype.val (q.apply_symm_apply (h x)))
  · intro x
    change (e (H x)).val ∉ B ↔ x.val ∈ intrinsicInterior ℝ C
    rw [← he (H x), not_not]
    exact hint x

end HodgeLean.Foundations.Program
