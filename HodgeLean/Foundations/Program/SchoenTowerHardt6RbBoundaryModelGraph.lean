import HodgeLean.Foundations.Program.SchoenTowerHardt6RbActualInverseFormula
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGraphCompose

/-! Actual boundary graph transport through an identified convex model boundary. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_boundary_model_graph {n m r : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (D T : Set (EuclideanSpace ℝ (Fin m)))
    (A B : Set (EuclideanSpace ℝ (Fin r))) (hTD : T ⊆ D) (hBA : B ⊆ A)
    (e : D ≃ₜ A) (q : T ≃ₜ B) (h : S ≃ₜ B)
    (hq : ∀ x : T, (q x).val = (e ⟨x.val, hTD x.property⟩).val)
    (G : s2v_t11b_Formula (n + r)) (J : s2v_t11b_Formula (m + r))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : S,
      (∀ i, z (Fin.castAdd r i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (h x).val i))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ x : D,
      (∀ i, z (Fin.castAdd r i) = x.val i) ∧
      (∀ i, z (Fin.natAdd m i) = (e x).val i)) :
    ∃ R : s2v_t11b_Formula (n + m), ∀ z, z ∈ R.realize ↔ ∃ x : S,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = ((h.trans q.symm) x).val i) := by
  obtain ⟨I, hI⟩ := s2v_hardt6rb_actual_inverse_formula D A e J hJ
  let f : S → A := fun x => ⟨(h x).val, hBA (h x).property⟩
  obtain ⟨R, hR⟩ := s2v_hardt6rb_actual_graph_compose S A D f e.symm G I hG hI
  have hk (x : S) : ((h.trans q.symm) x).val = (e.symm (f x)).val := by
    have heq : e ⟨(q.symm (h x)).val, hTD (q.symm (h x)).property⟩ = f x := by
      apply Subtype.ext
      exact (hq (q.symm (h x))).symm.trans (congrArg Subtype.val (q.apply_symm_apply (h x)))
    have hv := congrArg (fun y => (e.symm y).val) heq
    simpa only [e.symm_apply_apply, Homeomorph.trans_apply] using hv
  refine ⟨R, ?_⟩
  intro z
  simpa only [hk] using hR z

end HodgeLean.Foundations.Program
