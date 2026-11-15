import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAmbientBandCoordinateGraph
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineHullGraph

/-! Actual affine source endpoints and nonlinear endpoint graphs give the full local model graph. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_affine_band_model_graph {n N : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin n)))
    (l u : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] ℝ) (c d : EuclideanSpace ℝ (Fin n) → ℝ)
    (gc gd : s2v_t11b_Formula (n + 1))
    (hgc : ∀ z, z ∈ gc.realize ↔ ∃ x ∈ convexHull ℝ (S : Set _),
      (∀ i, z i.succ = x i) ∧ z 0 = c x)
    (hgd : ∀ z, z ∈ gd.realize ↔ ∃ x ∈ convexHull ℝ (S : Set _),
      (∀ i, z i.succ = x i) ∧ z 0 = d x)
    (h : {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 ∈ convexHull ℝ (S : Set _) ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1} ≃ₜ
      {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 ∈ convexHull ℝ (S : Set _) ∧ c p.1 ≤ p.2 ∧ p.2 ≤ d p.1})
    (hh : ∀ p q, h p = q ↔ p.val.1 = q.val.1 ∧
      (p.val.2 - l p.val.1) * (d p.val.1 - c p.val.1) =
        (q.val.2 - c p.val.1) * (u p.val.1 - l p.val.1))
    (e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (he0 : ∀ p, e p 0 = p.2) (hes : ∀ p i, e p i.succ = p.1 i)
    (idx outIdx : Fin (n + 1) → Fin N) :
    ∃ G : s2v_t11b_Formula N, ∀ z, z ∈ G.realize ↔ ∃ p,
      (∀ i, z (idx i) = e p.val i) ∧ (∀ i, z (outIdx i) = e (h p).val i) := by
  obtain ⟨F, hF⟩ := s2v_hardt6rb_finite_convexHull_formula (S : Set (EuclideanSpace ℝ (Fin n))) S.finite_toSet
  obtain ⟨gl, hgl⟩ := s2v_hardt6rb_affine_hull_graph S l
  obtain ⟨gu, hgu⟩ := s2v_hardt6rb_affine_hull_graph S u
  let g : Fin 4 → s2v_t11b_Formula (n + 1) := ![gl, gu, gc, gd]
  have hg0 : ∀ i z, z ∈ (g i).realize ↔ ∃ x ∈ convexHull ℝ (S : Set _),
      (∀ v, z v.succ = x v) ∧ z 0 = (![(l : _ → ℝ), (u : _ → ℝ), c, d] i) x := by
    intro i z
    fin_cases i
    · exact hgl z
    · exact hgu z
    · exact hgc z
    · exact hgd z
  have hg : ∀ i z, z ∈ (g i).realize ↔ ∃ x : F.realize,
      (∀ v, z v.succ = x.val v) ∧ z 0 = (![(l : _ → ℝ), (u : _ → ℝ), c, d] i) x.val := by
    intro i z
    rw [hg0]
    constructor
    · rintro ⟨x, hx, hb, ht⟩
      exact ⟨⟨x, hF.symm ▸ hx⟩, hb, ht⟩
    · rintro ⟨x, hb, ht⟩
      exact ⟨x.val, hF ▸ x.property, hb, ht⟩
  revert h
  rw [← hF]
  intro h hh
  exact s2v_hardt6rb_ambient_band_coordinate_graph F l u c d g hg _ rfl h hh e he0 hes idx outIdx

end HodgeLean.Foundations.Program
