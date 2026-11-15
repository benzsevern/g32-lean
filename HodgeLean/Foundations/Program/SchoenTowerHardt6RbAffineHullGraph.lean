import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandCoordinates
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPolyhedronFormula

/-! Affine endpoint graphs on actual finite hulls are finite lifted hulls. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_affine_hull_graph {n : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin n))) (A : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] ℝ) :
    ∃ g : s2v_t11b_Formula (n + 1), ∀ z, z ∈ g.realize ↔
      ∃ x ∈ convexHull ℝ (S : Set _), (∀ i, z i.succ = x i) ∧ z 0 = A x := by
  obtain ⟨e, he0, hes, _, _⟩ := s2v_hardt6rb_band_coordinate_equiv n
  let lift : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    e.toLinearMap.toAffineMap.comp ((AffineMap.id ℝ _).prod A)
  obtain ⟨g, hg⟩ := s2v_hardt6rb_finite_convexHull_formula (lift '' (S : Set _))
    (S.finite_toSet.image lift)
  refine ⟨g, ?_⟩
  intro z
  rw [hg, ← lift.image_convexHull]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, fun i => hes (x, A x) i, he0 (x, A x)⟩
  · rintro ⟨x, hx, hs, h0⟩
    refine ⟨x, hx, ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (he0 (x, A x)).trans h0.symm
    · exact (hes (x, A x) j).trans (hs j).symm

end HodgeLean.Foundations.Program
