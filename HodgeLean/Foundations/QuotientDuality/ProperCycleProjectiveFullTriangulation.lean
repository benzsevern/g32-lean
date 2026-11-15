import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMarkedTriangulation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCommonSubdivision

/-! # Global projective triangulations with actual full algebraic subcomplexes -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- One actual finite global projective triangulation retains every original algebraic closed mark as a full subcomplex.
Source: properCycle_projective_marked_triangulation; s2v_hardt6rb_common_full_subdivision.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_full_triangulation
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] {r : ℕ}
    (Z : Fin r → Over (Spec ↧ℂ)) (i : ∀ j, Z j ⟶ X)
    [∀ j, IsClosedImmersion (i j).left] :
    ∃ a : ℕ, ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)),
      K.faces.Finite ∧ ∃ h : K.space ≃ₜ ComplexPoint X,
        ∀ j, ∃ D : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)),
          D.faces.Finite ∧ D.faces ⊆ K.faces ∧
            (∀ s ∈ K.faces, (∀ x ∈ s, x ∈ D.vertices) → s ∈ D.faces) ∧
            ∀ x : K.space, h x ∈ Set.range (Point.map (i j)) ↔ x.val ∈ D.space := by
  obtain ⟨a, K0, hK0, h0, hm⟩ := properCycle_projective_marked_triangulation X Z i
  obtain ⟨K, hK, he, hf⟩ := s2v_hardt6rb_common_full_subdivision K0 hK0
  let e : K.space ≃ₜ K0.space := Homeomorph.setCongr he
  refine ⟨a, K, hK, e.trans h0, ?_⟩
  intro j
  obtain ⟨D0, _, hD0, hm0⟩ := hm j
  obtain ⟨D, hD, hDK, hspace, hfull⟩ := hf D0 hD0
  refine ⟨D, hD, hDK, hfull, ?_⟩
  intro x
  change h0 (e x) ∈ Set.range (Point.map (i j)) ↔ x.val ∈ D.space
  rw [hm0, hspace]
  rfl

end HodgeLean.Foundations.QuotientDuality
