import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMarkedBooleanModel
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbClosedMarkSubcomplex

/-! # Global finite triangulations with original projective algebraic marks -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- An original projective complex scheme has a finite global geometric triangulation retaining every specified algebraic closed immersion as an actual subcomplex.
Source: properCycle_projective_marked_boolean_model; s2v_hardt6rb_compact_compatible_triangulation; s2v_hardt6rb_closed_mark_subcomplex.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_marked_triangulation
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] {r : ℕ}
    (Z : Fin r → Over (Spec ↧ℂ)) (i : ∀ j, Z j ⟶ X)
    [∀ j, IsClosedImmersion (i j).left] :
    ∃ a : ℕ, ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)),
      K.faces.Finite ∧ ∃ h : K.space ≃ₜ ComplexPoint X,
        ∀ j, ∃ D : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)),
          D.faces.Finite ∧ D.faces ⊆ K.faces ∧
            ∀ x : K.space, h x ∈ Set.range (Point.map (i j)) ↔ x.val ∈ D.space := by
  obtain ⟨a, B, hB, hX, b, hb⟩ := properCycle_projective_marked_boolean_model X Z i
  obtain ⟨K, hK, h0, hm, _⟩ := s2v_hardt6rb_compact_compatible_triangulation a B hB b
  let h := h0.trans hX.symm
  refine ⟨a, K, hK, h, ?_⟩
  intro j
  obtain ⟨S, hS, hsel⟩ := hm j
  have hc : IsClosed (Subtype.val ⁻¹' (b j).realize : Set B.realize) := by
    convert (isClosed_range_map_of_closedImmersion (i j)).preimage hX.symm.continuous using 1
    ext z
    change z.val ∈ (b j).realize ↔ hX.symm z ∈ Set.range (Point.map (i j))
    simpa only [Homeomorph.apply_symm_apply] using hb (hX.symm z) j
  obtain ⟨D, hD, hDK, hDm⟩ :=
    s2v_hardt6rb_closed_mark_subcomplex K hK B.realize (b j).realize h0 hc S hS hsel
  refine ⟨D, hD, hDK, ?_⟩
  intro x
  have hx : (h0 x).val ∈ (b j).realize ↔ h x ∈ Set.range (Point.map (i j)) := by
    simpa only [h, Homeomorph.trans_apply, Homeomorph.apply_symm_apply] using hb (h x) j
  exact hx.symm.trans (hDm x)

end HodgeLean.Foundations.QuotientDuality
