import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveClosedBooleanImage

/-! # Actual global Boolean models of closed projective subschemes -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- An original closed projective subscheme retains a compact Boolean carrier and a homeomorphism with its literal scheme projective coordinate values.
Source: isClosedEmbedding_map_of_closedImmersion; properCycle_projective_closed_boolean_image.
HC no distance; AV milestone no distance. -/
theorem properCycle_closed_projective_boolean_model (n : ℕ) (Z : Over (Spec ↧ℂ))
    (j : Z ⟶ Over.mk (ProjectiveSpace.toBase (Fin (n+1)) (Spec ↧ℂ)))
    [IsClosedImmersion j.left] :
    ∃ B : s2v_t11b_Formula (Fintype.card
      ((Fin (n+1) × Fin (n+1)) ⊕ (Fin (n+1) × Fin (n+1)))),
      IsCompact B.realize ∧ ∃ h : ComplexPoint Z ≃ₜ B.realize,
        ∀ z, (h z).val =
          (properCycle_projective_boolean_homeomorph n (Point.map j z)).val := by
  obtain ⟨B, hB⟩ := properCycle_projective_closed_boolean_image n Z j
  let f (z : ComplexPoint Z) :=
    (properCycle_projective_boolean_homeomorph n (Point.map j z)).val
  have hf : Topology.IsEmbedding f :=
    (Topology.IsEmbedding.subtypeVal.comp
      (properCycle_projective_boolean_homeomorph n).isEmbedding).comp
        (isEmbedding_map_of_closedImmersion j)
  let h : ComplexPoint Z ≃ₜ B.realize :=
    hf.toHomeomorph.trans (Homeomorph.setCongr hB.symm)
  letI : CompactSpace (ComplexPoint Z) :=
    (isClosedEmbedding_map_of_closedImmersion j).compactSpace
  have hcompact : IsCompact B.realize := by
    rw [hB]
    exact isCompact_range ((continuous_subtype_val.comp
      (properCycle_projective_boolean_homeomorph n).continuous).comp (Point.continuous_map j))
  exact ⟨B, hcompact, h, fun _ => rfl⟩

end HodgeLean.Foundations.QuotientDuality
