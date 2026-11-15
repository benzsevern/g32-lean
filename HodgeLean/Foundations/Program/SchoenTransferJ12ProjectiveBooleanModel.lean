import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairClosedImmersionFormula

/-! Boolean Euclidean models of the actual projective complex-point spaces. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry Topology
open HodgeLean.WitnessSelection.StageTwo
namespace HodgeLean.Foundations.Program

/-- Projective complex-point spaces have actual Boolean Euclidean models.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
theorem s4_selected_projective_boolean_model
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] :
    ∃ (N : ℕ) (f : s2v_t11b_Formula N), Nonempty (ComplexPoint X ≃ₜ f.realize) := by
  classical
  let P := Classical.choice (IsProjective.nonempty_presentation (f := X.hom))
  obtain ⟨h, hh⟩ := s2e_c11_projective_comparison_aux P.ambientDimension
  let i : X ⟶ Over.mk
      (ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) (Spec ↧ℂ)) := P.overImmersion
  letI : IsClosedImmersion i.left := P.isClosedImmersion
  let e := fun x : ComplexPoint X =>
    s2e_pair_projectiveRealMatrix P.ambientDimension (h.symm (Point.map i x))
  have he : IsClosedEmbedding e :=
    (s2e_pair_projectiveRealMatrix_isClosedEmbedding _).comp
      (h.symm.isClosedEmbedding.comp (ComplexPoint.isClosedEmbedding_map_of_closedImmersion i))
  obtain ⟨f, hf⟩ := s2e_pair_closed_immersion_formula X i h hh
  exact ⟨_, f, ⟨he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hf.symm)⟩⟩

end HodgeLean.Foundations.Program
