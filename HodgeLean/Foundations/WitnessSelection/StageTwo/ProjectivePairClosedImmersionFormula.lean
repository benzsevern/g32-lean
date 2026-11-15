import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairProjectiveLocusFormula
import HodgeLean.Foundations.Program.SchoenCycleC11SubProofs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact

/-! Boolean real matrix images of projective scheme immersions.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection.StageTwo

/-- A scheme immersed into projective space has a Boolean analytic matrix image.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_closed_immersion_formula {n : ℕ}
    (X : Over (Spec ↧ℂ))
    (i : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))
    [IsClosedImmersion i.left]
    (h : Projectivization ℂ (Fin (n + 1) → ℂ) ≃ₜ
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))))
    (hh : (h : _ → _) = ComplexProjectiveSpace.projectivizationToComplexPoint) :
    ∃ f : s2v_t11b_Formula (Fintype.card
      ((Fin (n + 1) × Fin (n + 1)) ⊕ (Fin (n + 1) × Fin (n + 1)))),
      f.realize = Set.range (fun x : ComplexPoint X =>
        s2e_pair_projectiveRealMatrix n (h.symm (Point.map i x))) := by
  obtain ⟨f, hf⟩ := s2e_pair_projective_locus_formula (Set.range i.left)
    i.left.isClosedEmbedding.isClosed_range
  refine ⟨f, ?_⟩
  ext z
  rw [hf]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : h p ∈ Set.range (Point.map i) := by
      rw [ComplexPoint.range_map_of_closedImmersion]
      change (h p).underlying ∈ Set.range i.left
      simpa only [hh] using hp
    obtain ⟨x, hx⟩ := hp'
    refine ⟨x, ?_⟩
    change s2e_pair_projectiveRealMatrix n (h.symm (Point.map i x)) = _
    rw [hx, h.symm_apply_apply]
  · rintro ⟨x, rfl⟩
    refine ⟨h.symm (Point.map i x), ?_, rfl⟩
    have hx : Point.map i x ∈ Set.range (Point.map i) := ⟨x, rfl⟩
    rw [ComplexPoint.range_map_of_closedImmersion] at hx
    change (Point.map i x).underlying ∈ Set.range i.left at hx
    simpa only [← hh, h.apply_symm_apply] using hx

end HodgeLean.WitnessSelection.StageTwo
