import HodgeLean.Foundations.QuotientDuality.ProperCycleHomeomorphRelativeProjection
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveBoundaryProjection
import HodgeLean.Adapters.NormalConeB4aGysinReducedClosedDimension

/-! # Actual ordinary homology of projective supports across smaller boundaries
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal analytic support of an algebraic closed subset has an actual open neighborhood of any smaller algebraic boundary with bijective ordinary-to-relative projection above twice the boundary dimension plus one.
Source: properCycle_projective_boundary_projection_bijective; properCycle_homeomorph_relative_projection_bijective.
HC no distance; AV milestone no distance. -/
lemma properCycle_closed_support_boundary_projection
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (S B : Closeds X.left)
    (b : ℕ) (hdim : topologicalKrullDim B ≤ b) :
    ∃ N : Set {z : ComplexPoint X | z.underlying ∈ S}, IsOpen N ∧
      {z | z.val.underlying ∈ B} ⊆ N ∧
      ∀ n : ℕ, 2*b < n → Function.Bijective
        (relativeHomologyProjection ℚ (TopPair.ofSubset
          (X := TopCat.of {z : ComplexPoint X | z.underlying ∈ S}) N) (n+1)).hom := by
  let Y := Over.mk (reducedClosedStructureMap X.hom S)
  let j := properCycle_reduced_closed_map X S
  letI : IsProjective Y.hom := properCycle_closed_projective_structure X Y j
  let T : Closeds Y.left := ⟨j.left ⁻¹' (B : Set X.left), B.isClosed.preimage j.left.continuous⟩
  have hdimT : topologicalKrullDim T ≤ b := by
    have hf := j.left.isClosedEmbedding.isEmbedding.restrictPreimage (B : Set X.left)
    exact hf.isInducing.topologicalKrullDim_le.trans hdim
  let Z := Over.mk (reducedClosedStructureMap Y.hom T)
  let i := properCycle_reduced_closed_map Y T
  have hdimZ : topologicalKrullDim Z.left ≤ b := by
    change topologicalKrullDim (reducedClosedSubscheme T) ≤ b
    rw [a3b4a_gysin_reduced_closed_dimension_eq]
    exact hdimT
  obtain ⟨U, hU, hBU, hp⟩ := properCycle_projective_boundary_projection_bijective Y Z i b hdimZ
  have hr : Set.range (Point.map j) = {z : ComplexPoint X | z.underlying ∈ S} := by
    rw [range_map_of_closedImmersion]
    change {z : ComplexPoint X | z.underlying ∈ Set.range (reducedClosedSubschemeι S)} = _
    rw [range_reducedClosedSubschemeι]
    rfl
  let e : ComplexPoint Y ≃ₜ {z : ComplexPoint X | z.underlying ∈ S} :=
    (isEmbedding_map_of_closedImmersion j).toHomeomorph.trans (Homeomorph.setCongr hr)
  refine ⟨e '' U, e.isOpenMap U hU, ?_, ?_⟩
  · intro z hz
    let y := e.symm z
    have hyT : y.underlying ∈ T := by
      have he : Point.map j y = z.val := congrArg Subtype.val (e.apply_symm_apply z)
      change (Point.map j y).underlying ∈ B
      rw [he]
      exact hz
    have hyR : y ∈ Set.range (Point.map i) := by
      rw [range_map_of_closedImmersion]
      change y.underlying ∈ Set.range (reducedClosedSubschemeι T)
      rw [range_reducedClosedSubschemeι]
      exact hyT
    exact ⟨y, hBU hyR, e.apply_symm_apply z⟩
  · intro n hn
    exact properCycle_homeomorph_relative_projection_bijective
      (TopCat.of (ComplexPoint Y)) (TopCat.of {z : ComplexPoint X | z.underlying ∈ S})
      e U (n+1) (hp n hn)

end HodgeLean.Foundations.QuotientDuality
