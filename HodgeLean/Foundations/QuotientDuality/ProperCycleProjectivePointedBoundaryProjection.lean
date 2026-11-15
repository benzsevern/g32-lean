import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodRelativeProjection
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectivePointedNeighborhood

/-! # Original projective homology across actual small algebraic boundary neighborhoods -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original projective closed boundary has an actual open neighborhood avoiding a specified outside point, with bijective original ordinary to relative homology projection above twice the boundary dimension plus one.
Source: properCycle_projective_pointed_neighborhood_deformation; properCycle_projective_homology_dimension_vanishes; properCycle_deformation_neighborhood_projection_bijective.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_pointed_boundary_projection_bijective
    (X Z : Over (Spec ↧ℂ)) [IsProjective X.hom] (i : Z ⟶ X)
    [IsClosedImmersion i.left] (b : ℕ) (hdim : topologicalKrullDim Z.left ≤ b)
    (x : ComplexPoint X) (hx : x ∉ Set.range (Point.map i)) :
    ∃ N : Set (ComplexPoint X), IsOpen N ∧ Set.range (Point.map i) ⊆ N ∧ x ∉ N ∧
      ∀ n : ℕ, 2*b < n → Function.Bijective
        (relativeHomologyProjection ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) N)
          (n+1)).hom := by
  let P := TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (Set.range (Point.map i))
  obtain ⟨U, j, k, hf, hk, hxN, q, _, H, _⟩ :=
    properCycle_projective_pointed_neighborhood_deformation X Z i x hx
  letI : IsProjective Z.hom := properCycle_closed_projective_structure X Z i
  have hA (n : ℕ) (hn : 2*b < n) : Subsingleton (Homology ℚ P.snd n) :=
    properCycle_homeomorph_homology_subsingleton
      (X := P.snd) (Y := TopCat.of (ComplexPoint Z))
      (isEmbedding_map_of_closedImmersion i).toHomeomorph.symm n
      (properCycle_projective_homology_dimension_vanishes Z b hdim n hn)
  refine ⟨Set.range k, hk.isOpen_range, ?_, hxN, ?_⟩
  · intro x hx
    let a : P.snd := ⟨x, hx⟩
    refine ⟨j a, ?_⟩
    exact congrArg (fun f => f a) hf
  · intro n hn
    exact properCycle_deformation_neighborhood_projection_bijective j q k hk.isEmbedding H n
      (hA (n+1) (by omega)) (hA n hn)

end HodgeLean.Foundations.QuotientDuality
