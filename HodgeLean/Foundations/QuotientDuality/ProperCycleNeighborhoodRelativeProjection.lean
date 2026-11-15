import HodgeLean.Foundations.QuotientDuality.ProperCycleOrdinaryRelativeProjection

/-! # Original relative homology projections through actual deformation neighborhoods -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual open neighborhood embedding and its original homotopy retraction give a bijective ordinary to relative homology projection when the support homology vanishes in adjacent degrees.
Source: properCycle_homotopy_retraction_homology_vanishes; properCycle_ordinary_relative_projection_bijective.
HC no distance; AV milestone no distance. -/
theorem properCycle_deformation_neighborhood_projection_bijective
    {X A U : TopCat.{0}} (j : A ⟶ U) (q : U ⟶ A) (k : U ⟶ X)
    (hk : Topology.IsEmbedding k) (H : TopCat.Homotopy (𝟙 U) (q ≫ j))
    (n : ℕ) (hn : Subsingleton (Homology ℚ A (n+1)))
    (hp : Subsingleton (Homology ℚ A n)) :
    Function.Bijective
      (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) (Set.range k)) (n+1)).hom := by
  have hU (m : ℕ) (hm : Subsingleton (Homology ℚ A m)) :
      Subsingleton (Homology ℚ U m) :=
    properCycle_homotopy_retraction_homology_vanishes j q H m hm
  have hr (m : ℕ) (hm : Subsingleton (Homology ℚ A m)) :
      Subsingleton (Homology ℚ (TopCat.of (Set.range k)) m) :=
    properCycle_homeomorph_homology_subsingleton
      (X := TopCat.of (Set.range k)) (Y := U) hk.toHomeomorph.symm m (hU m hm)
  exact properCycle_ordinary_relative_projection_bijective _ n (hr (n+1) hn) (hr n hp)

end HodgeLean.Foundations.QuotientDuality
