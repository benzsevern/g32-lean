import HodgeLean.Foundations.Program.SchoenTowerComparisonProofs

/-! # Equivariant finite-cover comparison
Implication from a finite map of projective complex schemes to the singular
and sheaf cohomology comparison with the specified generator.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The finite pushforward comparison intertwines the actual generator and
coefficient multiplication; the image projector realizes its eigenspace.
Source: G32 v0.16, Lemma 4.3, first equality; finite proper base change. -/
theorem s2d_finite_cover_comparison (W B E : Over (Spec ↧ℂ))
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (d : W ⟶ W) (hd : d ≫ β = β)
    (m : ℕ) (hm : 0 < m) (horder : (End.of d) ^ m = 1)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (n : ℕ) :
    let f := s2c_points.map (s2b_toExceptional β j)
    let δ := s2c_points.map (s2b_preimageDeck β j d hd)
    ∃ hδ : δ ≫ f = f,
      ∃ c : AlgebraicTopology.Singular.Cohomology ℂ
        (s2c_points.obj (s2b_preimage β j)) n ≃+ Sheaf.H (s2c_coverSheaf f) n,
        (∀ v, c (s2b_preimageCohomologyDeck β j d hd n v) =
          Sheaf.H.map (s2c_coverSheafDeck f δ hδ) n (c v)) ∧
        (∀ (z : ℂ) v, c (z • v) =
          Sheaf.H.map (s2c_coverSheafScalar f z) n (c v)) ∧
        ∃ e : Sheaf.H (s2c_characterSheaf f δ hδ m ζ) n ≃+
          (Module.End.eigenspace (s2b_preimageCohomologyDeck β j d hd n) ζ),
          ∀ v, c (e v).val = Sheaf.H.map
            (image.ι (s2c_characterProjector f δ hδ m ζ)) n v :=
  s2d_finite_cover_comparison_aux W B E β j d hd m hm horder ζ hζ n

example := @s2d_finite_cover_comparison

end HodgeLean.Foundations.Program
