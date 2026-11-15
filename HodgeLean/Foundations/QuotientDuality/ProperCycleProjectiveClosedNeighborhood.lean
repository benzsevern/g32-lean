import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMarkedBooleanModel
import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairBooleanCollar

/-! # Actual deformation neighborhoods of original closed projective supports -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
open Semialgebraic.CompatibleTriangulation.Helpers
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal image of an original closed immersion into a projective complex scheme has an actual open neighborhood that strongly deforms onto that image.
Source: properCycle_projective_marked_boolean_model; s2e_pair_boolean_neighbourhood_deformation; s2e_pair_neighbourhood_deformation_transport.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_closed_neighborhood_deformation
    (X Z : Over (Spec ↧ℂ)) [IsProjective X.hom] (i : Z ⟶ X)
    [IsClosedImmersion i.left] :
    let P := TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (Set.range (Point.map i))
    ∃ (U : TopCat.{0}) (j : P.snd ⟶ U) (k : U ⟶ P.fst),
      j ≫ k = P.map ∧ Topology.IsOpenEmbedding k ∧
      ∃ q : U ⟶ P.snd, j ≫ q = 𝟙 P.snd ∧
        ∃ H : TopCat.Homotopy (𝟙 U) (q ≫ j),
          ∀ (t : unitInterval) (z : P.snd), H (t, j z) = j z := by
  obtain ⟨a, B, hB, hX, b, hb⟩ := properCycle_projective_marked_boolean_model X
    (fun _ : Fin 1 => Z) (fun _ => i)
  let P := TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (Set.range (Point.map i))
  let Q := TopPair.ofSubset (X := TopCat.of B.realize) (Subtype.val ⁻¹' (b 0).realize)
  have hm (z : B.realize) : z.val ∈ (b 0).realize ↔ hX.symm z ∈ Set.range (Point.map i) := by
    simpa only [Homeomorph.apply_symm_apply] using hb (hX.symm z) 0
  have hc : IsClosed (Subtype.val ⁻¹' (b 0).realize : Set B.realize) := by
    convert (isClosed_range_map_of_closedImmersion i).preimage hX.symm.continuous using 1
    ext z
    exact hm z
  let eX : Q.fst ≅ P.fst := TopCat.isoOfHomeo hX.symm
  let eA : Q.snd ≅ P.snd := TopCat.isoOfHomeo (hX.symm.subtype hm)
  have hsquare : Q.map ≫ eX.hom = eA.hom ≫ P.map := rfl
  obtain ⟨U, j, k, hfactor, hk, q, hq, H, hfixed⟩ :=
    s2e_pair_boolean_neighbourhood_deformation B (b 0) hB hc
  obtain ⟨j', k', hf', hk', q', hq', H', hfixed'⟩ :=
    s2e_pair_neighbourhood_deformation_transport Q P eX eA hsquare U j k hfactor hk q hq H hfixed
  exact ⟨U, j', k', hf', hk', q', hq', H', hfixed'⟩

end HodgeLean.Foundations.QuotientDuality
