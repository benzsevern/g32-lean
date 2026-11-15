import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairFullSubcomplexCollar
import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairFullTriangulation
import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairDeformationTransport

/-! Neighbourhood deformations for compact Boolean pairs.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- A relatively closed Boolean mark in a compact Boolean carrier has a fixed neighbourhood deformation. -/
theorem s2e_pair_boolean_neighbourhood_deformation {n : ℕ}
    (f b : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (hb : IsClosed (Subtype.val ⁻¹' b.realize : Set f.realize)) :
    let Q := TopPair.ofSubset (X := TopCat.of f.realize) (Subtype.val ⁻¹' b.realize)
    ∃ (U : TopCat.{0}) (j : Q.snd ⟶ U) (k : U ⟶ Q.fst),
      j ≫ k = Q.map ∧ Topology.IsOpenEmbedding k ∧
      ∃ q : U ⟶ Q.snd, j ≫ q = 𝟙 Q.snd ∧
        ∃ H : TopCat.Homotopy (𝟙 U) (q ≫ j),
          ∀ (t : unitInterval) (a : Q.snd), H (t, j a) = j a := by
  classical
  obtain ⟨L, M, hL, _, hML, hfull, h, hmark⟩ :=
    s2e_pair_boolean_full_triangulation f b hf hb
  let P := TopPair.ofSubset (X := TopCat.of L.space) {x | x.val ∈ M.space}
  let Q := TopPair.ofSubset (X := TopCat.of f.realize) (Subtype.val ⁻¹' b.realize)
  let eX : P.fst ≅ Q.fst := TopCat.isoOfHomeo h
  let eA : P.snd ≅ Q.snd := TopCat.isoOfHomeo (h.subtype (fun x => (hmark x).symm))
  have hsquare : P.map ≫ eX.hom = eA.hom ≫ Q.map := rfl
  obtain ⟨U, j, k, hfactor, hk, q, hq, H, hfixed⟩ :=
    s2e_pair_full_subcomplex_neighbourhood_deformation L M hL hML hfull
  obtain ⟨j', k', hfactor', hk', q', hq', H', hfixed'⟩ :=
    s2e_pair_neighbourhood_deformation_transport P Q eX eA hsquare
      U j k hfactor hk q hq H hfixed
  exact ⟨U, j', k', hfactor', hk', q', hq', H', hfixed'⟩

end Semialgebraic.CompatibleTriangulation.Helpers
