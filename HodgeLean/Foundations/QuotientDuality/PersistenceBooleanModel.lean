import HodgeLean.Foundations.QuotientDuality.PersistenceBooleanNeighbourhood
import HodgeLean.Foundations.QuotientDuality.PersistenceMarkedHomeomorph
import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairDeformationTransport

/-! Actual neighbourhoods transported from compact Boolean models. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_boolean_model_neighbourhood_deformation
    {X : Type} [TopologicalSpace X] (A : Set X) {n : ℕ}
    (f b : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (hb : IsClosed (Subtype.val ⁻¹' b.realize : Set f.realize))
    (e : X ≃ₜ f.realize) (hmark : ∀ x, (e x).val ∈ b.realize ↔ x ∈ A) :
    ∃ (V : Set X), IsOpen V ∧ ∃ (hAV : A ⊆ V)
      (q : TopCat.of V ⟶ TopCat.of A),
      persistenceSubsetNeighbourhoodInclusion A V hAV ≫ q = 𝟙 (TopCat.of A) ∧
      ∃ H : TopCat.Homotopy (𝟙 (TopCat.of V))
        (q ≫ persistenceSubsetNeighbourhoodInclusion A V hAV),
        ∀ (t : unitInterval) (a : A),
          H (t, persistenceSubsetNeighbourhoodInclusion A V hAV a) =
            persistenceSubsetNeighbourhoodInclusion A V hAV a := by
  let B := (Subtype.val ⁻¹' b.realize : Set f.realize)
  let P := TopPair.ofSubset (X := TopCat.of f.realize) B
  let Q := TopPair.ofSubset (X := TopCat.of X) A
  let eA := persistenceMarkedHomeomorph e A B hmark
  let eXiso : P.fst ≅ Q.fst := TopCat.isoOfHomeo e.symm
  let eAiso : P.snd ≅ Q.snd := TopCat.isoOfHomeo eA.symm
  have hsquare : P.map ≫ eXiso.hom = eAiso.hom ≫ Q.map := rfl
  obtain ⟨U, j, k, hfactor, hk, q, hq, H, hfixed⟩ :=
    Semialgebraic.CompatibleTriangulation.compact_pair_neighbourhood_deformation f b hf hb
  obtain ⟨j', k', hfactor', hk', q', hq', H', hfixed'⟩ :=
    Semialgebraic.CompatibleTriangulation.Helpers.s2e_pair_neighbourhood_deformation_transport
      P Q eXiso eAiso hsquare U j k hfactor hk q hq H hfixed
  obtain ⟨hopen, hAV, q'', hq'', H'', hfixed''⟩ :=
    persistence_neighbourhood_range_deformation A U j' k' hfactor' hk' q' hq' H' hfixed'
  exact ⟨Set.range k', hopen, hAV, q'', hq'', H'', hfixed''⟩

lemma persistence_boolean_model_locus_isClosed
    {X : Type} [TopologicalSpace X] (A : Set X) {n : ℕ}
    (f b : s2v_t11b_Formula n)
    (hb : IsClosed (Subtype.val ⁻¹' b.realize : Set f.realize))
    (e : X ≃ₜ f.realize) (hmark : ∀ x, (e x).val ∈ b.realize ↔ x ∈ A) :
    IsClosed A := by
  have heq : e ⁻¹' (Subtype.val ⁻¹' b.realize : Set f.realize) = A := by
    ext x
    exact hmark x
  rw [← heq]
  exact hb.preimage e.continuous

end HodgeLean.Foundations.QuotientDuality
