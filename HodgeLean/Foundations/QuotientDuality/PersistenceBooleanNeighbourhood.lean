import HodgeLean.Foundations.QuotientDuality.PersistenceNeighbourhoodRange
import HodgeLean.Foundations.Semialgebraic.CompatibleTriangulation

/-! Actual open subset neighbourhoods for compact Boolean pairs. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_boolean_neighbourhood_deformation {n : ℕ}
    (f b : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (hb : IsClosed (Subtype.val ⁻¹' b.realize : Set f.realize)) :
    let A := (Subtype.val ⁻¹' b.realize : Set f.realize)
    ∃ (V : Set f.realize), IsOpen V ∧ ∃ (hAV : A ⊆ V)
      (q : TopCat.of V ⟶ TopCat.of A),
      persistenceSubsetNeighbourhoodInclusion A V hAV ≫ q = 𝟙 (TopCat.of A) ∧
      ∃ H : TopCat.Homotopy (𝟙 (TopCat.of V))
        (q ≫ persistenceSubsetNeighbourhoodInclusion A V hAV),
        ∀ (t : unitInterval) (a : A),
          H (t, persistenceSubsetNeighbourhoodInclusion A V hAV a) =
            persistenceSubsetNeighbourhoodInclusion A V hAV a := by
  obtain ⟨U, j, k, hfactor, hk, q, hq, H, hfixed⟩ :=
    Semialgebraic.CompatibleTriangulation.compact_pair_neighbourhood_deformation f b hf hb
  obtain ⟨hopen, hAV, q', hq', H', hfixed'⟩ :=
    persistence_neighbourhood_range_deformation _ U j k hfactor hk q hq H hfixed
  exact ⟨Set.range k, hopen, hAV, q', hq', H', hfixed'⟩

end HodgeLean.Foundations.QuotientDuality
