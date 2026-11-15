import HodgeLean.Foundations.QuotientDuality.PersistenceSubsetEnlargement
import Mathlib.Topology.Homeomorph.Lemmas

/-! Actual range neighbourhoods from specified open embeddings. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_neighbourhood_range_deformation
    {X : Type} [TopologicalSpace X] (A : Set X) (U : TopCat.{0})
    (j : TopCat.of A ⟶ U) (k : U ⟶ TopCat.of X)
    (hfactor : j ≫ k = (TopPair.ofSubset (X := TopCat.of X) A).map)
    (hk : IsOpenEmbedding k) (q : U ⟶ TopCat.of A) (hq : j ≫ q = 𝟙 (TopCat.of A))
    (H : TopCat.Homotopy (𝟙 U) (q ≫ j))
    (hfixed : ∀ (t : unitInterval) (a : A), H (t, j a) = j a) :
    IsOpen (Set.range k) ∧ ∃ (hAR : A ⊆ Set.range k)
      (q' : TopCat.of (Set.range k) ⟶ TopCat.of A),
      persistenceSubsetNeighbourhoodInclusion A (Set.range k) hAR ≫ q' = 𝟙 (TopCat.of A) ∧
      ∃ H' : TopCat.Homotopy (𝟙 (TopCat.of (Set.range k)))
        (q' ≫ persistenceSubsetNeighbourhoodInclusion A (Set.range k) hAR),
        ∀ (t : unitInterval) (a : A),
          H' (t, persistenceSubsetNeighbourhoodInclusion A (Set.range k) hAR a) =
            persistenceSubsetNeighbourhoodInclusion A (Set.range k) hAR a := by
  let e := hk.isEmbedding.toHomeomorph
  let p : U ⟶ TopCat.of (Set.range k) := TopCat.ofHom ⟨e, e.continuous⟩
  let v : TopCat.of (Set.range k) ⟶ U := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hAR : A ⊆ Set.range k := by
    intro a ha
    exact ⟨j ⟨a, ha⟩, congrArg (fun f => f ⟨a, ha⟩) hfactor⟩
  let j' := persistenceSubsetNeighbourhoodInclusion A (Set.range k) hAR
  have hje : j' = j ≫ p := by
    apply TopCat.ext
    intro a
    apply Subtype.ext
    exact (congrArg (fun f => f a) hfactor).symm
  have hpv : p ≫ v = 𝟙 U := by
    apply TopCat.ext
    exact e.symm_apply_apply
  refine ⟨hk.isOpen_range, hAR, v ≫ q, ?_, ?_⟩
  · change j' ≫ (v ≫ q) = _
    rw [hje, ← Category.assoc, Category.assoc j p v, hpv, Category.comp_id, hq]
  · let H' : TopCat.Homotopy (𝟙 (TopCat.of (Set.range k))) ((v ≫ q) ≫ j') := {
      toFun := fun z => e (H (z.1, e.symm z.2))
      continuous_toFun := e.continuous.comp (H.continuous.comp
        (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
      map_zero_left := by
        intro y
        change e (H (0, e.symm y)) = y
        rw [H.apply_zero]
        exact e.apply_symm_apply y
      map_one_left := by
        intro y
        change e (H (1, e.symm y)) = j' (q (e.symm y))
        rw [H.apply_one]
        exact (congrArg (fun f => f (q (e.symm y))) hje).symm }
    refine ⟨H', ?_⟩
    intro t a
    have hja : j' a = e (j a) := congrArg (fun f => f a) hje
    change e (H (t, e.symm (j' a))) = j' a
    rw [hja, e.symm_apply_apply, hfixed]

end HodgeLean.Foundations.QuotientDuality
