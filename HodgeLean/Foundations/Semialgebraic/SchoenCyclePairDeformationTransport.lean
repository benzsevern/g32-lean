import Mathlib.Topology.Category.TopPair
import Mathlib.Topology.Homotopy.TopCat.Basic

/-! Transport of specified neighbourhood deformations through isomorphisms of pairs.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- Isomorphisms of pairs transport an open neighbourhood and its fixed deformation. -/
theorem s2e_pair_neighbourhood_deformation_transport (P Q : TopPair.{0})
    (eX : P.fst ≅ Q.fst) (eA : P.snd ≅ Q.snd)
    (hsquare : P.map ≫ eX.hom = eA.hom ≫ Q.map)
    (U : TopCat.{0}) (j : P.snd ⟶ U) (k : U ⟶ P.fst)
    (hfactor : j ≫ k = P.map) (hk : Topology.IsOpenEmbedding k)
    (q : U ⟶ P.snd) (hq : j ≫ q = 𝟙 P.snd)
    (H : TopCat.Homotopy (𝟙 U) (q ≫ j))
    (hfixed : ∀ (s : unitInterval) (a : P.snd), H (s, j a) = j a) :
    ∃ (j' : Q.snd ⟶ U) (k' : U ⟶ Q.fst),
      j' ≫ k' = Q.map ∧ Topology.IsOpenEmbedding k' ∧
      ∃ q' : U ⟶ Q.snd, j' ≫ q' = 𝟙 Q.snd ∧
        ∃ H' : TopCat.Homotopy (𝟙 U) (q' ≫ j'),
          ∀ (s : unitInterval) (a : Q.snd), H' (s, j' a) = j' a := by
  refine ⟨eA.inv ≫ j, k ≫ eX.hom, ?_, ?_, q ≫ eA.hom, ?_, ?_⟩
  · rw [← Category.assoc, Category.assoc eA.inv j k, hfactor,
      Category.assoc, hsquare, Iso.inv_hom_id_assoc]
  · exact (TopCat.homeoOfIso eX).isOpenEmbedding.comp hk
  · rw [Category.assoc, ← Category.assoc j q, hq, Category.id_comp,
      Iso.inv_hom_id]
  · have he : (q ≫ eA.hom) ≫ eA.inv ≫ j = q ≫ j := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    refine ⟨{ toContinuousMap := H.toContinuousMap
              map_zero_left := H.map_zero_left
              map_one_left := ?_ }, ?_⟩
    · intro x
      exact (H.map_one_left x).trans
        (congrArg (fun f : U ⟶ U => f x) he).symm
    · intro s a
      exact hfixed s (eA.inv a)

end Semialgebraic.CompatibleTriangulation.Helpers
