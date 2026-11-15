import HodgeLean.Foundations.QuotientDuality.PersistenceCollapsePairs
import Mathlib.Algebra.Homology.QuasiIso

/-! Actual pair isomorphisms on the canonical preimage pairs of homeomorphisms. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual preimage pair map of a homeomorphism, with its specified inverse. -/
def persistenceHomeomorphPairIso
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsHomeomorph f) (A : Set Y) :
    TopPair.ofSubset (f ⁻¹' A) ≅ TopPair.ofSubset A := by
  let e := IsHomeomorph.homeomorph f hf
  let g : Y ⟶ X := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  let invPair : TopPair.ofSubset A ⟶ TopPair.ofSubset (f ⁻¹' A) :=
    TopPair.ofSubsetHom g (by
      intro y hy
      change e (e.symm y) ∈ A
      rw [e.apply_symm_apply]
      exact hy)
  exact {
    hom := persistencePairMap f A
    inv := invPair
    hom_inv_id := by
      apply persistence_pair_hom_ext
      apply TopCat.ext
      exact e.symm_apply_apply
    inv_hom_id := by
      apply persistence_pair_hom_ext
      apply TopCat.ext
      exact e.apply_symm_apply }

lemma persistence_homeomorph_relative_chain_quasiIso
    (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : IsHomeomorph f) (A : Set Y) :
    QuasiIso ((relativeChainFunctor K).map (persistencePairMap f A)) := by
  haveI : IsIso (persistencePairMap f A) := (persistenceHomeomorphPairIso f hf A).isIso_hom
  infer_instance

end HodgeLean.Foundations.QuotientDuality
