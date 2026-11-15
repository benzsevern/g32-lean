import HodgeLean.Foundations.QuotientDuality.PersistenceCollapse
import HodgeLean.Foundations.QuotientDuality.PersistenceDefs
import HodgeLean.Foundations.QuotientDuality.PersistencePairSequence

/-! Relative cohomology on the quotient side of a collapse comparison. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The canonical collapse map with its quotient-topology continuity. -/
def persistenceCollapseContinuousMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (A : Set Y) :
    ContinuousMap (Quotient (persistenceCollapseSetoid (f ⁻¹' A)))
      (Quotient (persistenceCollapseSetoid A)) :=
  ⟨persistenceCollapseMap f A, continuous_quot_map (by
    rintro x y (rfl | ⟨hx, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hx, hy⟩) hf⟩

lemma persistence_homeomorph_relative_preimage_bijective
    (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : IsHomeomorph f) (A : Set Y) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n (persistencePairMap f A)) := by
  let e := IsHomeomorph.homeomorph f hf
  let g : Y ⟶ X := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  let invPair : TopPair.ofSubset A ⟶ TopPair.ofSubset (f ⁻¹' A) :=
    TopPair.ofSubsetHom g (by
      intro y hy
      change e (e.symm y) ∈ A
      rw [e.apply_symm_apply]
      exact hy)
  have hfg : persistencePairMap f A ≫ invPair = 𝟙 _ := by
    apply persistence_pair_hom_ext
    apply TopCat.ext
    intro x
    exact e.symm_apply_apply x
  have hgf : invPair ≫ persistencePairMap f A = 𝟙 _ := by
    apply persistence_pair_hom_ext
    apply TopCat.ext
    intro y
    exact e.apply_symm_apply y
  have hright := congrArg (relativeCohomologyMap K n) hfg
  have hleft := congrArg (relativeCohomologyMap K n) hgf
  rw [relativeCohomologyMap_comp, relativeCohomologyMap_id] at hright hleft
  have hL : Function.LeftInverse (relativeCohomologyMap K n invPair)
      (relativeCohomologyMap K n (persistencePairMap f A)) :=
    fun u => LinearMap.congr_fun hleft u
  have hR : Function.RightInverse (relativeCohomologyMap K n invPair)
      (relativeCohomologyMap K n (persistencePairMap f A)) :=
    fun u => LinearMap.congr_fun hright u
  exact ⟨hL.injective, hR.surjective⟩

end HodgeLean.Foundations.QuotientDuality
