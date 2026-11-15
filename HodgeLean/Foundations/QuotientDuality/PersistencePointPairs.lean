import HodgeLean.Foundations.QuotientDuality.PersistenceCollapsePairs

/-! Canonical maps between specified singleton pairs. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal map between singleton pairs specified by an ambient map and a point. -/
def persistencePointPairMap {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    TopPair.ofSubset ({x} : Set X) ⟶ TopPair.ofSubset ({f x} : Set Y) :=
  TopPair.ofSubsetHom f (by
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    rfl)

lemma persistence_point_pair_relative_cohomology_bijective
    (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : IsHomeomorph f) (x : X) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n (persistencePointPairMap f x)) := by
  let e := hf.homeomorph f
  let g : Y ⟶ X := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  let invPair : TopPair.ofSubset ({f x} : Set Y) ⟶ TopPair.ofSubset ({x} : Set X) :=
    TopPair.ofSubsetHom g (by
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact e.symm_apply_apply x)
  have hfg : persistencePointPairMap f x ≫ invPair = 𝟙 _ := by
    apply persistence_pair_hom_ext
    apply TopCat.ext
    exact e.symm_apply_apply
  have hgf : invPair ≫ persistencePointPairMap f x = 𝟙 _ := by
    apply persistence_pair_hom_ext
    apply TopCat.ext
    exact e.apply_symm_apply
  have hright := congrArg (relativeCohomologyMap K n) hfg
  have hleft := congrArg (relativeCohomologyMap K n) hgf
  rw [relativeCohomologyMap_comp, relativeCohomologyMap_id] at hright hleft
  have hL : Function.LeftInverse (relativeCohomologyMap K n invPair)
      (relativeCohomologyMap K n (persistencePointPairMap f x)) :=
    fun u => LinearMap.congr_fun hleft u
  have hR : Function.RightInverse (relativeCohomologyMap K n invPair)
      (relativeCohomologyMap K n (persistencePointPairMap f x)) :=
    fun u => LinearMap.congr_fun hright u
  exact ⟨hL.injective, hR.surjective⟩

end HodgeLean.Foundations.QuotientDuality
