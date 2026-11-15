import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseComplement
import HodgeLean.Foundations.QuotientDuality.PersistenceCollapsePairs
import HodgeLean.Foundations.QuotientDuality.PersistencePuncturedExcision

/-! The excision square for the actual quotient projection. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- The quotient projection on the actual enlarged pairs. -/
def persistenceCollapseEnlargedPairMap
    {X : Type} [TopologicalSpace X] (A : Set X)
    (V : Set (Quotient (persistenceCollapseSetoid A))) :=
  persistencePairMap
    (TopCat.ofHom ⟨Quotient.mk (persistenceCollapseSetoid A), continuous_quotient_mk'⟩) V

lemma persistence_collapse_complement_homeomorph_val
    {X : Type*} [TopologicalSpace X] (A : Set X) (hA : IsClosed A)
    (x : ↥(Aᶜ : Set X)) :
    (persistenceCollapseComplementHomeomorph A hA x).val =
      Quotient.mk (persistenceCollapseSetoid A) x.val := rfl

/-- The canonical preimage pair map on the actual complements. -/
def persistenceCollapsePuncturedPairMap
    {X : Type} [TopologicalSpace X] (A : Set X) (hA : IsClosed A)
    (V : Set (Quotient (persistenceCollapseSetoid A))) :
    TopPair.ofSubset (X := TopCat.of ↥(Aᶜ : Set X))
        {x | Quotient.mk (persistenceCollapseSetoid A) x.val ∈ V} ⟶
      TopPair.ofSubset
        (X := TopCat.of ↥(((Quotient.mk (persistenceCollapseSetoid A)) '' A)ᶜ))
        {y | y.val ∈ V} :=
  persistencePairMap (TopCat.ofHom
    ⟨persistenceCollapseComplementHomeomorph A hA,
      (persistenceCollapseComplementHomeomorph A hA).continuous⟩) {y | y.val ∈ V}

lemma persistence_collapse_excision_square
    {X : Type} [TopologicalSpace X] (A : Set X) (hA : IsClosed A)
    (V : Set (Quotient (persistenceCollapseSetoid A))) :
    persistencePuncturedNeighbourhoodPairMap A
        ((Quotient.mk (persistenceCollapseSetoid A)) ⁻¹' V) ≫
      persistenceCollapseEnlargedPairMap A V =
    persistenceCollapsePuncturedPairMap A hA V ≫
      persistencePuncturedNeighbourhoodPairMap
        ((Quotient.mk (persistenceCollapseSetoid A)) '' A) V := by
  apply persistence_pair_hom_ext
  rfl

lemma persistence_collapse_punctured_relative_cohomology_bijective
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A : Set X) (hA : IsClosed A)
    (V : Set (Quotient (persistenceCollapseSetoid A))) (n : ℕ) :
    Function.Bijective
      (relativeCohomologyMap K n (persistenceCollapsePuncturedPairMap A hA V)) := by
  exact persistence_homeomorph_relative_preimage_bijective K _
    (persistenceCollapseComplementHomeomorph A hA).isHomeomorph _ n

lemma persistence_collapse_enlarged_relative_cohomology_bijective
    (K : Type) [Field K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    (A : Set X) (hA : IsClosed A)
    (V : Set (Quotient (persistenceCollapseSetoid A))) (hV : IsOpen V)
    (hAV : (Quotient.mk (persistenceCollapseSetoid A)) '' A ⊆ V) (n : ℕ) :
    Function.Bijective
      (relativeCohomologyMap K n (persistenceCollapseEnlargedPairMap A V)) := by
  have hs := persistence_punctured_neighbourhood_relative_cohomology_bijective K
    hA (hV.preimage continuous_quotient_mk') (fun x hx => hAV ⟨x, hx, rfl⟩) n
  have ht := persistence_punctured_neighbourhood_relative_cohomology_bijective K
    (persistence_collapse_isClosedMap A hA A hA) hV hAV n
  have hm := persistence_collapse_punctured_relative_cohomology_bijective K A hA V n
  have heq := congrArg (relativeCohomologyMap K n)
    (persistence_collapse_excision_square A hA V)
  rw [relativeCohomologyMap_comp, relativeCohomologyMap_comp] at heq
  have hb : Function.Bijective
      ((relativeCohomologyMap K n
        (persistencePuncturedNeighbourhoodPairMap A
          ((Quotient.mk (persistenceCollapseSetoid A)) ⁻¹' V))) ∘
        (relativeCohomologyMap K n (persistenceCollapseEnlargedPairMap A V))) := by
    change Function.Bijective
      ((relativeCohomologyMap K n
        (persistencePuncturedNeighbourhoodPairMap A
          ((Quotient.mk (persistenceCollapseSetoid A)) ⁻¹' V))) ∘ₗ
        (relativeCohomologyMap K n (persistenceCollapseEnlargedPairMap A V)))
    rw [heq]
    exact hm.comp ht
  exact hb.of_comp_left hs.injective

/-- The literal projection from a neighbourhood pair to its quotient image pair. -/
def persistenceCollapseNeighbourhoodPairMap
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    TopPair.ofSubset (X := TopCat.of X) U ⟶
      TopPair.ofSubset (X := TopCat.of (Quotient (persistenceCollapseSetoid A)))
        ((Quotient.mk (persistenceCollapseSetoid A)) '' U) :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨Quotient.mk (persistenceCollapseSetoid A), continuous_quotient_mk'⟩)
    (fun x hx => ⟨x, hx, rfl⟩)

lemma persistence_collapse_neighbourhood_relative_cohomology_bijective
    (K : Type) [Field K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    (A U : Set X) (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) (n : ℕ) :
    Function.Bijective
      (relativeCohomologyMap K n (persistenceCollapseNeighbourhoodPairMap A U)) := by
  let e := persistenceSubsetPairIso (TopCat.of X) U
    ((Quotient.mk (persistenceCollapseSetoid A)) ⁻¹'
      ((Quotient.mk (persistenceCollapseSetoid A)) '' U))
    (persistence_collapse_neighbourhood_preimage A U hAU).symm
  have hmap : persistenceCollapseNeighbourhoodPairMap A U = e.hom ≫
      persistenceCollapseEnlargedPairMap A
        ((Quotient.mk (persistenceCollapseSetoid A)) '' U) := by
    apply persistence_pair_hom_ext
    rfl
  have hbig := persistence_collapse_enlarged_relative_cohomology_bijective K A hA
    ((Quotient.mk (persistenceCollapseSetoid A)) '' U)
    (persistence_collapse_neighbourhood_isOpen A U hAU hU) (Set.image_mono hAU) n
  have hiso : Function.Bijective (relativeCohomologyMap K n e.hom) := by
    have hright := congrArg (relativeCohomologyMap K n) e.hom_inv_id
    have hleft := congrArg (relativeCohomologyMap K n) e.inv_hom_id
    rw [relativeCohomologyMap_comp, relativeCohomologyMap_id] at hright hleft
    have hL : Function.LeftInverse (relativeCohomologyMap K n e.inv)
        (relativeCohomologyMap K n e.hom) := fun u => LinearMap.congr_fun hleft u
    have hR : Function.RightInverse (relativeCohomologyMap K n e.inv)
        (relativeCohomologyMap K n e.hom) := fun u => LinearMap.congr_fun hright u
    exact ⟨hL.injective, hR.surjective⟩
  rw [hmap, relativeCohomologyMap_comp]
  exact hiso.comp hbig

end HodgeLean.Foundations.QuotientDuality
