import HodgeLean.Foundations.QuotientDuality.PersistenceGoodPairComparison

/-! Empty inverse-image loci in the actual closed-map comparison. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_empty_preimage_locus_isOpen
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hclosed : IsClosedMap f) (A : Set Y)
    (hfibre : ∀ y, y ∉ A → ∃! x, f x = y) (hB : f ⁻¹' A = ∅) : IsOpen A := by
  have hrange : Set.range f = Aᶜ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩ hx
      have hx' : x ∈ f ⁻¹' A := hx
      rw [hB] at hx'
      exact hx'
    · intro hy
      obtain ⟨x, hx, _⟩ := hfibre y hy
      exact ⟨x, hx⟩
  have hrc : IsClosed (Set.range f) := by
    simpa only [Set.image_univ] using hclosed Set.univ isClosed_univ
  rw [hrange] at hrc
  simpa only [compl_compl] using hrc.isOpen_compl

/-- The literal ambient map with codomain restricted to the locus complement. -/
def persistenceEmptyPreimageComplementMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set Y) (hB : f ⁻¹' A = ∅) : C(X, ↥(Aᶜ : Set Y)) :=
  ⟨fun x => ⟨f x, by
    intro hx
    have hx' : x ∈ f ⁻¹' A := hx
    rw [hB] at hx'
    exact hx'⟩, f.continuous.subtype_mk _⟩

lemma persistence_empty_preimage_complement_isHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hclosed : IsClosedMap f) (A : Set Y)
    (hfibre : ∀ y, y ∉ A → ∃! x, f x = y) (hB : f ⁻¹' A = ∅) :
    IsHomeomorph (persistenceEmptyPreimageComplementMap f A hB) := by
  apply isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
  refine ⟨(persistenceEmptyPreimageComplementMap f A hB).continuous,
    hclosed.codRestrict _, ?_, ?_⟩
  · intro x y heq
    have hxy : f x = f y := congrArg Subtype.val heq
    obtain ⟨z, _, hu⟩ := hfibre (f x) (persistenceEmptyPreimageComplementMap f A hB x).property
    exact (hu x rfl).trans (hu y hxy.symm).symm
  · intro y
    obtain ⟨x, hx, _⟩ := hfibre y.val y.property
    exact ⟨x, Subtype.ext hx⟩

lemma persistence_empty_preimage_relative_cohomology_bijective
    (K : Type) [Field K] [Algebra ℚ K]
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hclosed : IsClosedMap f) (A : Set Y) (hA : IsClosed A)
    (hfibre : ∀ y, y ∉ A → ∃! x, f x = y) (hB : f ⁻¹' A = ∅) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n (persistencePairMap (TopCat.ofHom f) A)) := by
  let g := TopCat.ofHom (persistenceEmptyPreimageComplementMap f A hB)
  have hfactor : persistencePairMap (TopCat.ofHom f) A =
      persistencePairMap g {y | y.val ∈ A} ≫
        persistencePuncturedNeighbourhoodPairMap A A := by
    apply persistence_pair_hom_ext
    rfl
  have hleft := persistence_homeomorph_relative_preimage_bijective K g
    (persistence_empty_preimage_complement_isHomeomorph f hclosed A hfibre hB)
    {y | y.val ∈ A} n
  have hright := persistence_punctured_neighbourhood_relative_cohomology_bijective K hA
    (persistence_empty_preimage_locus_isOpen f hclosed A hfibre hB) (Set.Subset.refl A) n
  rw [hfactor, relativeCohomologyMap_comp]
  exact hleft.comp hright

end HodgeLean.Foundations.QuotientDuality
