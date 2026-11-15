import HodgeLean.Foundations.QuotientDuality.LocalSupportedCoefficients

/-! Open loci on which a supported class realizes the specified local generators. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem supported_generator_locus_isOpen (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n) (U : Opens X)
    (w : RelativeHomology ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ) n) :
    IsOpen {x : X | ∃ hx : x ∈ U, relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) w = o.generator x} := by
  obtain ⟨f, hf, hw⟩ := relative_open_coefficients X n o U w
  have heq : {x : X | ∃ hx : x ∈ U, relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) w = o.generator x} =
      Subtype.val '' {x : U | f x = 1} := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      apply (o.generates x).1
      change f ⟨x, hx⟩ • o.generator x = (1 : ℚ) • o.generator x
      rw [one_smul, ← hw ⟨x, hx⟩]
      exact h
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      rw [hw y, hy, one_smul]
  rw [heq]
  exact (U.isOpen.isOpenMap_subtype_val) _ (hf.isOpen_fiber 1)

#print axioms supported_generator_locus_isOpen
end HodgeLean.Foundations.QuotientDuality
