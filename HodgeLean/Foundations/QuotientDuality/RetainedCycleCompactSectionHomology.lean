import HodgeLean.Foundations.QuotientDuality.RetainedCycleCompactSectionComparison

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal chain-to-sections map on a compact Hausdorff space is an isomorphism of complexes. -/
theorem retained_global_chain_sheaf_section_isIso (X : TopCat.{0}) [T2Space X]
    [CompactSpace X] : IsIso (retainedChainSheafSectionMap X ⊤) := by
  haveI (n : ℕ) : IsIso ((retainedChainSheafSectionMap X ⊤).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (retained_global_chain_sheaf_section_bijective X n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Actual singular homology is isomorphic to homology of global chain-sheaf sections on a compact Hausdorff space. -/
theorem retained_global_chain_sheaf_section_homology_isIso (X : TopCat.{0}) [T2Space X]
    [CompactSpace X] (n : ℕ) : IsIso (retainedChainSheafSectionHomologyMap X ⊤ n) := by
  have := retained_global_chain_sheaf_section_isIso X
  unfold retainedChainSheafSectionHomologyMap
  infer_instance

/-- The actual global chain-sheaf section comparison induces a bijection on singular homology. -/
theorem retained_global_chain_sheaf_section_homology_bijective (X : TopCat.{0}) [T2Space X]
    [CompactSpace X] (n : ℕ) :
    Function.Bijective (retainedChainSheafSectionHomologyMap X ⊤ n) := by
  have := retained_global_chain_sheaf_section_homology_isIso X n
  exact ConcreteCategory.bijective_of_isIso _

end HodgeLean.Foundations.QuotientDuality
