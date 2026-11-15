import HodgeLean.Foundations.QuotientDuality.RetainedCycleSectionReconstruction
import HodgeLean.Foundations.QuotientDuality.RetainedCycleRelativeCoordinateDetection

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The finite reconstruction of a compact global section retains every actual germ. -/
theorem retained_chain_from_global_section_germ (X : TopCat.{0}) [T2Space X]
    [CompactSpace X] (n : ℕ) (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤)) (x : X) :
    (singularChainSheaf ℚ X n).presheaf.germ ⊤ x (by trivial)
      ((retainedChainSheafSectionMap X ⊤).f n (retainedChainFromGlobalSection X n s)) =
    (singularChainSheaf ℚ X n).presheaf.germ ⊤ x (by trivial) s := by
  obtain ⟨c, hc⟩ := retained_chain_section_germ_representative X ⊤ n s x (by trivial)
  rw [← hc]
  apply (ConcreteCategory.bijective_of_isIso ((singularChainSheafStalkIso ℚ X x).hom.f n)).1
  have hg (a : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) n) :
      (singularChainSheafStalkIso ℚ X x).hom.f n
        ((singularChainSheaf ℚ X n).presheaf.germ ⊤ x (by trivial)
          ((retainedChainSheafSectionMap X ⊤).f n a)) =
      ((relativeChainProjection ℚ (pointComplementPair x)).f n).hom a :=
    ConcreteCategory.congr_hom (retained_chain_sheaf_section_germ X ⊤ x (by trivial) n) a
  change (singularChainSheafStalkIso ℚ X x).hom.f n
    ((singularChainSheaf ℚ X n).presheaf.germ ⊤ x (by trivial)
      ((retainedChainSheafSectionMap X ⊤).f n (retainedChainFromGlobalSection X n s))) =
    (singularChainSheafStalkIso ℚ X x).hom.f n
    ((singularChainSheaf ℚ X n).presheaf.germ ⊤ x (by trivial)
      ((retainedChainSheafSectionMap X ⊤).f n c))
  rw [hg, hg]
  apply sub_eq_zero.mp
  erw [← map_sub]
  apply retained_relative_projection_zero_of_coordinates
  intro σ hσ
  obtain ⟨t, ht⟩ := retained_simplex_hits_point_of_not_from_complement X n x σ hσ
  change retainedSimplexCoordinate (TopCat.toSSet.obj X) n σ
    (retainedChainFromGlobalSection X n s - c) = 0
  rw [map_sub, retained_chain_from_global_section_coordinate]
  apply sub_eq_zero.mpr
  have he := retained_global_section_simplex_coordinate_of_germ X n s c σ t (by rw [ht]; exact hc)
  exact (retained_global_section_coefficient_at X n s σ t).symm.trans he

/-- Actual finite chains reconstruct every global chain-sheaf section on a compact Hausdorff space. -/
theorem retained_chain_from_global_section_section (X : TopCat.{0}) [T2Space X]
    [CompactSpace X] (n : ℕ) (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤)) :
    (retainedChainSheafSectionMap X ⊤).f n (retainedChainFromGlobalSection X n s) = s := by
  apply TopCat.Presheaf.section_ext
  intro x hx
  exact retained_chain_from_global_section_germ X n s x

/-- The actual global chain-to-sections comparison is bijective in every degree on a compact Hausdorff space. -/
theorem retained_global_chain_sheaf_section_bijective (X : TopCat.{0}) [T2Space X]
    [CompactSpace X] (n : ℕ) :
    Function.Bijective ((retainedChainSheafSectionMap X ⊤).f n) :=
  ⟨retained_global_chain_sheaf_section_injective X n,
    fun s => ⟨retainedChainFromGlobalSection X n s, retained_chain_from_global_section_section X n s⟩⟩

end HodgeLean.Foundations.QuotientDuality
