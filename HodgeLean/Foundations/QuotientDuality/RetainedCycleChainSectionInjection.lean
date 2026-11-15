import HodgeLean.Foundations.QuotientDuality.RetainedCyclePointChainDetection
import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapStalk

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- A germ of the actual chain section comparison is the literal point-complement chain projection. -/
theorem retained_chain_sheaf_section_germ (X : TopCat.{0}) [T2Space X]
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    (retainedChainSheafSectionMap X U).f n ≫
      (singularChainSheaf ℚ X n).presheaf.germ U x hx ≫
        (singularChainSheafStalkIso ℚ X x).hom.f n =
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).map ((relativeChainProjection ℚ (pointComplementPair x)).f n) := by
  rw [retained_chain_sheaf_section_component]
  simp only [Category.assoc]
  erw [← TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    retained_sheafification_stalk_chain_comparison, singularChainPresheafStalkIso_germ]
  rw [← Functor.map_comp]
  have hn := congrArg (fun f => f.f n)
    (relativeChainProjection_supportInclusion ℚ X (Set.singleton_subset_iff.mpr hx))
  exact congrArg ((forget₂ (ModuleCat ℚ) AddCommGrpCat).map) hn

/-- The actual global singular-chain section comparison is injective in every degree. -/
theorem retained_global_chain_sheaf_section_injective (X : TopCat.{0}) [T2Space X] (n : ℕ) :
    Function.Injective ((retainedChainSheafSectionMap X ⊤).f n) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply retained_chain_eq_zero_of_point_projections X n (a - b)
  intro x
  have h0 : (retainedChainSheafSectionMap X ⊤).f n (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hg := ConcreteCategory.congr_hom
    (retained_chain_sheaf_section_germ X ⊤ x (by trivial) n) (a - b)
  change (singularChainSheafStalkIso ℚ X x).hom.f n
      ((singularChainSheaf ℚ X n).presheaf.germ ⊤ x (by trivial)
        ((retainedChainSheafSectionMap X ⊤).f n (a - b))) =
    ((relativeChainProjection ℚ (pointComplementPair x)).f n).hom (a - b) at hg
  rw [h0, map_zero, map_zero] at hg
  exact hg.symm

/-- The actual global chain-to-sections comparison is a monomorphism of chain complexes. -/
theorem retained_global_chain_sheaf_section_mono (X : TopCat.{0}) [T2Space X] :
    Mono (retainedChainSheafSectionMap X ⊤) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact ConcreteCategory.mono_of_injective _ (retained_global_chain_sheaf_section_injective X n)

end HodgeLean.Foundations.QuotientDuality
