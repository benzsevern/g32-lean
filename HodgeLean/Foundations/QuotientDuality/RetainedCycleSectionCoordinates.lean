import HodgeLean.Foundations.QuotientDuality.RetainedCycleLocalChainSections
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual coefficient of a global chain-sheaf section along a specified simplex point. -/
def retainedGlobalSectionSimplexCoordinate (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤))
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (t : SimplexCategory.toTop.{0}.obj ⦋n⦌) : ℚ :=
  let x := retainedSimplexAt X n σ t
  retainedRelativeSimplexCoordinate (pointComplementPair x) n σ
    (retained_simplex_not_from_point_complement X n σ t)
    ((singularChainSheafStalkIso ℚ X x).hom.f n
      ((singularChainSheaf ℚ X n).presheaf.germ ⊤ x (by trivial) s))

/-- On an actual chain section the pointwise coefficient is its original literal simplex coefficient. -/
theorem retained_global_section_simplex_coordinate_chain (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) n)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (t : SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    retainedGlobalSectionSimplexCoordinate X n ((retainedChainSheafSectionMap X ⊤).f n c) σ t =
      retainedSimplexCoordinate (TopCat.toSSet.obj X) n σ c := by
  let x := retainedSimplexAt X n σ t
  let hσ := retained_simplex_not_from_point_complement X n σ t
  have hg := ConcreteCategory.congr_hom
    (retained_chain_sheaf_section_germ X ⊤ x (by trivial) n) c
  change (singularChainSheafStalkIso ℚ X x).hom.f n
      ((singularChainSheaf ℚ X n).presheaf.germ ⊤ x (by trivial)
        ((retainedChainSheafSectionMap X ⊤).f n c)) =
    ((relativeChainProjection ℚ (pointComplementPair x)).f n).hom c at hg
  change retainedRelativeSimplexCoordinate (pointComplementPair x) n σ hσ
    ((singularChainSheafStalkIso ℚ X x).hom.f n
      ((singularChainSheaf ℚ X n).presheaf.germ ⊤ x (by trivial)
        ((retainedChainSheafSectionMap X ⊤).f n c))) = _
  rw [hg]
  exact ConcreteCategory.congr_hom (retained_relative_simplex_coordinate_projection
    (pointComplementPair x) n σ hσ) c

/-- An actual germ representative computes the section coefficient at the specified simplex point. -/
theorem retained_global_section_simplex_coordinate_of_germ (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤))
    (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) n)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (t : SimplexCategory.toTop.{0}.obj ⦋n⦌)
    (h : (singularChainSheaf ℚ X n).presheaf.germ ⊤ (retainedSimplexAt X n σ t) (by trivial)
        ((retainedChainSheafSectionMap X ⊤).f n c) =
      (singularChainSheaf ℚ X n).presheaf.germ ⊤ (retainedSimplexAt X n σ t) (by trivial) s) :
    retainedGlobalSectionSimplexCoordinate X n s σ t =
      retainedSimplexCoordinate (TopCat.toSSet.obj X) n σ c := by
  have he := congrArg (fun z => retainedRelativeSimplexCoordinate
    (pointComplementPair (retainedSimplexAt X n σ t)) n σ
    (retained_simplex_not_from_point_complement X n σ t)
    ((singularChainSheafStalkIso ℚ X (retainedSimplexAt X n σ t)).hom.f n z)) h
  change retainedGlobalSectionSimplexCoordinate X n ((retainedChainSheafSectionMap X ⊤).f n c) σ t =
    retainedGlobalSectionSimplexCoordinate X n s σ t at he
  rw [retained_global_section_simplex_coordinate_chain] at he
  exact he.symm

/-- Actual global section coefficients are locally constant on each singular simplex domain. -/
theorem retained_global_section_simplex_coordinate_locally_constant
    (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤))
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    IsLocallyConstant (retainedGlobalSectionSimplexCoordinate X n s σ) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro t
  obtain ⟨V, hV, ht, c, hc⟩ := retained_chain_section_local_representative X ⊤ n s
    (retainedSimplexAt X n σ t) (by trivial)
  let f : C(SimplexCategory.toTop.{0}.obj ⦋n⦌, X) :=
    TopCat.Hom.hom (show SimplexCategory.toTop.{0}.obj ⦋n⦌ ⟶ X from σ.down)
  refine ⟨f ⁻¹' (V : Set X), V.isOpen.preimage f.continuous, ht, ?_⟩
  intro t' ht'
  have h₁ := retained_global_section_simplex_coordinate_of_germ X n s c σ t' (hc _ ht')
  have h₂ := retained_global_section_simplex_coordinate_of_germ X n s c σ t (hc _ ht)
  exact h₁.trans h₂.symm

/-- A global section has one constant coefficient on each actual singular simplex. -/
theorem retained_global_section_simplex_coordinate_constant
    (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤))
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (t t' : SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    retainedGlobalSectionSimplexCoordinate X n s σ t =
      retainedGlobalSectionSimplexCoordinate X n s σ t' :=
  (retained_global_section_simplex_coordinate_locally_constant X n s σ).apply_eq_of_preconnectedSpace t t'

/-- The constant actual coefficient attached to a simplex by a global chain-sheaf section. -/
def retainedGlobalSectionCoefficient (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤))
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) : ℚ :=
  retainedGlobalSectionSimplexCoordinate X n s σ (Classical.choice inferInstance)

/-- Every actual simplex point computes the constant coefficient of the global section. -/
theorem retained_global_section_coefficient_at (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤))
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (t : SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    retainedGlobalSectionSimplexCoordinate X n s σ t = retainedGlobalSectionCoefficient X n s σ :=
  retained_global_section_simplex_coordinate_constant X n s σ t _

end HodgeLean.Foundations.QuotientDuality
