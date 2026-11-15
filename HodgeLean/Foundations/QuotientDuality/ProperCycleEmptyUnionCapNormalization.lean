import HodgeLean.Foundations.QuotientDuality.ProperCycleEmptyTriadNormalization
import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionRelativeCapNaturality

/-! # Actual empty-triad normalization in union-relative coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original empty-triad source comparison followed by literal union inclusion is the actual triad-to-union map.
Source: properCycle_empty_triad_relative_projection; triadRelativeChainProjection_triadToUnionRelativeChainMap.
HC no distance; AV milestone no distance. -/
theorem properCycle_empty_triad_union_comparison (X : TopCat.{0}) (A : Set X) :
    (properCycle_empty_triad_relative_iso X A).hom ≫
      (relativeChainFunctor ℚ).map (TopPair.ofSubsetHom (𝟙 X)
        (show A ⊆ A ∪ (∅ : Set X) from Set.subset_union_left)) =
      triadToUnionRelativeChainMap ℚ X A ∅ := by
  letI : Epi (triadRelativeChainProjection ℚ X A ∅) := by
    change Epi (cokernel.π _)
    infer_instance
  apply (cancel_epi (triadRelativeChainProjection ℚ X A ∅)).mp
  rw [← Category.assoc, properCycle_empty_triad_relative_projection,
    TopPair.Homotopy.relativeChainProjection_naturality,
    triadRelativeChainProjection_triadToUnionRelativeChainMap]
  change (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
    (𝟙 X)) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Actual union-relative inclusion of a specified relative class has precisely its original empty-triad inverse source class under excision.
Source: properCycle_empty_triad_union_comparison; original relative homology functoriality.
HC no distance; AV milestone no distance. -/
theorem properCycle_empty_triad_union_class (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := X) A) n) :
    let F := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
      (properCycle_empty_triad_relative_iso X A)
    triadToUnionRelativeHomologyMap ℚ X A ∅ n (F.inv.hom z) =
      relativeHomologyMap ℚ n (TopPair.ofSubsetHom (𝟙 X)
        (show A ⊆ A ∪ (∅ : Set X) from Set.subset_union_left)) z := by
  let F := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
    (properCycle_empty_triad_relative_iso X A)
  have h := congrArg (fun m => HomologicalComplex.homologyMap m n)
    (properCycle_empty_triad_union_comparison X A)
  rw [HomologicalComplex.homologyMap_comp] at h
  have he := ConcreteCategory.congr_hom h (F.inv.hom z)
  change relativeHomologyMap ℚ n (TopPair.ofSubsetHom (𝟙 X)
      (show A ⊆ A ∪ (∅ : Set X) from Set.subset_union_left)) (F.hom.hom (F.inv.hom z)) =
    triadToUnionRelativeHomologyMap ℚ X A ∅ n (F.inv.hom z) at he
  rw [show F.hom.hom (F.inv.hom z) = z from ConcreteCategory.congr_hom F.inv_hom_id z] at he
  exact he.symm

/-- The original union-relative normal cap has unit evaluation one on the specified normal orientation, using only the actual identity union inclusion and empty-relative target projection.
Source: Hatcher, Algebraic Topology, section 3.3; properCycle_empty_triad_union_class; properCycle_empty_triad_normalized_cap_unit.
HC no distance; AV milestone no distance. -/
theorem properCycle_empty_union_normalized_cap_unit
    (X : TopCat.{0}) (A : Set X) (hA : IsOpen A) (p : ℕ) (hp : Even p)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := X) A) p) (hz : z ≠ 0) :
    letI := properCycle_empty_relative_projection_isIso X
    let G := HomologicalComplex.homologyMap
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (∅ : Set X))) 0
    cohomologyEquivDualHomology ℚ X 0 (unit (R := ℚ) X)
      ((inv G).hom (unionRelativeTriadCapCohomologyLinear ℚ X A ∅ p 0
        (triadToUnionRelativeChainMap_quasiIso_of_isOpen X A ∅ hA isOpen_empty)
        (normalizedRelativeCoclass z hz)
        (relativeHomologyMap ℚ p (TopPair.ofSubsetHom (𝟙 X)
          (show A ⊆ A ∪ (∅ : Set X) from Set.subset_union_left)) z))) = 1 := by
  letI := properCycle_empty_relative_projection_isIso X
  dsimp only
  rw [← properCycle_empty_triad_union_class X A p z]
  erw [unionRelativeTriadCapCohomologyLinear_on_comparison ℚ X A ∅ p 0]
  exact properCycle_empty_triad_normalized_cap_unit X A p hp z hz

end HodgeLean.Foundations.QuotientDuality
