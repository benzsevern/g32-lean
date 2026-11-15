import HodgeLean.Foundations.BundleThom.SubcomplexProjectionUnionHelpers
import HodgeLean.Foundations.BundleThom.SingularSubsetIntersectionHelpers

/-! # Actual subset chain coordinates for base projections

HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

private local instance (X : TopCat) (U : Set X) : Mono (topologicalSubsetInclusion X U) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective
private local instance (X : TopCat) (U : Set X) :
    Mono (TopCat.toSSet.map (topologicalSubsetInclusion X U)) := by apply Functor.map_mono

/-- Chains on an actual topological subset identify with the chains of its singular range.
Source: Hatcher, Algebraic Topology, §2.1, actual singular chains of subspaces. -/
def i1_subsetSingularChainIso (X : TopCat) (U : Set X) :
    (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).obj (TopCat.of U)) ≅
      SSet.chainComplex (i1_singularSubsetRange X U) (ModuleCat.of ℚ ℚ) :=
  ((SSet.chainComplexFunctor.{0,0,1} (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).mapIso
    (asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map (topologicalSubsetInclusion X U))))

/-- The actual subset chain identification respects every supplied ambient projection.
Source: Hatcher, Algebraic Topology, §2.1, functoriality of subspace chains. -/
theorem i1_subsetSingularChainIso_comp_projection (X Y : TopCat) (p : X ⟶ Y)
    (U : Set X) :
    (i1_subsetSingularChainIso X U).hom ≫
      i1_subcomplexChainProjection (TopCat.toSSet.map p) (i1_singularSubsetRange X U) =
    (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
      (topologicalSubsetInclusion X U ≫ p)) := by
  let F : SSet ⥤ ChainComplex (ModuleCat ℚ) ℕ :=
    (SSet.chainComplexFunctor.{0,0,1} (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map (SSet.Subcomplex.toRange (TopCat.toSSet.map (topologicalSubsetInclusion X U))) ≫
    F.map ((i1_singularSubsetRange X U).ι ≫ TopCat.toSSet.map p) =
    F.map (TopCat.toSSet.map (topologicalSubsetInclusion X U ≫ p))
  rw [TopCat.toSSet.map_comp, ← F.map_comp]
  rfl

/-- The singular-range projection is a quasi-isomorphism exactly when the actual subset projection is.
Source: Hatcher, Algebraic Topology, §2.1, invariance under chain coordinates. -/
theorem i1_subsetChainProjection_quasiIso_iff (X Y : TopCat) (p : X ⟶ Y)
    (U : Set X) :
    QuasiIso (i1_subcomplexChainProjection (TopCat.toSSet.map p) (i1_singularSubsetRange X U)) ↔
    QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
      (topologicalSubsetInclusion X U ≫ p)) := by
  rw [← i1_subsetSingularChainIso_comp_projection]
  exact (quasiIso_iff_comp_left (i1_subsetSingularChainIso X U).hom _).symm

/-- Projection surjectivity on rational homology is retained by the actual subset chain coordinates.
Source: Hatcher, Algebraic Topology, §2.1, invariance under chain coordinates. -/
theorem i1_subsetChainProjection_homology_epi_iff (X Y : TopCat) (p : X ⟶ Y)
    (U : Set X) (n : ℕ) :
    Epi (HomologicalComplex.homologyMap
      (i1_subcomplexChainProjection (TopCat.toSSet.map p) (i1_singularSubsetRange X U)) n) ↔
    Epi (HomologicalComplex.homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        (topologicalSubsetInclusion X U ≫ p)) n) := by
  rw [← i1_subsetSingularChainIso_comp_projection, HomologicalComplex.homologyMap_comp]
  exact (epi_comp_iff_of_epi _ _).symm

/-- Projection invertibility on rational homology is retained by the actual subset chain coordinates.
Source: Hatcher, Algebraic Topology, §2.1, invariance under chain coordinates. -/
theorem i1_subsetChainProjection_homology_isIso_iff (X Y : TopCat) (p : X ⟶ Y)
    (U : Set X) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (i1_subcomplexChainProjection (TopCat.toSSet.map p) (i1_singularSubsetRange X U)) n) ↔
    IsIso (HomologicalComplex.homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        (topologicalSubsetInclusion X U ≫ p)) n) := by
  rw [← i1_subsetSingularChainIso_comp_projection, HomologicalComplex.homologyMap_comp]
  exact (isIso_comp_left_iff _ _).symm

end HodgeLean.Foundations.BundleThom
