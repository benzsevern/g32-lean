import HodgeLean.Foundations.BundleThom.ContractibleFactorProjectionHelpers

/-! # Homology surjectivity of actual product projections

A specified point of the second factor supplies a section in every degree.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Every first projection with a specified fiber point is surjective on rational homology in every degree.
Source: Hatcher, Algebraic Topology, §2.1, functoriality and split projections. -/
theorem i1_productProjection_homology_epi (B Y : Type) [TopologicalSpace B]
    [TopologicalSpace Y] (y : Y) (n : ℕ) :
    Epi (HomologicalComplex.homologyMap
      ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ))).map
        (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : ContinuousMap (B × Y) B))) n) := by
  let F := ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n
  let p : TopCat.of (B × Y) ⟶ TopCat.of B := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  let s : TopCat.of B ⟶ TopCat.of (B × Y) :=
    TopCat.ofHom ⟨fun b => (b, y), continuous_id.prodMk continuous_const⟩
  have he : s ≫ p = 𝟙 (TopCat.of B) := rfl
  have hf : F.map s ≫ F.map p = 𝟙 _ := by
    rw [← F.map_comp, he, F.map_id]
  change Epi (F.map p)
  exact epi_of_epi_fac hf

end HodgeLean.Foundations.BundleThom
