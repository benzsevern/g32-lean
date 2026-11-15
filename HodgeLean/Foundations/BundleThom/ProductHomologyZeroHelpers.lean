import HodgeLean.Foundations.BundleThom.PathConnectedHomologyZeroHelpers

/-! # Degree-zero product projection with a path-connected factor

Fibre inclusions detect the maps even when the base has arbitrary path components.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Projection away from a path-connected factor induces an invertible degree-zero rational homology map.
Source: Hatcher, Algebraic Topology, §2.1, degree-zero homology and path components. -/
def i1_productHomologyZeroIso {B F : Type} [TopologicalSpace B] [TopologicalSpace F]
    [PathConnectedSpace F] (w : F) :
    Homology ℚ (TopCat.of (B × F)) 0 ≅ Homology ℚ (TopCat.of B) 0 := by
  let p : TopCat.of (B × F) ⟶ TopCat.of B := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  let s : TopCat.of B ⟶ TopCat.of (B × F) :=
    TopCat.ofHom ⟨fun b => (b, w), continuous_id.prodMk continuous_const⟩
  let H := fun {X Y : TopCat} (f : X ⟶ Y) =>
    HomologicalComplex.homologyMap (singularChainComplexMap ℚ f) 0
  have comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
      H (f ≫ g) = H f ≫ H g := by
    dsimp [H, singularChainComplexMap]
    rw [Functor.map_comp, HomologicalComplex.homologyMap_comp]
  have hs : H s ≫ H p = 𝟙 _ := by
    rw [← comp]
    change HomologicalComplex.homologyMap (singularChainComplexMap ℚ (𝟙 (TopCat.of B))) 0 = _
    simp only [singularChainComplexMap]
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  have hp : H p ≫ H s = 𝟙 _ := by
    rw [← comp]
    let i : ∀ _ : B, TopCat.of F ⟶ TopCat.of (B × F) := fun b =>
      TopCat.ofHom ⟨fun v => (b, v), continuous_const.prodMk continuous_id⟩
    apply i1_homologyZero_hom_ext_of_cover (fun _ : B => TopCat.of F) i
      (fun x => ⟨x.1, x.2, rfl⟩)
    intro b
    change H (i b) ≫ H (p ≫ s) = H (i b) ≫ 𝟙 _
    rw [← comp, Category.comp_id]
    let c : TopCat.of F ⟶ TopCat.of F := TopCat.ofHom (ContinuousMap.const F w)
    have hi : i b ≫ (p ≫ s) = c ≫ i b := rfl
    rw [hi, comp]
    dsimp only [H]
    rw [i1_homologyZero_map_eq_of_pathConnectedTarget c (𝟙 _)]
    simp only [H, singularChainComplexMap]
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id, Category.id_comp]
  exact ⟨H p, H s, hp, hs⟩

end HodgeLean.Foundations.BundleThom
