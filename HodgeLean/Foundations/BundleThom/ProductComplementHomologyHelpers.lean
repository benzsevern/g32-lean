import HodgeLean.Foundations.BundleThom.ProductComplementSectionHelpers
import HodgeLean.Foundations.BundleThom.RelativeChainQuasiIsoHelpers

/-! # Actual complement homology splittings for arbitrary bases

The section replaces only the normal coordinate and the splitting is induced by its ambient homotopy.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- The actual complement inclusion has a specified right inverse on rational homology in every degree over every base.
Source: Hatcher, Algebraic Topology, §2.1, homotopy invariance of singular homology. -/
def i1_productComplementHomologySplitEpi {B : Type} [TopologicalSpace B] (k : ℕ)
    (w : Fin k → ℂ) (hw : w ≠ 0) (n : ℕ) :
    SplitEpi (HomologicalComplex.homologyMap
      ((chainPairFunctor ℚ).obj (i1_productNormalPair B k)).hom n) where
  section_ := HomologicalComplex.homologyMap
    (((singularChainComplexFunctor.{0} (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
      (i1_productComplementSection (B := B) k w hw)) n
  id := by
    rw [← HomologicalComplex.homologyMap_comp]
    change HomologicalComplex.homologyMap
      (((singularChainComplexFunctor.{0} (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        (i1_productComplementSection (B := B) k w hw) ≫
      ((singularChainComplexFunctor.{0} (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        (i1_productNormalPair B k).map) n = _
    rw [← CategoryTheory.Functor.map_comp,
      (i1_productComplementSectionHomotopy (B := B) k w hw).congr_homologyMap_singularChainComplexFunctor
        (ModuleCat.of ℚ ℚ) n,
      CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
    rfl

/-- The actual product complement inclusion is surjective on rational homology in every degree over an arbitrary base.
Source: Hatcher, Algebraic Topology, §2.1, the homology splitting of normal contraction. -/
theorem i1_productComplementHomology_epi {B : Type} [TopologicalSpace B] (k : ℕ)
    (w : Fin k → ℂ) (hw : w ≠ 0) (n : ℕ) :
    Epi (HomologicalComplex.homologyMap
      ((chainPairFunctor ℚ).obj (i1_productNormalPair B k)).hom n) :=
  epi_of_epi_fac (i1_productComplementHomologySplitEpi (B := B) k w hw n).id

end HodgeLean.Foundations.BundleThom
