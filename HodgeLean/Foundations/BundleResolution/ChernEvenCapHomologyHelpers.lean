import HodgeLean.Foundations.BundleResolution.ChernEvenCapChainHelpers
import HodgeLean.Foundations.BundleResolution.ChernExtendedHomologyComparisonHelpers

/-! # Actual cap homology from the integer-indexed comparison

The extension homology isomorphisms identify the full cap chain comparison
with the existing relative cap map in every target degree.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_evenRelativeCapExtendedChainMap_homology (P : TopPair) (k n : ℕ)
    (φ : RelativeCochain ℚ P (2 * k)) (hφ : relativeCoboundary ℚ P (2 * k) φ = 0) :
    let K := (relativeChainFunctor ℚ).obj P
    let L := ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj P.fst
    (K.extendHomologyIso (ComplexShape.embeddingUpIntLE (2 * k : ℕ))
      (show (ComplexShape.embeddingUpIntLE (2 * k : ℕ)).f (2 * k + n) = -(n : ℤ) by
        simp only [ComplexShape.embeddingUpIntLE_f]; omega)).inv ≫
      homologyMap (i1_evenRelativeCapExtendedChainMap P k φ hφ) (-(n : ℤ)) ≫
      (L.extendHomologyIso (ComplexShape.embeddingUpIntLE 0)
        (show (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) by
          simp only [ComplexShape.embeddingUpIntLE_f]; omega)).hom =
      ShortComplex.homologyMap (relativeCapShortComplexHom ℚ P (2 * k) n φ hφ) := by
  dsimp only
  apply i1_extendedHomologyMap_of_middle
  change _ ≫ i1_degreeLoweringExtendedComponent _ _ (2 * k)
    (fun n => relativeCapHom ℚ P (2 * k) n φ) (-(n : ℤ)) ≫ _ = _
  rw [i1_degreeLoweringExtendedComponent_neg, relativeCapShortComplexHom_τ₂]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end HodgeLean.Foundations.BundleResolution
