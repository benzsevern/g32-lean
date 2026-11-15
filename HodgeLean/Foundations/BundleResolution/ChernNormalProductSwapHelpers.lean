import HodgeLean.Foundations.BundleResolution.ChernRelativeProductPairHelpers
import HodgeLean.Foundations.BundleThom.ProductMatrixPairHelpers

/-! # Actual normal product pair coordinate interchange

Interchanging the two coordinates identifies the fibre-first relative
product with the fixed base-first normal pair used by bundle charts.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

def i1_normalProductPairSwap (k : ℕ) (Y : TopCat) :
    i1_relativeProductPair (puncturedPair ℂ k) Y ≅ i1_productNormalPair Y k where
  hom := TopPair.ofHom (TopCat.ofHom ⟨Prod.swap, continuous_swap⟩)
    (TopCat.ofHom
      ⟨fun p : {w : Fin k → ℂ // w ≠ 0} × Y => ⟨(p.2, p.1.val), p.1.property⟩,
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)).subtype_mk _⟩)
    (by ext p; rfl)
  inv := TopPair.ofHom (TopCat.ofHom ⟨Prod.swap, continuous_swap⟩)
    (TopCat.ofHom
      ⟨fun p : {p : Y × (Fin k → ℂ) // p.2 ≠ 0} => (⟨p.val.2, p.property⟩, p.val.1),
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _).prodMk
          (continuous_fst.comp continuous_subtype_val)⟩)
    (by ext p; rfl)
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext p
      rfl
    · ext p
      rfl
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext p
      rfl
    · ext p
      rfl

theorem i1_normalProductPairSwap_comp_projection (k : ℕ) (Y : TopCat) :
    (i1_normalProductPairSwap k Y).hom ≫ i1_productNormalProjection Y k =
      i1_relativeProductFirst (puncturedPair ℂ k) Y := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

theorem i1_normalProductPairSwap_comp_base (k : ℕ) (Y : TopCat) :
    TopPair.Hom.fst (i1_normalProductPairSwap k Y).hom ≫
        productFirst Y (TopCat.of (Fin k → ℂ)) =
      productSecond (puncturedPair ℂ k).fst Y := by
  ext p
  rfl

end HodgeLean.Foundations.BundleResolution
