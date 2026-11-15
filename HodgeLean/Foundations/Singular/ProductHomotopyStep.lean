import HodgeLean.Foundations.Singular.ProductHomotopyObstruction
import HodgeLean.Foundations.Singular.ProductSelfBoundary

/-! The recursive extension of actual natural product-chain-chain homotopy maps. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- The next actual degree-raising map obtained by extending chosen universal model fillers.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
def ProductHomotopyStage.nextHom
    {F G : ∀ X Y : TopCat.{0}, rationalProductChains X Y ⟶ rationalProductChains X Y}
    {n : ℕ} (H : ProductHomotopyStage F G n) (X Y : TopCat.{0}) :
    (rationalProductChains X Y).X (n + 1) →ₗ[ℚ] (rationalProductChains X Y).X (n + 2) :=
  productSelfModelExtension X Y (n + 1) (n + 2)
    (Classical.choose H.model_filler)

/-- Extending the chosen model fillers gives the full next chain-homotopy boundary equation.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
theorem ProductHomotopyStage.nextHom_boundary
    {F G : ∀ X Y : TopCat.{0}, rationalProductChains X Y ⟶ rationalProductChains X Y}
    (hF : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalProductChainMap f g ≫ F X' Y' = F X Y ≫ rationalProductChainMap f g)
    (hG : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalProductChainMap f g ≫ G X' Y' = G X Y ≫ rationalProductChainMap f g)
    {n : ℕ} (H : ProductHomotopyStage F G n) (X Y : TopCat.{0}) :
    (((rationalProductChains X Y).d (n + 2) (n + 1)).hom).comp (H.nextHom X Y) =
      H.obstruction X Y := by
  exact productSelfModelExtension_boundary (n + 1) (n + 1) H.obstruction
    (H.obstruction_naturality hF hG)
    (Classical.choose H.model_filler)
    (Classical.choose_spec H.model_filler) X Y

/-- The model-filler extension supplies the next natural product-chain homotopy stage.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
def ProductHomotopyStage.extend
    {F G : ∀ X Y : TopCat.{0}, rationalProductChains X Y ⟶ rationalProductChains X Y}
    (hF : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalProductChainMap f g ≫ F X' Y' = F X Y ≫ rationalProductChainMap f g)
    (hG : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalProductChainMap f g ≫ G X' Y' = G X Y ≫ rationalProductChainMap f g)
    {n : ℕ} (H : ProductHomotopyStage F G n) : ProductHomotopyStage F G (n + 1) where
  hom := H.nextHom
  naturality f g := productSelfModelExtension_naturality f g (n + 1) (n + 2) _
  cycles X Y z hz := by
    have hz' : ((rationalProductChains X Y).d (n + 1) n).hom z = 0 := by simpa using hz
    have hb := LinearMap.congr_fun (H.nextHom_boundary hF hG X Y) z
    change ((rationalProductChains X Y).d (n + 2) (n + 1)).hom (H.nextHom X Y z) =
      ((F X Y).f (n + 1)).hom z - ((G X Y).f (n + 1)).hom z -
        H.hom X Y (((rationalProductChains X Y).d (n + 1) n).hom z) at hb
    simpa only [hz', map_zero, sub_zero] using hb

#print axioms ProductHomotopyStage.extend
#print axioms ProductHomotopyStage.nextHom
#print axioms ProductHomotopyStage.nextHom_boundary
end HodgeLean.Foundations.Singular
