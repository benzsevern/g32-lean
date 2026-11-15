import HodgeLean.Foundations.Singular.ProductHomotopyStage

/-! Naturality of the actual product-chain homotopy obstruction. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- The actual next obstruction map for a degree-raising product-chain stage.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction of chain homotopies. -/
def ProductHomotopyStage.obstruction
    {F G : ∀ X Y : TopCat.{0}, rationalProductChains X Y ⟶ rationalProductChains X Y}
    {n : ℕ} (H : ProductHomotopyStage F G n) (X Y : TopCat.{0}) :
    (rationalProductChains X Y).X (n + 1) →ₗ[ℚ] (rationalProductChains X Y).X (n + 1) :=
  ((F X Y).f (n + 1)).hom - ((G X Y).f (n + 1)).hom -
    (H.hom X Y).comp ((rationalProductChains X Y).d (n + 1) n).hom

/-- The actual next obstruction map is natural whenever the two chain endomaps are natural.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction of chain homotopies. -/
theorem ProductHomotopyStage.obstruction_naturality
    {F G : ∀ X Y : TopCat.{0}, rationalProductChains X Y ⟶ rationalProductChains X Y}
    (hF : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalProductChainMap f g ≫ F X' Y' = F X Y ≫ rationalProductChainMap f g)
    (hG : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalProductChainMap f g ≫ G X' Y' = G X Y ≫ rationalProductChainMap f g)
    {n : ℕ} (H : ProductHomotopyStage F G n)
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (H.obstruction X' Y').comp ((rationalProductChainMap f g).f (n + 1)).hom =
      (((rationalProductChainMap f g).f (n + 1)).hom).comp (H.obstruction X Y) := by
  apply LinearMap.ext
  intro z
  have hf := congrArg (fun k => (k.f (n + 1)).hom z) (hF f g)
  have hg := congrArg (fun k => (k.f (n + 1)).hom z) (hG f g)
  have hh := LinearMap.congr_fun (H.naturality f g)
    (((rationalProductChains X Y).d (n + 1) n).hom z)
  change ((F X' Y').f (n + 1)).hom (((rationalProductChainMap f g).f (n + 1)).hom z) =
    ((rationalProductChainMap f g).f (n + 1)).hom (((F X Y).f (n + 1)).hom z) at hf
  change ((G X' Y').f (n + 1)).hom (((rationalProductChainMap f g).f (n + 1)).hom z) =
    ((rationalProductChainMap f g).f (n + 1)).hom (((G X Y).f (n + 1)).hom z) at hg
  dsimp only [obstruction, LinearMap.comp_apply, LinearMap.sub_apply]
  rw [map_sub, map_sub, hf, hg, rationalChainMap_boundary]
  exact congrArg (fun t => _ - t) hh

#print axioms ProductHomotopyStage.obstruction
#print axioms ProductHomotopyStage.obstruction_naturality
end HodgeLean.Foundations.Singular
