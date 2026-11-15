import HodgeLean.Foundations.Singular.ProductHomotopyStep

/-! Assembly of actual natural product-chain-chain homotopies degree by degree. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Singular

/-- Equal degree-zero chain maps have the zero degree-raising product-chain stage.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
def productHomotopyStageZero
    (F G : ∀ X Y : TopCat.{0}, rationalProductChains X Y ⟶ rationalProductChains X Y)
    (h₀ : ∀ X Y : TopCat.{0}, (F X Y).f 0 = (G X Y).f 0) : ProductHomotopyStage F G 0 where
  hom X Y := 0
  naturality f g := by
    ext z
    simp
  cycles X Y z hz := by
    change ((rationalProductChains X Y).d 1 0).hom 0 =
      ((F X Y).f 0).hom z - ((G X Y).f 0).hom z
    rw [map_zero, h₀ X Y, sub_self]

/-- The recursive actual product-chain homotopy stages for two natural chain endomaps equal on vertices.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
def productHomotopyStages
    (F G : ∀ X Y : TopCat.{0}, rationalProductChains X Y ⟶ rationalProductChains X Y)
    (hF : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalProductChainMap f g ≫ F X' Y' = F X Y ≫ rationalProductChainMap f g)
    (hG : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalProductChainMap f g ≫ G X' Y' = G X Y ≫ rationalProductChainMap f g)
    (h₀ : ∀ X Y : TopCat.{0}, (F X Y).f 0 = (G X Y).f 0) :
    (n : ℕ) → ProductHomotopyStage F G n
  | 0 => productHomotopyStageZero F G h₀
  | n + 1 => (productHomotopyStages F G hF hG h₀ n).extend hF hG

#print axioms productHomotopyStages
#print axioms productHomotopyStageZero
end HodgeLean.Foundations.Singular
