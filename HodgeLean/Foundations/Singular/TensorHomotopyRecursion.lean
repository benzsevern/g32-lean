import HodgeLean.Foundations.Singular.TensorHomotopyStep

/-! Assembly of actual natural tensor-chain homotopies degree by degree. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Singular

/-- Equal degree-zero chain maps have the zero degree-raising tensor stage.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
def tensorHomotopyStageZero
    (F G : ∀ X Y : TopCat.{0}, rationalTensorChains X Y ⟶ rationalTensorChains X Y)
    (h₀ : ∀ X Y : TopCat.{0}, (F X Y).f 0 = (G X Y).f 0) : TensorHomotopyStage F G 0 where
  hom X Y := 0
  naturality f g := by
    ext z
    simp
  cycles X Y z hz := by
    change ((rationalTensorChains X Y).d 1 0).hom 0 =
      ((F X Y).f 0).hom z - ((G X Y).f 0).hom z
    rw [map_zero, h₀ X Y, sub_self]

/-- The recursive actual tensor homotopy stages for two natural chain endomaps equal on vertices.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
def tensorHomotopyStages
    (F G : ∀ X Y : TopCat.{0}, rationalTensorChains X Y ⟶ rationalTensorChains X Y)
    (hF : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalTensorChainMap f g ≫ F X' Y' = F X Y ≫ rationalTensorChainMap f g)
    (hG : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalTensorChainMap f g ≫ G X' Y' = G X Y ≫ rationalTensorChainMap f g)
    (h₀ : ∀ X Y : TopCat.{0}, (F X Y).f 0 = (G X Y).f 0) :
    (n : ℕ) → TensorHomotopyStage F G n
  | 0 => tensorHomotopyStageZero F G h₀
  | n + 1 => (tensorHomotopyStages F G hF hG h₀ n).extend hF hG

#print axioms tensorHomotopyStages
#print axioms tensorHomotopyStageZero
end HodgeLean.Foundations.Singular
