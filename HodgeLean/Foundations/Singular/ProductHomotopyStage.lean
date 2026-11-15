import HodgeLean.Foundations.Singular.ProductSelfExtensions
import HodgeLean.Foundations.Singular.ChainHomotopyObstruction
import HodgeLean.Foundations.Singular.ProductSteps

/-! Actual natural degree-raising maps on rational product chains. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Singular

/-- The actual rational chain complex of a topological product.
Source: Hatcher, Algebraic Topology, §3.2, products of singular chains. -/
abbrev rationalProductChains (X Y : TopCat.{0}) := rationalChains (TopCat.of (X × Y))

/-- The actual rational product-chain map of two continuous maps.
Source: Hatcher, Algebraic Topology, §3.2, functoriality of product chains. -/
abbrev rationalProductChainMap {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :=
  rationalChainMap (topologicalProductMap f g)

/-- An actual natural degree-raising product-chain map with its boundary value on cycles.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
structure ProductHomotopyStage
    (F G : ∀ X Y : TopCat.{0}, rationalProductChains X Y ⟶ rationalProductChains X Y) (n : ℕ) where
  hom : ∀ X Y : TopCat.{0},
    (rationalProductChains X Y).X n →ₗ[ℚ] (rationalProductChains X Y).X (n + 1)
  naturality : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
    (hom X' Y').comp ((rationalProductChainMap f g).f n).hom =
      (((rationalProductChainMap f g).f (n + 1)).hom).comp (hom X Y)
  cycles : ∀ (X Y : TopCat.{0}) (z : (rationalProductChains X Y).X n),
    ((rationalProductChains X Y).d n (n - 1)).hom z = 0 →
      ((rationalProductChains X Y).d (n + 1) n).hom (hom X Y z) =
        ((F X Y).f n).hom z - ((G X Y).f n).hom z

/-- The next product-chain homotopy obstruction has a filler on its diagonal universal model.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
theorem ProductHomotopyStage.model_filler
    {F G : ∀ X Y : TopCat.{0}, rationalProductChains X Y ⟶ rationalProductChains X Y}
    {n : ℕ} (H : ProductHomotopyStage F G n) :
    let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))
    ∃ w : (rationalProductChains X X).X (n + 2),
      ((rationalProductChains X X).d (n + 2) (n + 1)).hom w =
        ((F X X).f (n + 1)).hom (universalProductSimplex (n + 1)) -
          ((G X X).f (n + 1)).hom (universalProductSimplex (n + 1)) -
            H.hom X X (((rationalProductChains X X).d (n + 1) n).hom
              (universalProductSimplex (n + 1))) := by
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))
  let u := universalProductSimplex (n + 1)
  let z : (rationalProductChains X X).X (n + 1) :=
    ((F X X).f (n + 1)).hom u - ((G X X).f (n + 1)).hom u -
      H.hom X X (((rationalProductChains X X).d (n + 1) n).hom u)
  have hz : ((rationalProductChains X X).d (n + 1) n).hom z = 0 :=
    chainHomotopy_obstruction_cycle (F X X) (G X X) n (H.hom X X) (H.cycles X X) u
  exact simplexProductModel_cycle_filler (n + 1) (n + 1) n z hz

#print axioms ProductHomotopyStage.model_filler
end HodgeLean.Foundations.Singular
