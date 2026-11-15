import HodgeLean.Foundations.Singular.TensorModelExtensions
import HodgeLean.Foundations.Singular.TensorModels
import HodgeLean.Foundations.Singular.ChainHomotopyObstruction
import HodgeLean.Foundations.Singular.ProductSteps

/-! Natural degree maps for constructing homotopies on actual tensor chains. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Singular

/-- An actual natural degree-raising tensor map with its boundary value on cycles.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction of chain homotopies. -/
structure TensorHomotopyStage
    (F G : ∀ X Y : TopCat.{0}, rationalTensorChains X Y ⟶ rationalTensorChains X Y) (n : ℕ) where
  hom : ∀ X Y : TopCat.{0},
    (rationalTensorChains X Y).X n →ₗ[ℚ] (rationalTensorChains X Y).X (n + 1)
  naturality : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
    (hom X' Y').comp ((rationalTensorChainMap f g).f n).hom =
      (((rationalTensorChainMap f g).f (n + 1)).hom).comp (hom X Y)
  cycles : ∀ (X Y : TopCat.{0}) (z : (rationalTensorChains X Y).X n),
    ((rationalTensorChains X Y).d n (n - 1)).hom z = 0 →
      ((rationalTensorChains X Y).d (n + 1) n).hom (hom X Y z) =
        ((F X Y).f n).hom z - ((G X Y).f n).hom z

/-- The next obstruction of an actual tensor homotopy stage has a filler on every universal model.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for the Eilenberg–Zilber comparison. -/
theorem TensorHomotopyStage.model_filler
    {F G : ∀ X Y : TopCat.{0}, rationalTensorChains X Y ⟶ rationalTensorChains X Y}
    {n : ℕ} (H : TensorHomotopyStage F G n) (p q : ℕ) (hpq : p + q = n + 1) :
    let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1)))
    let Y := TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1)))
    ∃ w : (rationalTensorChains X Y).X (n + 2),
      ((rationalTensorChains X Y).d (n + 2) (n + 1)).hom w =
        ((F X Y).f (n + 1)).hom (universalTensorSimplex p q (n + 1) hpq) -
          ((G X Y).f (n + 1)).hom (universalTensorSimplex p q (n + 1) hpq) -
            H.hom X Y (((rationalTensorChains X Y).d (n + 1) n).hom
              (universalTensorSimplex p q (n + 1) hpq)) := by
  letI := standardTopologicalSimplex_contractibleSpace p
  letI := standardTopologicalSimplex_contractibleSpace q
  exact contractibleTensor_cycle_filler _ _ n _
    (chainHomotopy_obstruction_cycle (F _ _) (G _ _) n (H.hom _ _) (H.cycles _ _) _)

/-- The actual next obstruction map for a degree-raising tensor stage.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction of chain homotopies. -/
def TensorHomotopyStage.obstruction
    {F G : ∀ X Y : TopCat.{0}, rationalTensorChains X Y ⟶ rationalTensorChains X Y}
    {n : ℕ} (H : TensorHomotopyStage F G n) (X Y : TopCat.{0}) :
    (rationalTensorChains X Y).X (n + 1) →ₗ[ℚ] (rationalTensorChains X Y).X (n + 1) :=
  ((F X Y).f (n + 1)).hom - ((G X Y).f (n + 1)).hom -
    (H.hom X Y).comp ((rationalTensorChains X Y).d (n + 1) n).hom

/-- The actual next obstruction map is natural whenever the two chain endomaps are natural.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction of chain homotopies. -/
theorem TensorHomotopyStage.obstruction_naturality
    {F G : ∀ X Y : TopCat.{0}, rationalTensorChains X Y ⟶ rationalTensorChains X Y}
    (hF : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalTensorChainMap f g ≫ F X' Y' = F X Y ≫ rationalTensorChainMap f g)
    (hG : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalTensorChainMap f g ≫ G X' Y' = G X Y ≫ rationalTensorChainMap f g)
    {n : ℕ} (H : TensorHomotopyStage F G n)
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (H.obstruction X' Y').comp ((rationalTensorChainMap f g).f (n + 1)).hom =
      (((rationalTensorChainMap f g).f (n + 1)).hom).comp (H.obstruction X Y) := by
  apply LinearMap.ext
  intro z
  have hf := congrArg (fun k => (k.f (n + 1)).hom z) (hF f g)
  have hg := congrArg (fun k => (k.f (n + 1)).hom z) (hG f g)
  have hh := LinearMap.congr_fun (H.naturality f g)
    (((rationalTensorChains X Y).d (n + 1) n).hom z)
  change ((F X' Y').f (n + 1)).hom (((rationalTensorChainMap f g).f (n + 1)).hom z) =
    ((rationalTensorChainMap f g).f (n + 1)).hom (((F X Y).f (n + 1)).hom z) at hf
  change ((G X' Y').f (n + 1)).hom (((rationalTensorChainMap f g).f (n + 1)).hom z) =
    ((rationalTensorChainMap f g).f (n + 1)).hom (((G X Y).f (n + 1)).hom z) at hg
  dsimp only [obstruction, LinearMap.comp_apply, LinearMap.sub_apply]
  rw [map_sub, map_sub, hf, hg, rationalTensorChainMap_boundary]
  exact congrArg (fun t => _ - t) hh

#print axioms TensorHomotopyStage.obstruction
#print axioms TensorHomotopyStage.obstruction_naturality
#print axioms TensorHomotopyStage.model_filler
end HodgeLean.Foundations.Singular
