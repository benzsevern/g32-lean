import HodgeLean.Foundations.Singular.TensorHomotopyStage
import HodgeLean.Foundations.Singular.TensorModelBoundary

/-! The recursive extension of actual natural tensor-chain homotopy maps. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- The next actual degree-raising map obtained by extending chosen universal model fillers.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
def TensorHomotopyStage.nextHom
    {F G : ∀ X Y : TopCat.{0}, rationalTensorChains X Y ⟶ rationalTensorChains X Y}
    {n : ℕ} (H : TensorHomotopyStage F G n) (X Y : TopCat.{0}) :
    (rationalTensorChains X Y).X (n + 1) →ₗ[ℚ] (rationalTensorChains X Y).X (n + 2) :=
  tensorModelExtension X Y (n + 1) (n + 2)
    (fun p q hpq => Classical.choose (H.model_filler p q hpq))

/-- Extending the chosen model fillers gives the full next chain-homotopy boundary equation.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
theorem TensorHomotopyStage.nextHom_boundary
    {F G : ∀ X Y : TopCat.{0}, rationalTensorChains X Y ⟶ rationalTensorChains X Y}
    (hF : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalTensorChainMap f g ≫ F X' Y' = F X Y ≫ rationalTensorChainMap f g)
    (hG : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalTensorChainMap f g ≫ G X' Y' = G X Y ≫ rationalTensorChainMap f g)
    {n : ℕ} (H : TensorHomotopyStage F G n) (X Y : TopCat.{0}) :
    (((rationalTensorChains X Y).d (n + 2) (n + 1)).hom).comp (H.nextHom X Y) =
      H.obstruction X Y := by
  exact tensorModelExtension_boundary (n + 1) (n + 1) H.obstruction
    (H.obstruction_naturality hF hG)
    (fun p q hpq => Classical.choose (H.model_filler p q hpq))
    (fun p q hpq => Classical.choose_spec (H.model_filler p q hpq)) X Y

/-- The model-filler extension supplies the next natural tensor homotopy stage.
Source: Hatcher, Algebraic Topology, §3.2, acyclic models for chain homotopies. -/
def TensorHomotopyStage.extend
    {F G : ∀ X Y : TopCat.{0}, rationalTensorChains X Y ⟶ rationalTensorChains X Y}
    (hF : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalTensorChainMap f g ≫ F X' Y' = F X Y ≫ rationalTensorChainMap f g)
    (hG : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      rationalTensorChainMap f g ≫ G X' Y' = G X Y ≫ rationalTensorChainMap f g)
    {n : ℕ} (H : TensorHomotopyStage F G n) : TensorHomotopyStage F G (n + 1) where
  hom := H.nextHom
  naturality f g := tensorModelExtension_naturality f g (n + 1) (n + 2) _
  cycles X Y z hz := by
    have hz' : ((rationalTensorChains X Y).d (n + 1) n).hom z = 0 := by simpa using hz
    have hb := LinearMap.congr_fun (H.nextHom_boundary hF hG X Y) z
    change ((rationalTensorChains X Y).d (n + 2) (n + 1)).hom (H.nextHom X Y z) =
      ((F X Y).f (n + 1)).hom z - ((G X Y).f (n + 1)).hom z -
        H.hom X Y (((rationalTensorChains X Y).d (n + 1) n).hom z) at hb
    simpa only [hz', map_zero, sub_zero] using hb

#print axioms TensorHomotopyStage.extend
#print axioms TensorHomotopyStage.nextHom
#print axioms TensorHomotopyStage.nextHom_boundary
end HodgeLean.Foundations.Singular
