import HodgeLean.Foundations.Curves.Picard.LineBundles.PushforwardTensor
import HodgeLean.Foundations.Curves.Picard.LineBundles.TensorFunctor

/-! # Tensor comparison through the module adjunction

The comparison is the mate of the actual pushforward tensor map.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The canonical pullback tensor map obtained from the module adjunction. -/
def pullbackTensorHom {X Y : Scheme} (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (tensor M N) ⟶
      tensor ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (tensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      pushforwardTensorHom f ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N))

/-- The pullback tensor map has the specified pushforward adjoint. -/
theorem pullbackTensorHom_adjunct {X Y : Scheme} (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackTensorHom f M N) =
      tensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      pushforwardTensorHom f ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) :=
  Equiv.apply_symm_apply _ _

/-- The pullback tensor comparison is natural in both module arguments. -/
theorem pullbackTensorHom_naturality {X Y : Scheme} (f : X ⟶ Y)
    {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (tensorMap a b) ≫ pullbackTensorHom f M' N' =
      pullbackTensorHom f M N ≫
        tensorMap ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  have ha : a ≫ A.unit.app M' = A.unit.app M ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map a) :=
    A.unit.naturality a
  have hb : b ≫ A.unit.app N' = A.unit.app N ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map b) :=
    A.unit.naturality b
  apply (A.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rw [pullbackTensorHom_adjunct, pullbackTensorHom_adjunct]
  change tensorMap a b ≫ (tensorMap (A.unit.app M') (A.unit.app N') ≫ _) =
    (tensorMap (A.unit.app M) (A.unit.app N) ≫ _) ≫ _
  rw [← Category.assoc, tensorMap_comp, ha, hb, ← tensorMap_comp]
  rw [Category.assoc, pushforwardTensorHom_naturality]
  simp only [Category.assoc]

end HodgeLean.Foundations.Curves.Picard.LineBundles
