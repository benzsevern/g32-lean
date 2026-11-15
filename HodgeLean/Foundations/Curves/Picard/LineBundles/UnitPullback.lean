import HodgeLean.Foundations.Curves.Picard.LineBundles.PullbackTensor
import HodgeLean.Foundations.Curves.Picard.LineBundles.TensorUnitSections

/-! # Unit comparisons for module pullback

The coefficient map is the actual unit of the structure-module adjunction.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The actual structure-module coefficient map under pushforward. -/
def pushforwardUnit {X Y : Scheme} (f : X ⟶ Y) :
    unit Y ⟶ (Scheme.Modules.pushforward f).obj (unit X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- The actual pullback unit comparison is adjoint to the coefficient map. -/
theorem pullbackUnit_adjunct {X Y : Scheme} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnit f).hom =
      pushforwardUnit f :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-- The pushforward unit acts on sections by the actual structure-ring morphism. -/
theorem pushforwardUnit_section {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) :
    (pushforwardUnit f).app U s = f.app U s := rfl

/-- Tensor multiplication of coefficient maps agrees with their ring multiplication. -/
theorem pushforwardUnit_tensor {X Y : Scheme} (f : X ⟶ Y) :
    tensorMap (pushforwardUnit f) (pushforwardUnit f) ≫
        pushforwardTensorHom f (unit X) (unit X) ≫
        (Scheme.Modules.pushforward f).map (tensorUnit (unit X)).hom =
      (tensorUnit (unit Y)).hom ≫ pushforwardUnit f := by
  apply tensor_hom_ext
  intro U s t
  change ((Scheme.Modules.pushforward f).map (tensorUnit (unit X)).hom).app U
      ((pushforwardTensorHom f (unit X) (unit X)).app U
        ((tensorMap (pushforwardUnit f) (pushforwardUnit f)).app U
          (tensorSection (unit Y) (unit Y) U s t))) =
    (pushforwardUnit f).app U
      ((tensorUnit (unit Y)).hom.app U (tensorSection (unit Y) (unit Y) U s t))
  rw [tensorMap_section, pushforwardTensorHom_section, tensorUnit_section]
  change (tensorUnit (unit X)).hom.app (f ⁻¹ᵁ U)
      (tensorSection (unit X) (unit X) (f ⁻¹ᵁ U)
        (f.app U s) (f.app U t)) = f.app U ((show Γ(Y, U) from s) * (show Γ(Y, U) from t))
  rw [tensorUnit_section]
  exact ((f.app U).hom.map_mul (show Γ(Y, U) from s) (show Γ(Y, U) from t)).symm

end HodgeLean.Foundations.Curves.Picard.LineBundles
