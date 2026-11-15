import HodgeLean.Foundations.Curves.Picard.LineBundles.TensorSections

/-! # Tensor multiplication under module pushforward

The structure-ring map acts on the actual tensor sections over inverse-image opens.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Sectionwise tensor multiplication under the actual module pushforward. -/
def pushforwardTensorPresheaf {X Y : Scheme} (f : X ⟶ Y) (M N : X.Modules) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := Y.presheaf) ((Scheme.Modules.pushforward f).obj M).val
        ((Scheme.Modules.pushforward f).obj N).val ⟶
      ((Scheme.Modules.pushforward f).obj (tensor M N)).val := by
  refine PresheafOfModulesOfCommRing.homMk (fun V => ?_) ?_
  · refine ModuleCat.MonoidalCategory.tensorLift
      (fun s t => tensorSection M N (f ⁻¹ᵁ V.unop) s t) ?_ ?_ ?_ ?_
    · intro s u t
      exact tensorSection_add_left M N _ s u t
    · intro a s t
      change tensorSection M N _ ((f.app V.unop a) • (show Γ(M, f ⁻¹ᵁ V.unop) from s)) t =
        (f.app V.unop a) • tensorSection M N _ s t
      exact tensorSection_smul_left M N _ _ s t
    · intro s t u
      exact tensorSection_add_right M N _ s t u
    · intro a s t
      change tensorSection M N _ s ((f.app V.unop a) • (show Γ(N, f ⁻¹ᵁ V.unop) from t)) =
        (f.app V.unop a) • tensorSection M N _ s t
      exact tensorSection_smul_right M N _ _ s t
  · intro V W g
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    exact (tensorSection_restrict M N ((TopologicalSpace.Opens.map f.base).map g.unop).le s t).symm

/-- The actual tensor comparison under module pushforward. -/
def pushforwardTensorHom {X Y : Scheme} (f : X ⟶ Y) (M N : X.Modules) :
    tensor ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      (Scheme.Modules.pushforward f).obj (tensor M N) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 Y.ringCatSheaf.obj)).symm
    (pushforwardTensorPresheaf f M N)

/-- Pushforward tensor multiplication sends pure tensors to their actual tensor section. -/
theorem pushforwardTensorHom_section {X Y : Scheme} (f : X ⟶ Y) (M N : X.Modules)
    (U : Y.Opens) (s : Γ((Scheme.Modules.pushforward f).obj M, U))
    (t : Γ((Scheme.Modules.pushforward f).obj N, U)) :
    (pushforwardTensorHom f M N).app U
        (tensorSection ((Scheme.Modules.pushforward f).obj M)
          ((Scheme.Modules.pushforward f).obj N) U s t) =
      tensorSection M N (f ⁻¹ᵁ U) s t := by
  have he := (PresheafOfModules.sheafificationHomEquiv
    (F := (Scheme.Modules.pushforward f).obj (tensor M N))
    (𝟙 Y.ringCatSheaf.obj)).apply_symm_apply
    (pushforwardTensorPresheaf f M N)
  have hh := congrArg (fun h => h.app (Opposite.op U) (s ⊗ₜ[Γ(Y, U)] t)) he
  exact hh

/-- The pushforward tensor comparison is natural in both module arguments. -/
theorem pushforwardTensorHom_naturality {X Y : Scheme} (f : X ⟶ Y)
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    tensorMap ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) ≫
        pushforwardTensorHom f M' N' =
      pushforwardTensorHom f M N ≫ (Scheme.Modules.pushforward f).map (tensorMap a b) := by
  apply tensor_hom_ext
  intro U s t
  change (pushforwardTensorHom f M' N').app U
      ((tensorMap ((Scheme.Modules.pushforward f).map a)
        ((Scheme.Modules.pushforward f).map b)).app U
          (tensorSection ((Scheme.Modules.pushforward f).obj M)
            ((Scheme.Modules.pushforward f).obj N) U s t)) =
    (tensorMap a b).app (f ⁻¹ᵁ U)
      ((pushforwardTensorHom f M N).app U
        (tensorSection ((Scheme.Modules.pushforward f).obj M)
          ((Scheme.Modules.pushforward f).obj N) U s t))
  rw [tensorMap_section, pushforwardTensorHom_section, pushforwardTensorHom_section]
  exact (tensorMap_section a b (f ⁻¹ᵁ U) s t).symm

end HodgeLean.Foundations.Curves.Picard.LineBundles
