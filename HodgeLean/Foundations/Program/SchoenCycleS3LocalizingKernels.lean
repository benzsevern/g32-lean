module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! # Kernels of localizing module sheaves -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Sections of a module-sheaf kernel are the kernel of the map on sections. -/
def s2e_sheafKernelSectionsIso {R : CommRingCat.{u}}
    {M N : CategoryTheory.Sheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)} (φ : M ⟶ N) (U : (Spec R).Opens) :
    ((kernel φ).obj.obj (.op U)) ≅
      ModuleCat.of R (LinearMap.ker (φ.hom.app (.op U)).hom) := by
  let E := sheafToPresheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R) ⋙
    (evaluation _ _).obj (.op U)
  letI : E.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  exact PreservesKernel.iso E φ ≪≫ ModuleCat.kernelIsoKer (E.map φ)

/-- The section comparison preserves the inclusion of the kernel. -/
@[reassoc]
theorem s2e_sheafKernelSectionsIso_inv_ι {R : CommRingCat.{u}}
    {M N : CategoryTheory.Sheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)}
    (φ : M ⟶ N) (U : (Spec R).Opens) :
    (s2e_sheafKernelSectionsIso φ U).inv ≫ (kernel.ι φ).hom.app (.op U) =
      ModuleCat.ofHom (LinearMap.ker (φ.hom.app (.op U)).hom).subtype := by
  let E := sheafToPresheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R) ⋙
    (evaluation _ _).obj (.op U)
  let : E.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  change (ModuleCat.kernelIsoKer (E.map φ)).inv ≫
    ((PreservesKernel.iso E φ).inv ≫ E.map (kernel.ι φ)) = _
  rw [PreservesKernel.iso_inv_ι, ModuleCat.kernelIsoKer_inv_kernel_ι]
  rfl

end HodgeLean.Foundations.Program
