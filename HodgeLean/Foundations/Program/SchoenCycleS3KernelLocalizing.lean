module

public import HodgeLean.Foundations.Program.SchoenCycleS3LocalizingKernels
public import HodgeLean.Foundations.Program.SchoenCycleS3LocalizedKernelMap

/-! # Localization of kernels on affine schemes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Kernels of localizing sheaves of modules are localizing. -/
theorem s2e_sheafKernel_isLocalizing {R : CommRingCat.{u}}
    {M N : CategoryTheory.Sheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)}
    (φ : M ⟶ N)
    (hM : IsLocalizing (show TopCat.Sheaf (ModuleCat R) (Spec R) from M))
    (hN : IsLocalizing (show TopCat.Sheaf (ModuleCat R) (Spec R) from N)) :
    IsLocalizing (show TopCat.Sheaf (ModuleCat R) (Spec R) from
      (kernel φ : CategoryTheory.Sheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R))) := by
  intro a
  let U := PrimeSpectrum.basicOpen a
  let m := (M.obj.map U.leTop.op).hom
  let n := (N.obj.map U.leTop.op).hom
  let f := (φ.hom.app (.op ⊤)).hom
  let g := (φ.hom.app (.op U)).hom
  let : IsLocalizedModule (.powers a) m := hM a
  let : IsLocalizedModule (.powers a) n := hN a
  have h : g.comp m = n.comp f := congrArg ModuleCat.Hom.hom (φ.hom.naturality U.leTop.op)
  let t : f.ker →ₗ[R] g.ker := m.restrict (fun x hx => by
    change g (m x) = 0
    rw [← LinearMap.comp_apply, h, LinearMap.comp_apply, hx, map_zero])
  let : IsLocalizedModule (.powers a) t := s2e_localizedKernelMap (.powers a) m n f g h
  let e₀ := (s2e_sheafKernelSectionsIso φ ⊤).toLinearEquiv
  let e₁ := (s2e_sheafKernelSectionsIso φ U).toLinearEquiv
  have ht : IsLocalizedModule (.powers a) (e₁.symm.toLinearMap.comp (t.comp e₀.toLinearMap)) := by
    infer_instance
  have he : e₁.symm.toLinearMap.comp (t.comp e₀.toLinearMap) =
      ((kernel φ).obj.map U.leTop.op).hom := by
    apply LinearMap.ext
    intro x
    apply e₁.injective
    apply Subtype.ext
    have hi₀ := s2e_sheafKernelSectionsIso_inv_ι φ ⊤
    have hi₁ := s2e_sheafKernelSectionsIso_inv_ι φ U
    have h₀ : (kernel.ι φ).hom.app (.op ⊤) x = (e₀ x).val := by
      have hh := congrArg (fun q => q.hom (e₀ x)) hi₀
      change (kernel.ι φ).hom.app (.op ⊤) (e₀.symm (e₀ x)) = (e₀ x).val at hh
      rw [LinearEquiv.symm_apply_apply] at hh
      exact hh
    have h₁ : ∀ y, (kernel.ι φ).hom.app (.op U) y = (e₁ y).val := by
      intro y
      have hh := congrArg (fun q => q.hom (e₁ y)) hi₁
      change (kernel.ι φ).hom.app (.op U) (e₁.symm (e₁ y)) = (e₁ y).val at hh
      rw [LinearEquiv.symm_apply_apply] at hh
      exact hh
    change (e₁ (e₁.symm (t (e₀ x)))).val =
      (e₁ (((kernel φ).obj.map U.leTop.op) x)).val
    rw [LinearEquiv.apply_symm_apply, ← h₁]
    change m ((e₀ x).val) = _
    rw [← h₀]
    exact (congrArg (fun q => q.hom x) ((kernel.ι φ).hom.naturality U.leTop.op)).symm
  rw [he] at ht
  exact ht

end HodgeLean.Foundations.Program
