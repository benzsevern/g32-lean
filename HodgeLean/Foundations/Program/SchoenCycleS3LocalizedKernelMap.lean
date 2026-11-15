module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! # Localizing a commuting square of module maps -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 100000
open LinearMap
namespace HodgeLean.Foundations.Program

/-- Kernel restriction in a localizing square is itself a localization map. -/
theorem s2e_localizedKernelMap {R : Type*} [CommRing R] (p : Submonoid R)
    {M N M' N' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N']
    (m : M →ₗ[R] M') (n : N →ₗ[R] N')
    [IsLocalizedModule p m] [IsLocalizedModule p n]
    (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (h : g.comp m = n.comp f) :
    IsLocalizedModule p (m.restrict (p := f.ker) (q := g.ker)
      (fun x hx => by
        change g (m x) = 0
        rw [← LinearMap.comp_apply, h, LinearMap.comp_apply, hx, map_zero])) := by
  have hg : g = IsLocalizedModule.map p m n f := by
    apply IsLocalizedModule.linearMap_ext p m n
    rw [h, IsLocalizedModule.map_comp]
  subst g
  let : Module (Localization p) M' := IsLocalizedModule.module p m
  let : IsScalarTower R (Localization p) M' := IsLocalizedModule.isScalarTower_module p m
  let : Module (Localization p) N' := IsLocalizedModule.module p n
  let : IsScalarTower R (Localization p) N' := IsLocalizedModule.isScalarTower_module p n
  exact LinearMap.toKerLocalized_isLocalizedModule (Localization p) p m n f

end HodgeLean.Foundations.Program
