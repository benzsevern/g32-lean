import HodgeLean.Foundations.BundleResolution.ModuleFrameSectionHelpers
import HodgeLean.Foundations.Algebraic.GrassmannianSheafFree

/-! # Regular coefficients of sections in an algebraic frame

The free projections give actual regular coefficient functions, and their
finite sum recovers the supplied module section.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Algebraic
namespace HodgeLean.Foundations.BundleResolution
variable {Q : Over (Spec ↧ℂ)}

def i1_module_frameSectionCoefficient (M : Q.left.Modules) (U : Q.left.Opens) (k : ℕ)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) ≅
      (Scheme.Modules.pullback U.ι).obj M)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj M) (i : Fin k) : Γ(U.toScheme, ⊤) :=
  f5sheaf_scalOf (s ≫ e.inv ≫ f5sheaf_freeProj i)

theorem i1_module_frameSection_decomposition (M : Q.left.Modules) (U : Q.left.Opens) (k : ℕ)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) ≅
      (Scheme.Modules.pullback U.ι).obj M)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj M) :
    s = ∑ i : Fin k, f5sheaf_scal (i1_module_frameSectionCoefficient M U k e s i) ≫
      SheafOfModules.ιFree i ≫ e.hom := by
  symm
  calc
    _ = (s ≫ e.inv) ≫ (∑ i : Fin k, f5sheaf_freeProj i ≫ SheafOfModules.ιFree i) ≫
        e.hom := by
      simp only [i1_module_frameSectionCoefficient, f5sheaf_scal_scalOf,
        Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    _ = s := by
      erw [f5sheaf_sum_freeProj, Category.id_comp, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
end HodgeLean.Foundations.BundleResolution
