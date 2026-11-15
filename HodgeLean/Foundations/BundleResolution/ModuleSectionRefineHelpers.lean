import HodgeLean.Foundations.BundleResolution.ModulePointValueAlgebraHelpers
import HodgeLean.Foundations.BundleResolution.ModulePointValueRefineHelpers
/-! # Restriction of actual module sections

Normalized section pullback respects specialization at the original point.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleResolution
variable {Q : Over (Spec ↧ℂ)}

def i1_moduleSectionRefine (M : Q.left.Modules) {V U : Q.left.Opens} (h : V ≤ U)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M) :
    SheafOfModules.unit V.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback V.ι).obj M :=
  i1_module_sectionPullback (Q.left.homOfLE h) ((Scheme.Modules.pullback U.ι).obj M) s ≫
    (Scheme.Modules.pullbackComp (Q.left.homOfLE h) U.ι).hom.app M ≫
      (Scheme.Modules.pullbackCongr (Q.left.homOfLE_ι h)).hom.app M

theorem i1_moduleSectionValue_refine (M : Q.left.Modules) {V U : Q.left.Opens} (h : V ≤ U)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen V) :
    i1_moduleSectionValue M V (i1_moduleSectionRefine M h s) x hx =
      i1_moduleSectionValue M U s x (h hx) := by
  let a := ComplexPoint.liftToOpen Q V x hx
  let b := Q.left.homOfLE h
  let w := ComplexPoint.liftToOpen Q U x (h hx)
  have hw : a ≫ b = w := by
    apply (cancel_mono U.ι).1
    dsimp only [a, b, w]
    rw [Category.assoc, Q.left.homOfLE_ι, ComplexPoint.liftToOpen_fac,
      ComplexPoint.liftToOpen_fac]
  exact i1_module_pointValue_factorization a b U.ι V.ι w x.left
    (Q.left.homOfLE_ι h) hw (ComplexPoint.liftToOpen_fac Q V x hx)
    (ComplexPoint.liftToOpen_fac Q U x (h hx)) M s
end HodgeLean.Foundations.BundleResolution
