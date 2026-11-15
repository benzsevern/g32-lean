import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Retain the supplied conormal model under a second scheme identification -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Change the model's scheme through the specified isomorphism, retaining
the original module isomorphism and the canonical pullback comparisons. -/
def paired_module_modelIso_transport {X Y Z : Scheme}
    (e : X ≅ Y) (d : Z ≅ Y) (N : X.Modules) (M : Y.Modules)
    (E : N ≅ (Scheme.Modules.pullback e.hom).obj M) :
    N ≅ (Scheme.Modules.pullback (e ≪≫ d.symm).hom).obj
      ((Scheme.Modules.pullback d.hom).obj M) := by
  have h : (e ≪≫ d.symm).hom ≫ d.hom = e.hom := by
    change (e.hom ≫ d.inv) ≫ d.hom = e.hom
    rw [Category.assoc, d.inv_hom_id, Category.comp_id]
  exact E ≪≫ ((Scheme.Modules.pullbackComp (e ≪≫ d.symm).hom d.hom).app M ≪≫
    (Scheme.Modules.pullbackCongr h).app M).symm

end HodgeLean.Foundations.Program.G32Native
