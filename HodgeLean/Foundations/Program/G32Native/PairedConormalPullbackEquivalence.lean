import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Equivalence

/-! # Actual module pullback along a scheme isomorphism -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The two actual pullback functors and their composition comparisons give an equivalence. -/
def conormalModulesPullbackEquivalence {X Y : Scheme} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (pullback e.hom) (pullback e.inv)
    ((pullbackComp e.inv e.hom ≪≫
      eqToIso (congrArg pullback e.inv_hom_id) ≪≫ pullbackId Y).symm)
    (pullbackComp e.hom e.inv ≪≫
      eqToIso (congrArg pullback e.hom_inv_id) ≪≫ pullbackId X)

/-- The original pullback functor is an equivalence, without replacing its maps. -/
theorem conormal_pullback_isEquivalence {X Y : Scheme} (e : X ≅ Y) :
    (pullback e.hom).IsEquivalence :=
  (conormalModulesPullbackEquivalence e).isEquivalence_functor

end HodgeLean.Foundations.Program.G32Native
