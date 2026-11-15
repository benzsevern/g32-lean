import HodgeLean.Foundations.BundleThom.ConormalFibre
import Mathlib.LinearAlgebra.Dual.Defs

/-! # Fibrewise transport retaining a specified conormal isomorphism

The dual map reverses direction. This is algebraic fibre transport, before
constructing an analytic bundle or a tubular support comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Apply the actual complex-point pullback and global sections to a conormal isomorphism.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, pullback and fibres. -/
def i1_conormalFibreIso {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (M : Q.left.Modules)
    (E : AlgebraicGeometry.Conormal.sheaf j ≅ M) (x : ComplexPoint Q) :
    i1_conormalFibre j x ≅
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
        ((Scheme.Modules.pullback x.left).obj M) :=
  (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    ((Scheme.Modules.pullback x.left).mapIso E)

/-- Dual fibre transport induced by the specified conormal isomorphism.
Source: Hartshorne, Algebraic Geometry, II.8, normal-conormal duality. -/
def i1_normalFibreEquiv {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (M : Q.left.Modules)
    (E : AlgebraicGeometry.Conormal.sheaf j ≅ M) (x : ComplexPoint Q) :
    Module.Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x.left).obj M)) ≃ₗ[ℂ] i1_normalFibre j x :=
  (i1_conormalFibreIso j M E x).toLinearEquiv.dualMap

example {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V)
    (M : Q.left.Modules) (E : AlgebraicGeometry.Conormal.sheaf j ≅ M)
    (x : ComplexPoint Q) (f : Module.Dual ℂ
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
        ((Scheme.Modules.pullback x.left).obj M))) (v : i1_conormalFibre j x) :
    i1_normalFibreEquiv j M E x f v = f ((i1_conormalFibreIso j M E x).hom v) := rfl

example {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V)
    (x : ComplexPoint Q) (v : i1_conormalFibre j x) :
    (i1_conormalFibreIso j _ (Iso.refl _) x).hom v = v := by
  simp only [i1_conormalFibreIso, Functor.mapIso_refl, Iso.refl_hom,
    ModuleCat.id_apply]

end HodgeLean.Foundations.BundleThom
