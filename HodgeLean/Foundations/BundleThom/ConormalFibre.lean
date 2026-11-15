import HodgeLean.Foundations.AlgebraicGeometry.ConormalFramesDefs
import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # The actual complex conormal fibre and its dual

Pullback to the supplied complex point precedes taking global sections and
linear dual. These fibres retain the original immersion, without a splitting.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- The complex vector space obtained by pulling the actual conormal to a complex point.
Source: Hartshorne, Algebraic Geometry, II.8, conormal and normal sheaves. -/
abbrev i1_conormalFibre {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (x : ComplexPoint Q) : ModuleCat ℂ :=
  (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
    ((Scheme.Modules.pullback x.left).obj (AlgebraicGeometry.Conormal.sheaf j))

/-- The actual normal fibre is the complex linear dual of the conormal fibre.
Source: Hartshorne, Algebraic Geometry, II.8, normal sheaf of an immersion. -/
abbrev i1_normalFibre {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (x : ComplexPoint Q) :=
  Module.Dual ℂ (i1_conormalFibre j x)

example {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (x : ComplexPoint Q)
    (f : i1_normalFibre j x) (v : i1_conormalFibre j x) :
    f ((2 : ℂ) • v) = (2 : ℂ) • f v := map_smul f (2 : ℂ) v

example {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (x : ComplexPoint Q)
    (f : i1_normalFibre j x) (v w : i1_conormalFibre j x) :
    f (v + w) = f v + f w := map_add f v w

end HodgeLean.Foundations.BundleThom
