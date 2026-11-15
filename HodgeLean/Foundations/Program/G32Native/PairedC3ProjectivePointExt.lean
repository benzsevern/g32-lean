import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveFactorCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Equality of scheme maps on the original complex points -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Equality after every original complex-point morphism determines a map
from a reduced scheme of finite type to a separated scheme.
Source: Mathlib.AlgebraicGeometry.Morphisms.Separated,
`ext_of_isDominant`; Mathlib.AlgebraicGeometry.AlgClosed.Basic,
`pointOfClosedPoint`. -/
theorem paired_c3_hom_ext_of_complex_points
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (Y : Scheme) [Y.IsSeparated] (f g : X.left ⟶ Y)
    (h : ∀ p : ComplexPoint X, p.left ≫ f = p.left ≫ g) : f = g := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  haveI : IsDominant (equalizer.ι f g) := by
    refine ⟨Dense.mono ?_ (show Dense (closedPoints X.left) from ?_)⟩
    · intro x hx
      let p : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x hx)
        (pointOfClosedPoint_comp X.hom x hx)
      let a := equalizer.lift p.left (h p)
      refine ⟨a (IsLocalRing.closedPoint ℂ), ?_⟩
      have ha : a ≫ equalizer.ι f g = p.left := equalizer.lift_ι p.left (h p)
      have hp := congrArg (fun t : Spec ↧ℂ ⟶ X.left => t (IsLocalRing.closedPoint ℂ)) ha
      exact (Scheme.Hom.comp_apply a (equalizer.ι f g) _).symm.trans
        (hp.trans (pointOfClosedPoint_apply X.hom x hx _))
    · rw [dense_iff_closure_eq, closure_closedPoints]
  exact ext_of_isDominant (equalizer.ι f g) (equalizer.condition f g)

#print axioms paired_c3_hom_ext_of_complex_points
end HodgeLean.Foundations.Program.G32Native
