import HodgeLean.Foundations.Program.G32Native.RetainedRegularEquationDifferential
import HodgeLean.Foundations.Program.G32Native.FramedCovectorQuotient
import HodgeLean.Foundations.Program.G32Native.RegularEquationCoefficientOperator
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The retained conormal quotient in original algebraic frame coordinates -/
noncomputable section
set_option maxHeartbeats 50000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- Evaluate retained conormal covectors and express the resulting normal
functional in the specified algebraic dual frame.
Source: the dual conormal pairing and `i1_conormalFrameBasis`. -/
def retainedNormalFrameQuotientAt
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (U : Y.left.Opens) (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (x : ComplexPoint Y) (hx : x ∈ Point.overOpen U)
    (z : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    (Fin d → ℂ) →L[ℂ] (Fin k → ℂ) :=
  let D := retainedAffineConormalDifferential X Y j d A hA x (hU hx) z hz
  framedCovectorQuotient (i1_conormalFrameBasis j.left k U E x hx) D

/-- The quotient retains its basis and covector family without expanding
concrete fibre maps.
Source: definition of `retainedNormalFrameQuotientAt`. -/
theorem retainedNormalFrameQuotientAt_eq
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (U : Y.left.Opens) (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (x : ComplexPoint Y) (hx : x ∈ Point.overOpen U)
    (z : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    retainedNormalFrameQuotientAt X Y j d k A hA U hU E x hx z hz =
      framedCovectorQuotient (i1_conormalFrameBasis j.left k U E x hx)
        (retainedAffineConormalDifferential X Y j d A hA x (hU hx) z hz) := rfl

/-- The equation coefficient matrix applied to the retained quotient gives
the derivatives of the same original equations, with no change of fibre.
Source: `retainedAffineConormalDifferential_regular_value` and
`dual_coordinate_pairing`. -/
theorem retainedNormalFrameQuotientAt_equation
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (U : Y.left.Opens) (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (u : Fin k → RingHom.ker (j.left.app A).hom)
    (r : Fin k → Fin k → Γ(Y.left, U))
    (x : ComplexPoint Y) (hx : x ∈ Point.overOpen U)
    (hr : ∀ i a, i1_conormalFrameCoordinates j.left k U E x hx
      (originalRegularConormalValue j.left A hA (u i) x (hU hx)) a = Point.evaluate U (r i a) x)
    (z : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (v : Fin d → ℂ) (i : Fin k) :
    regularEquationCoefficientOperator Y k U r x
      (retainedNormalFrameQuotientAt X Y j d k A hA U hU E x hx z hz v) i =
      fderiv ℂ (fun c : Fin d → ℂ =>
        Point.evaluate A (u i).val ((chartAt (Fin d → ℂ) z).symm c))
        ((chartAt (Fin d → ℂ) z) (Point.map j x)) v := by
  rw [retainedNormalFrameQuotientAt_eq, regularEquationCoefficientOperator_apply]
  rw [← retainedAffineConormalDifferential_regular_value X Y j d A hA (u i)
    x (hU hx) z hz]
  rw [← framedCovectorQuotient_pairing (i1_conormalFrameBasis j.left k U E x hx)]
  apply Finset.sum_congr rfl
  intro a _
  rw [i1_conormalFrameBasis, Module.Basis.ofEquivFun_repr_apply, hr]

#print axioms retainedNormalFrameQuotientAt_eq
#print axioms retainedNormalFrameQuotientAt_equation
end HodgeLean.Foundations.TubularEuler
