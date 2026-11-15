import HodgeLean.Foundations.Program.G32Native.RetainedAffineEquationRestriction
import HodgeLean.Foundations.Program.G32Native.RetainedRegularEquationDifferential

/-! # Retained derivatives of corresponding original equations -/
noncomputable section
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

/-- Corresponding regular equations have the same retained covector in
one ambient chart, before identifying their original conormal values.
Source: `affineIdealDifferential_restriction`,
`affineIdealDifferential_chart_eq`, and
`retainedAffineConormalDifferential_regular_value`. -/
theorem retained_restricted_equation_values
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A B : X.left.Opens) (hA : IsAffineOpen A) (hB : IsAffineOpen B) (hBA : B ≤ A)
    (u : RingHom.ker (j.left.app A).hom) (v : RingHom.ker (j.left.app B).hom)
    (hv : v.val = X.left.presheaf.map (homOfLE hBA).op u.val)
    (x : ComplexPoint Y) (hxA : x ∈ Point.overOpen (j.left ⁻¹ᵁ A))
    (hxB : x ∈ Point.overOpen (j.left ⁻¹ᵁ B))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    retainedAffineConormalDifferential X Y j d A hA x hxA z hz
        (originalRegularConormalValue j.left A hA u x hxA) =
      retainedAffineConormalDifferential X Y j d B hB x hxB z hz
        (originalRegularConormalValue j.left B hB v x hxB) := by
  have hd := affineIdealDifferential_restriction X Y j d A B hA hB hBA u v hv x hxB z hz
  rw [affineIdealDifferential_chart_eq, affineIdealDifferential_chart_eq] at hd
  exact (retainedAffineConormalDifferential_regular_value X Y j d A hA u x hxA z hz).trans
    (hd.trans (retainedAffineConormalDifferential_regular_value X Y j d B hB v x hxB z hz).symm)

#print axioms retained_restricted_equation_values
end HodgeLean.Foundations.TubularEuler
