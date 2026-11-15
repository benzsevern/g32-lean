import HodgeLean.Foundations.TubularEuler.AffineIdealDifferentialHelpers

/-! # The original equation differential respects ambient open restriction -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

/-- Restricting an ideal equation to a smaller affine open leaves its
analytic covector unchanged in the same ambient chart.
Source: `TopCat.Presheaf.germ_res_apply` and `affineIdealDifferential`. -/
theorem affineIdealDifferential_restriction
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A B : X.left.Opens) (hA : IsAffineOpen A) (hB : IsAffineOpen B) (hBA : B ≤ A)
    (u : RingHom.ker (j.left.app A).hom) (v : RingHom.ker (j.left.app B).hom)
    (hv : v.val = X.left.presheaf.map (homOfLE hBA).op u.val)
    (x : ComplexPoint Y) (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ B))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    affineIdealDifferential X Y j d A hA x (hBA (show (Point.map j x).underlying ∈ B from hx)) z hz u =
      affineIdealDifferential X Y j d B hB x hx z hz v := by
  change actualStalkDifferential X d z (Point.map j x) hz
      (X.left.presheaf.germ A (Point.map j x).underlying (hBA (show (Point.map j x).underlying ∈ B from hx)) u.val) =
    actualStalkDifferential X d z (Point.map j x) hz
      (X.left.presheaf.germ B (Point.map j x).underlying hx v.val)
  rw [hv, TopCat.Presheaf.germ_res_apply]

/-- The original ideal differential evaluates an equation by its chart derivative.
Source: `actualStalkDifferential_eq_section` and `affineIdealDifferential`. -/
theorem affineIdealDifferential_chart_eq
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (u : RingHom.ker (j.left.app A).hom)
    (x : ComplexPoint Y) (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    affineIdealDifferential X Y j d A hA x hx z hz u =
      fderiv ℂ (fun c : Fin d → ℂ =>
        Point.evaluate A u.val ((chartAt (Fin d → ℂ) z).symm c))
        ((chartAt (Fin d → ℂ) z) (Point.map j x)) := by
  change actualStalkDifferential X d z (Point.map j x) hz
    (X.left.presheaf.germ A (Point.map j x).underlying hx u.val) = _
  rw [actualStalkDifferential_eq_section]

#print axioms affineIdealDifferential_chart_eq
#print axioms affineIdealDifferential_restriction
end HodgeLean.Foundations.TubularEuler
