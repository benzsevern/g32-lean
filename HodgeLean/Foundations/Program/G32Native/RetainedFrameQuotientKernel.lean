import HodgeLean.Foundations.Program.G32Native.RetainedFrameQuotientAnalytic

/-! # Kernel evaluation in the original conormal frame -/
noncomputable section
set_option maxHeartbeats 50000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

theorem retainedFrameQuotientOperator_kernel
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A) (U : Y.left.Opens)
    (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (z : ComplexPoint X) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen U) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (v : Fin d → ℂ)
    (hv : retainedFrameQuotientOperator X Y j d k A hA U hU E z x v = 0)
    (a : i1_conormalFibre j.left x) :
    retainedAffineConormalDifferential X Y j d A hA x (hU hx) z hz a v = 0 := by
  rw [retainedFrameQuotientOperator_eq X Y j d k A hA U hU E z x hx hz] at hv
  rw [← framedCovectorQuotient_pairing (i1_conormalFrameBasis j.left k U E x hx) _ v a]
  simp only [hv, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

#print axioms retainedFrameQuotientOperator_kernel
end HodgeLean.Foundations.TubularEuler
