import HodgeLean.Foundations.Program.G32Native.PairedConormalPullbackComposition
import HodgeLean.Foundations.Program.G32Native.PairedConormalHyperplaneIdealIso

/-! # Actual relation nonvanishing on the specified polynomial projective model -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual ideal comparison and scheme pullback preserve pointwise
nonvanishing of the same original relation arrow. -/
theorem conormal_polynomial_ideal_relation_pullback_ne_zero
    (k : ℕ) {A : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules}
    (a : idealModule (s2e_hyperplaneIdeal k) ⟶ A)
    (ha : ∀ x : ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))),
      (Scheme.Modules.pullback x.left).map a ≠ 0)
    (x : ComplexPoint (Over.mk
      ((s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom ≫
        ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) :
    (Scheme.Modules.pullback x.left).map
      ((conormalHyperplanePolynomialIdealIso k).inv ≫
        (Scheme.Modules.pullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom).map a) ≠ 0 := by
  let f := (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom
  let y : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) := Point.map (Over.homMk f (by rfl)) x
  have hy := ha y
  intro hz
  rw [Functor.map_comp] at hz
  have hh : (Scheme.Modules.pullback x.left).map ((Scheme.Modules.pullback f).map a) = 0 := by
    apply (cancel_epi ((Scheme.Modules.pullback x.left).map
      (conormalHyperplanePolynomialIdealIso k).inv)).mp
    simpa only [CategoryTheory.Limits.comp_zero] using hz
  exact hy ((conormal_pullback_comp_map_eq_zero x.left f a).mp hh)

end HodgeLean.Foundations.Program.G32Native
