import HodgeLean.Foundations.Program.SchoenTowerI2aOrderedCurveChart

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Actual curve-coordinate pullbacks retain the specified tuple evaluations.
Source: Hartshorne, Algebraic Geometry, II.2, functoriality of residue evaluation. -/
theorem s2v_i2a_curve_coordinate_evaluations
    (A V Z : Over (Spec ↧ℂ)) (n : ℕ)
    (u : A ⟶ Z) [Mono u] (v : V ⟶ g3_power Z n)
    (a : Fin n → (V ⟶ A))
    (ha : ∀ i, a i ≫ u = v ≫ g3_proj Z n i)
    (p : ComplexPoint V) (x : ComplexPoint (g3_power Z n))
    (hp : Point.map v p = x) (y : Fin n → ComplexPoint A)
    (hy : ∀ i, Point.map u (y i) = Point.map (g3_proj Z n i) x)
    (z : Γ(A.left, ⊤)) :
    ∀ i, Point.evaluate ⊤ ((a i).left.appTop.hom z) p =
      Point.evaluate ⊤ z (y i) := by
  have hay (i : Fin n) : Point.map (a i) p = y i := by
    apply (cancel_mono u).mp
    change (p ≫ a i) ≫ u = y i ≫ u
    rw [Category.assoc, ha, ← Category.assoc]
    change Point.map (g3_proj Z n i) (Point.map v p) = Point.map u (y i)
    rw [hp, hy]
  intro i
  have H := Point.evaluate_map (a i) ⊤ z p
  rw [hay] at H
  simpa only [TopologicalSpace.Opens.map_top, Scheme.Hom.appTop] using H.symm

end HodgeLean.Foundations.Program
