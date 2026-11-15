import HodgeLean.Foundations.Program.SchoenTowerI2bChartInertia

/-! Projecting a fixed normalization-chart point to the actual covering point.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Fixing the actual chart point fixes its covering point under the intertwined iterate.
Source: iteration of the projection square and faithfulness of the underlying scheme morphism. -/
theorem s2v_i2b_complex_point_fixed_of_chart
    (W : Over (Spec ↧ℂ)) (Q : Scheme) (π : Q ⟶ W.left)
    (d : W ⟶ W) (dn : Q ⟶ Q) (hπ : dn ≫ π = π ≫ d.left)
    (q : Spec ↧ℂ ⟶ Q) (p : ComplexPoint W) (hq : q ≫ π = p.left)
    (n : ℕ) (hfixed : (fun z : Spec ↧ℂ ⟶ Q => z ≫ dn)^[n] q = q) :
    (Point.map d)^[n] p = p := by
  have hs : Function.Semiconj (fun z : Spec ↧ℂ ⟶ Q => z ≫ π)
      (fun z => z ≫ dn) (fun z => z ≫ d.left) := by
    intro z
    change (z ≫ dn) ≫ π = (z ≫ π) ≫ d.left
    rw [Category.assoc, hπ, Category.assoc]
  have hi := hs.iterate_right n q
  rw [hfixed, hq] at hi
  have hu : Function.Semiconj (fun z : ComplexPoint W => z.left)
      (Point.map d) (fun z => z ≫ d.left) := by
    intro z
    rfl
  have huN := hu.iterate_right n p
  apply Over.OverMorphism.ext
  exact huN.trans hi.symm

end HodgeLean.Foundations.Program
