import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneLoop
import HodgeLean.Foundations.Program.SchoenTowerL1bActionCircleHomotopy

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- The exponential circle map with specified initial logarithm and integral
number of turns. -/
def s2v_l1b_action_windingCircleMap (c : ℂ) (k : ℤ) :
    C(UnitAddCircle, {z : ℂ // z ≠ 0}) := by
  exact AlgebraicTopology.Singular.PuncturedPlane.windingCircle c k

/-- Projection of the canonical winding circle map on a real representative. -/
theorem s2v_l1b_action_windingCircleMap_coe (c : ℂ) (k : ℤ) (s : ℝ) :
    (s2v_l1b_action_windingCircleMap c k (s : UnitAddCircle)).val =
      Complex.exp (c + (s : ℂ) * ((k : ℂ) * (2 * Real.pi * Complex.I))) := rfl

/-- A canonical winding circle has the constant radius determined by its
initial logarithm. -/
theorem s2v_l1b_action_windingCircleMap_norm (c : ℂ) (k : ℤ) (x : UnitAddCircle) :
    ‖(s2v_l1b_action_windingCircleMap c k x).val‖ = Real.exp c.re := by
  induction x using Quotient.inductionOn with
  | h s =>
    rw [s2v_l1b_action_windingCircleMap_coe, Complex.norm_exp]
    congr 1
    simp

/-- The homology map of a punctured-plane circle map with a logarithmic lift
agrees with the canonical map with the same integral number of turns. -/
theorem s2v_l1b_action_circle_homology_normal_form
    (p : C(UnitAddCircle, {z : ℂ // z ≠ 0}))
    (L : ℝ → ℂ) (hL : Continuous L)
    (hp : ∀ s : ℝ, Complex.exp (L s) = (p (s : UnitAddCircle)).val)
    (k : ℤ)
    (hdL : ∀ s, L (s + 1) = L s + (k : ℂ) * (2 * Real.pi * Complex.I))
    (n : ℕ) :
    AlgebraicTopology.Singular.homologyMap ℤ n (TopCat.ofHom p) =
      AlgebraicTopology.Singular.homologyMap ℤ n
        (TopCat.ofHom (s2v_l1b_action_windingCircleMap 0 k)) := by
  exact AlgebraicTopology.Singular.PuncturedPlane.circle_homology_normal_form p L hL hp k hdL n

end HodgeLean.Foundations.Program
