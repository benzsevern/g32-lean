import HodgeLean.Foundations.Program.SchoenCycleBranchParameterDivisibility
import HodgeLean.Foundations.Program.SchoenCycleInsertionPointRange

/-! # Actual branch sections at tuples containing the mark -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- At any actual tuple with first coordinate equal to the mark, every branch section is divisible by that coordinate parameter.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_branch_section_first_parameter_dvd
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B) (a : ComplexPoint Z)
    (x : ComplexPoint (g3_power Z (n + 1)))
    (hx : Point.map (g3_proj Z (n + 1) 0) x = a)
    (U : B.left.affineOpens) (hxU : γ.left x.underlying ∈ U.1)
    (s : Γ(B.left, U.1)) (hs : s ∈ (s2c_branchIdeal Z B n γ a).ideal U) :
    s2e_curvePowerParameter Z (n + 1) x 0 ∣
      γ.left.stalkMap x.underlying (B.left.presheaf.germ U.1 (γ.left x.underlying) hxU s) := by
  let y := Point.map (s2e_dropFirstPowerCoordinate Z n) x
  have he : Point.map (s2c_branchInsertion Z n a) y = x :=
    s2e_branchInsertion_point_of_first_coordinate Z n a x hx
  have hd : ∀ hmem : γ.left (Point.map (s2c_branchInsertion Z n a) y).underlying ∈ U.1,
      γ.left.stalkMap (Point.map (s2c_branchInsertion Z n a) y).underlying
        (B.left.presheaf.germ U.1 (γ.left (Point.map (s2c_branchInsertion Z n a) y).underlying)
          hmem s) ∈ Ideal.span (Set.singleton (s2e_curvePowerParameter Z (n + 1)
            (Point.map (s2c_branchInsertion Z n a) y) 0)) := by
    intro hmem
    exact s2e_branchIdeal_section_parameter_divisibility Z B n γ a y U hmem s hs
  rw [he] at hd
  exact Ideal.mem_span_singleton.mp (hd hxU)

end HodgeLean.Foundations.Program
