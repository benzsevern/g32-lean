import HodgeLean.Foundations.Program.SchoenCycleBranchCoordinateDivisibility
import HodgeLean.Foundations.Program.SchoenCycleCoordinateParameterSeparation
import HodgeLean.Foundations.Program.SchoenCyclePrimeProductDivision

/-! # Products of actual marked coordinate parameters divide branch sections -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- Every actual branch section is divisible by the product of any set of coordinates centered at the mark.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_branch_section_marked_product_dvd
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (a : ComplexPoint Z) (x : ComplexPoint (g3_power Z (n + 1)))
    (S : Finset (Fin (n + 1)))
    (hS : ∀ i ∈ S, Point.map (g3_proj Z (n + 1) i) x = a)
    (U : B.left.affineOpens) (hxU : γ.left x.underlying ∈ U.1)
    (s : Γ(B.left, U.1)) (hs : s ∈ (s2c_branchIdeal Z B n γ a).ideal U) :
    (∏ i ∈ S, s2e_curvePowerParameter Z (n + 1) x i) ∣
      γ.left.stalkMap x.underlying (B.left.presheaf.germ U.1 (γ.left x.underlying) hxU s) := by
  apply s2e_distinct_prime_product_dvd (s2e_curvePowerParameter Z (n + 1) x) S
  · intro i _
    exact (Ideal.span_singleton_prime (s2e_curvePowerParameter_ne_zero Z (n + 1) x i)).mp
      (s2e_curvePowerParameter_ideal_prime Z n x i)
  · intro i _ j _ hij
    exact s2e_curvePowerParameter_not_dvd_of_ne Z n x i j hij
  intro i hi
  exact s2e_branch_section_coordinate_parameter_dvd Z B n γ hγ a x i (hS i hi) U hxU s hs

end HodgeLean.Foundations.Program
