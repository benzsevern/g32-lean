import HodgeLean.Foundations.Program.SchoenCycleBranchProductDivisibility
import HodgeLean.Foundations.Program.SchoenCycleParameterProductOrder
import HodgeLean.Foundations.Program.SchoenCycleLocalUnitApproximation

/-! # A branch section with the prescribed leading term has a unit quotient -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- A section of the actual branch ideal with the marked-product leading term generates that product ideal in the upstairs stalk.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_branch_section_marked_product_jet_unit
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (a : ComplexPoint Z) (x : ComplexPoint (g3_power Z (n + 1)))
    (S : Finset (Fin (n + 1)))
    (hS : ∀ i ∈ S, Point.map (g3_proj Z (n + 1) i) x = a)
    (U : B.left.affineOpens) (hxU : γ.left x.underlying ∈ U.1)
    (c : Γ(B.left, U.1)) (hc : c ∈ (s2c_branchIdeal Z B n γ a).ideal U) :
    let R := (g3_power Z (n + 1)).left.presheaf.stalk x.underlying
    let P := ∏ i ∈ S, s2e_curvePowerParameter Z (n + 1) x i
    let r := γ.left.stalkMap x.underlying
      (B.left.presheaf.germ U.1 (γ.left x.underlying) hxU c)
    r - P ∈ IsLocalRing.maximalIdeal R ^ (S.card + 1) →
      ∃ u : Rˣ, r = P * (u : R) := by
  dsimp only
  intro he
  obtain ⟨q, hq⟩ := s2e_branch_section_marked_product_dvd Z B n γ hγ a x S hS U hxU c hc
  have hu : IsUnit q := s2e_isUnit_of_product_approximation
    (IsLocalRing.maximalIdeal ((g3_power Z (n + 1)).left.presheaf.stalk x.underlying) ^ (S.card + 1))
    (∏ i ∈ S, s2e_curvePowerParameter Z (n + 1) x i) q
    (s2e_curvePowerParameter_product_not_mem_next_power Z (n + 1) x S) (by rwa [← hq])
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, ?_⟩
  simpa only [hu] using hq

end HodgeLean.Foundations.Program
