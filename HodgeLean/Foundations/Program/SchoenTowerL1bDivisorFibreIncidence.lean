import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCoordinateGeneric

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- At the generic point of one coordinate fibre, incidence support detects precisely its marked point. -/
theorem s2v_l1b_divisor_coordinate_fibre_incidence_support
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ σ, s2_permute Z (h + 1) σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ σ, s2_permute Z (h + 1) σ ≫ f = f) → ∃! b : B ⟶ T, γ ≫ b = f)
    (b c : ComplexPoint Z) (i : Fin (h + 1))
    (y : (g3_power Z (h + 1)).left) (hy : Order.coheight y = 1)
    (hyi : (g3_proj Z (h + 1) i).left y = b.underlying) :
    γ.left y ∈ (s2c_branchIdeal Z B h γ c).support ↔ c = b := by
  classical
  rw [s2v_l1b_divisor_incidence_support_coordinate Z B hdimZ h γ hγsurj hγinv hγ c y]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      exact ComplexPoint.underlying_injective_of_locallyOfFiniteType (hj.symm.trans hyi)
    · have hjgen := s2v_l1b_divisor_other_coordinates_generic Z hdimZ h b i y hy hyi j hji
      exact False.elim (s2v_l1b_divisor_curve_complex_ne_generic Z hdimZ c (hj.symm.trans hjgen))
  · rintro rfl
    exact ⟨i, hyi⟩

end HodgeLean.Foundations.Program
