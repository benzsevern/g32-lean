import HodgeLean.Foundations.Program.SchoenTowerL1aOrderedOpen

/-! # Retained permutation orbits in ordered curve neighborhoods

Implication from the actual coordinatewise point lift to containment of the
whole retained orbit in the ordered curve neighborhood.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual retained power map commutes with the retained permutations.
Source: Mac Lane, Categories for the Working Mathematician, III.4, product functoriality. -/
theorem s2v_l1a_ordered_power_permutation
    {U Z : Over (Spec ↧ℂ)} (u : U ⟶ Z) (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    s2_permute U n τ ≫ s2_powerMap u n =
      s2_powerMap u n ≫ s2_permute Z n τ := by
  apply s2_product_hom_ext n
  intro i
  simp only [Category.assoc, s2_permute, s2_powerMap, s2_check_lift_proj]
  rw [← Category.assoc, s2_check_lift_proj]

/-- An ordered point lifting to the curve neighborhood has its whole actual
permutation orbit in the image of that same retained power map.
Source: Schoen (1988), Lemma 2.2, printed p. 13, invariant ordered neighborhoods. -/
theorem s2v_l1a_ordered_orbit_in_range
    {U Z : Over (Spec ↧ℂ)} (u : U ⟶ Z) (n : ℕ)
    (x : ComplexPoint (g3_power Z n)) (y : ComplexPoint (g3_power U n))
    (hy : Point.map (s2_powerMap u n) y = x) (τ : Equiv.Perm (Fin n)) :
    (Point.map (s2_permute Z n τ) x).underlying ∈ Set.range (s2_powerMap u n).left := by
  have H : Point.map (s2_powerMap u n) (Point.map (s2_permute U n τ) y) =
      Point.map (s2_permute Z n τ) x := by
    change (y ≫ s2_permute U n τ) ≫ s2_powerMap u n = x ≫ s2_permute Z n τ
    rw [Category.assoc, s2v_l1a_ordered_power_permutation, ← Category.assoc]
    exact congrArg (fun f => f ≫ s2_permute Z n τ) hy
  exact ⟨(Point.map (s2_permute U n τ) y).underlying, congrArg Point.underlying H⟩

end HodgeLean.Foundations.Program
