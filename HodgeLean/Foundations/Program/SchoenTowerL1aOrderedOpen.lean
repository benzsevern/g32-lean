import HodgeLean.Foundations.Program.SchoenTowerL1aOrderedEtale
import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction

/-! # Ordered open curve neighborhoods

Implication from an actual curve open immersion to the retained ordered
open immersion and its coordinatewise complex point lifts.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained ordered power of an actual open immersion is an open immersion.
Source: Hartshorne, Algebraic Geometry, II.3, products and open immersions. -/
theorem s2v_l1a_ordered_power_open
    {U Z : Over (Spec ↧ℂ)} (u : U ⟶ Z) [IsOpenImmersion u.left] (n : ℕ) :
    IsOpenImmersion (s2_powerMap u n).left := by
  induction n with
  | zero =>
      have heq : s2_powerMap u 0 = 𝟙 (g3_power Z 0) :=
        CartesianMonoidalCategory.toUnit_unique _ _
      rw [heq]
      change IsOpenImmersion (𝟙 (Spec ↧ℂ))
      infer_instance
  | succ n ih =>
      rw [s2v_l1a_powerMap_succ, Over.tensorHom_left]
      exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
        (inferInstance : IsOpenImmersion u.left) ih
        (Over.w u).symm (Over.w (s2_powerMap u n)).symm

/-- Specified lifts of all coordinate points give an actual lift of the
ordered complex point through the retained power map.
Source: Mac Lane, Categories for the Working Mathematician, III.4, product universal property. -/
theorem s2v_l1a_ordered_point_lift
    {U Z : Over (Spec ↧ℂ)} (u : U ⟶ Z) (n : ℕ)
    (x : ComplexPoint (g3_power Z n)) (y : Fin n → ComplexPoint U)
    (hy : ∀ i, Point.map u (y i) = Point.map (g3_proj Z n i) x) :
    Point.map (s2_powerMap u n) (s2_lift n y) = x := by
  apply s2_product_hom_ext n
  intro i
  change (s2_lift n y ≫ s2_powerMap u n) ≫ g3_proj Z n i = x ≫ g3_proj Z n i
  have hp : s2_powerMap u n ≫ g3_proj Z n i = g3_proj U n i ≫ u :=
    s2_check_lift_proj n _ i
  rw [Category.assoc, hp, ← Category.assoc, s2_check_lift_proj]
  exact hy i

end HodgeLean.Foundations.Program
