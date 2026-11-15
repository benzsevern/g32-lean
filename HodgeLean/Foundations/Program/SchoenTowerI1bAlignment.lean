import HodgeLean.Foundations.Program.SchoenTowerI1bTranslations

/-! # I1b coordinate orbit alignment
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- Coordinate orbit lifts align any two tuples with permuted projected coordinates. -/
theorem s2v_i1b_align_points
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (p : Y ⟶ Z)
    (hp : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (h : ℕ) (x y : ComplexPoint (g3_power Y h))
    (τ : Equiv.Perm (Fin h))
    (he : Point.map (s2_permute Z h τ) (Point.map (s2_powerMap p h) x) =
      Point.map (s2_powerMap p h) y) :
    ∃ v : Fin h → ZMod S.m, Point.map (s2_action S Y a e h v τ) x = y := by
  have hc (j : Fin h) :
      Point.map p (Point.map (g3_proj Y h (τ.symm j)) x) =
      Point.map p (Point.map (g3_proj Y h j) y) := by
    have hj := congrArg (fun z => z ≫ g3_proj Z h j) he
    simpa only [Point.map, Category.assoc, s2_permute, s2_powerMap,
      s2_check_lift_proj] using hj
  choose u hu using fun j => (hp _ _).mp (hc j)
  refine ⟨fun j => Multiplicative.toAdd (e (u j)), ?_⟩
  apply s2_product_hom_ext h
  intro j
  simpa only [Point.map, Category.assoc, s2_action, s2_check_lift_proj,
    ofAdd_toAdd, e.symm_apply_apply] using hu j

end HodgeLean.Foundations.Program
