import HodgeLean.Foundations.Program.SchoenCoordinateActionLaws

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- The actual retained complex points of a scheme power identify with tuples of retained complex points by the product projections. -/
def s2_powerComplexPointEquiv (Y : Over (Spec ↧ℂ)) (h : ℕ) :
    ComplexPoint (g3_power Y h) ≃ (Fin h → ComplexPoint Y) where
  toFun x i := x ≫ g3_proj Y h i
  invFun y := s2_lift h y
  left_inv x := by
    apply s2_product_hom_ext h
    intro i
    exact s2_check_lift_proj h (fun j => x ≫ g3_proj Y h j) i
  right_inv y := by
    funext i
    exact s2_check_lift_proj h y i

/-- Actual translated-permutation actions have the prescribed coordinate formula on retained complex point tuples. -/
theorem s2_powerComplexPointEquiv_action (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m)) (h : ℕ)
    (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h))
    (x : ComplexPoint (g3_power Y h)) (i : Fin h) :
    s2_powerComplexPointEquiv Y h (Point.map (s2_action S Y a e h v σ) x) i =
      Point.map (a (e.symm (.ofAdd (v i)))) (s2_powerComplexPointEquiv Y h x (σ.symm i)) := by
  change (x ≫ s2_action S Y a e h v σ) ≫ g3_proj Y h i =
    (x ≫ g3_proj Y h (σ.symm i)) ≫ a (e.symm (.ofAdd (v i)))
  rw [Category.assoc, s2_action, s2_check_lift_proj, ← Category.assoc]

/-- The actual power morphism acts coordinatewise on retained complex point tuples. -/
theorem s2_powerComplexPointEquiv_powerMap {Y X : Over (Spec ↧ℂ)}
    (p : Y ⟶ X) (h : ℕ) (x : ComplexPoint (g3_power Y h)) (i : Fin h) :
    s2_powerComplexPointEquiv X h (Point.map (s2_powerMap p h) x) i =
      Point.map p (s2_powerComplexPointEquiv Y h x i) := by
  change (x ≫ s2_powerMap p h) ≫ g3_proj X h i = (x ≫ g3_proj Y h i) ≫ p
  rw [Category.assoc, s2_powerMap, s2_check_lift_proj, ← Category.assoc]

/-- The actual factor permutation permutes retained complex point coordinates. -/
theorem s2_powerComplexPointEquiv_permute (X : Over (Spec ↧ℂ)) (h : ℕ)
    (σ : Equiv.Perm (Fin h)) (x : ComplexPoint (g3_power X h)) (i : Fin h) :
    s2_powerComplexPointEquiv X h (Point.map (s2_permute X h σ) x) i =
      s2_powerComplexPointEquiv X h x (σ.symm i) := by
  change (x ≫ s2_permute X h σ) ≫ g3_proj X h i = x ≫ g3_proj X h (σ.symm i)
  rw [Category.assoc, s2_permute, s2_check_lift_proj]

/-- A morphism surjective on retained complex points remains so on every actual finite coordinate power. -/
theorem s2_powerMap_point_surjective {Y X : Over (Spec ↧ℂ)}
    (p : Y ⟶ X) (hp : Function.Surjective (Point.map p)) (h : ℕ) :
    Function.Surjective (Point.map (s2_powerMap p h)) := by
  classical
  intro x
  choose y hy using fun i => hp (s2_powerComplexPointEquiv X h x i)
  refine ⟨(s2_powerComplexPointEquiv Y h).symm y, ?_⟩
  apply (s2_powerComplexPointEquiv X h).injective
  funext i
  rw [s2_powerComplexPointEquiv_powerMap, Equiv.apply_symm_apply]
  exact hy i

end HodgeLean.Foundations.Program
