import HodgeLean.Foundations.Program.SchoenTowerL1bKummerOrbitDescent

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The given contravariant action is an action by actual automorphisms. -/
def s2v_l1b_divisor_actionAut
    {D : Type*} [Category D] (X : D) (G : Type*) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) : G →* Aut X where
  toFun g := Aut.of
    { hom := a g
      inv := a g⁻¹
      hom_inv_id := by rw [← hamul, inv_mul_cancel, ha1]
      inv_hom_id := by rw [← hamul, mul_inv_cancel, ha1] }
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    exact ha1
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    exact hamul g h

/-- The original finite orbit map has categorical descent on its smooth base. -/
theorem s2v_l1b_divisor_original_quotient
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (f : X ⟶ Y) [IsFinite f.left]
    (hsurj : Function.Surjective (Point.map f))
    (hinv : ∀ g, a g ≫ f = f)
    (horbit : ∀ x y : ComplexPoint X,
      Point.map f x = Point.map f y ↔ ∃ g, Point.map (a g) x = y) :
    ∀ (T : Over (Spec ↧ℂ)) (g : X ⟶ T),
      (∀ i, a i ≫ g = g) → ∃! u : Y ⟶ T, f ≫ u = g := by
  exact s2v_l1b_categorical_quotient_of_point_orbits X Y G
    (s2v_l1b_divisor_actionAut X G a ha1 hamul) f hsurj hinv horbit

end HodgeLean.Foundations.Program
