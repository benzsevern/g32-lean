import HodgeLean.Foundations.Program.TorusAlgebraizationB54GlobalEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Point
open scoped MonoidalCategory
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem b54_product_map_openImmersion {X Y A B : Over (Spec ↧ℂ)}
    (f : A ⟶ X) (g : B ⟶ Y) [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    IsOpenImmersion (f ⊗ₘ g).left := by
  change IsOpenImmersion (Limits.pullback.map _ _ _ _ f.left g.left (𝟙 _) (by simp) (by simp))
  infer_instance

theorem b54_product_point_lift {X Y A B : Over (Spec ↧ℂ)}
    (f : A ⟶ X) (g : B ⟶ Y) (p : ComplexPoint (gagam_product X Y))
    (a : ComplexPoint A) (b : ComplexPoint B)
    (ha : map f a = map (CartesianMonoidalCategory.fst X Y) p)
    (hb : map g b = map (CartesianMonoidalCategory.snd X Y) p) :
    ∃ q : ComplexPoint (gagam_product A B), map (f ⊗ₘ g) q = p := by
  refine ⟨CartesianMonoidalCategory.lift a b, ?_⟩
  apply CartesianMonoidalCategory.hom_ext
  · simpa [Point.map, Category.assoc] using ha
  · simpa [Point.map, Category.assoc] using hb

def b54_productCoordinates {A B : Over (Spec ↧ℂ)} {n : ℕ}
    (v : Fin n → Γ(A.left, ⊤)) (w : Fin n → Γ(B.left, ⊤)) :
    Fin (n * n) → Γ((gagam_product A B).left, ⊤) := fun k =>
  (CartesianMonoidalCategory.fst A B).left.appTop (v (finProdFinEquiv.symm k).1) *
    (CartesianMonoidalCategory.snd A B).left.appTop (w (finProdFinEquiv.symm k).2)

theorem b54_productCoordinates_evaluation {A B : Over (Spec ↧ℂ)} {n : ℕ}
    (v : Fin n → Γ(A.left, ⊤)) (w : Fin n → Γ(B.left, ⊤))
    (p : ComplexPoint (gagam_product A B)) (k : Fin (n * n)) :
    b54_globalEvaluation p (b54_productCoordinates v w k) =
      b54_globalEvaluation (map (CartesianMonoidalCategory.fst A B) p)
        (v (finProdFinEquiv.symm k).1) *
      b54_globalEvaluation (map (CartesianMonoidalCategory.snd A B) p)
        (w (finProdFinEquiv.symm k).2) := by
  rw [b54_productCoordinates, map_mul]
  exact congrArg₂ (fun x y : ℂ => x * y)
    (b54_globalEvaluation_map (CartesianMonoidalCategory.fst A B) p _)
    (b54_globalEvaluation_map (CartesianMonoidalCategory.snd A B) p _)

end HodgeLean.Foundations.Program
