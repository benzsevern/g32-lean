import HodgeLean.Foundations.Curves.SymmetricCharts.StageThree.Basic

/-! # S2 tower symmetric-power leaf A2

The smooth integral projective curve input implies the retained symmetric quotient
assembly in every degree. The library retains the projection and descent maps.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained symmetric quotient of a curve, in every natural degree.
Source: Schoen (1988), Remark 1.4; Milne, Jacobian Varieties, §3;
SGA 1, Exposé V, §1; SymmetricCharts/StageThree/Basic.lean:50.
HC no distance; AV milestone no distance.
-/
theorem s2_symmetric_power_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 1) (h : ℕ) :
    ∃ (B : Over (Spec ↧ℂ)) (γ : g3_power X h ⟶ B),
      ∃ (_ : IsIntegral B.left), Smooth B.hom ∧ IsProjective B.hom ∧
      TopologicalSpace.dim B.left = h ∧ IsFinite γ.left ∧
      Function.Surjective (Point.map γ) ∧
      (∀ σ, s2_permute X h σ ≫ γ = γ) ∧
      (∀ x y : ComplexPoint (g3_power X h), Point.map γ x = Point.map γ y ↔
        ∃ σ, Point.map (s2_permute X h σ) x = y) ∧
      (∀ (T : Over (Spec ↧ℂ)) (f : g3_power X h ⟶ T),
        (∀ σ, s2_permute X h σ ≫ f = f) →
        ∃! d : B ⟶ T, γ ≫ d = f) :=
  HodgeLean.Foundations.Curves.SymmetricCharts.StageThree.symmetric_power_assembly X hdim h

example := @HodgeLean.Foundations.Curves.SymmetricCharts.StageThree.retained_geometry_example

#print axioms s2_symmetric_power_aux
end HodgeLean.Foundations.Program
