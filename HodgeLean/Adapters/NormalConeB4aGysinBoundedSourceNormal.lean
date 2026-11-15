import HodgeLean.Adapters.NormalConeB4aGysinSmoothSourceNormal
import HodgeLean.Adapters.NormalConeB4aGysinSmoothProjectionNull

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- Smooth support presentations with relative dimension at most the parameter
dimension have transverse slices outside one null set of parameters. -/
theorem a3b4a_gysin_bounded_relative_dimension_normal_parameters
    (X Y : Over (Spec (CommRingCat.of ℂ))) (m n c : ℕ)
    [SmoothOfRelativeDimension m X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsImmersion f.left] (γ : AlgebraicCycle Y.left ℚ)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) (hmn : m ≤ n)
    (hS : ∀ y ∈ Φ.source, y ∈ a3b4_cycleSupport Y.hom γ ↔ y ∈ Set.range (Point.map f)) :
    ∃ B : Set (Fin n → ℂ), MeasureTheory.volume B = 0 ∧
      ∀ x : ComplexPoint X, Point.map f x ∈ Φ.source → (Φ (Point.map f x)).1 ∉ B →
        ∃ C : A3b4aGysinNormalChart Y.hom γ c, C.point = Point.map f x ∧
          HasFDerivAt (fun v' =>
            (C.chart (Φ.symm ((Φ (Point.map f x)).1, v' + (Φ (Point.map f x)).2))).2)
            (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 := by
  by_cases hmn' : m = n
  · subst m
    exact a3b4a_gysin_smooth_source_normal_parameters X Y n c f γ Φ hΦ hS
  · let B := (fun x => (Φ (Point.map f x)).1) '' (Point.map f ⁻¹' Φ.source)
    refine ⟨B, a3b4a_gysin_smooth_source_parameter_image_null X Y m n c f Φ hΦ
      (lt_of_le_of_ne hmn hmn'), ?_⟩
    intro x hx hnot
    exact (hnot ⟨x, hx, rfl⟩).elim

end HodgeLean.Adapters
