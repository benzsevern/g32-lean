import HodgeLean.Foundations.Program.G32Native.PairedResidualClosedLocus

/-! # Factoring a retained slice through the full fibre immersion -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Containment of complex-point images gives an actual factorization
through a closed immersion with reduced source.
Source: Hartshorne, Algebraic Geometry, II.3, reduced closed subschemes. -/
theorem paired_c3_factor_closed_immersion_of_point_image
    (X Y Z : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [IsReduced X.left] [IsReduced Y.left]
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion g.left]
    (h : ∀ p : ComplexPoint X, ∃ q : ComplexPoint Y, Point.map g q = Point.map f p) :
    ∃ i : X ⟶ Y, i ≫ g = f := by
  let K : TopologicalSpace.Closeds Z.left :=
    ⟨Set.range g.left, g.left.isClosedEmbedding.isClosed_range⟩
  have hr : Set.range f.left ⊆ Set.range g.left :=
    residual_range_in_closed_locus X Z f K (by
      intro p
      obtain ⟨q, hq⟩ := h p
      change (Point.map f p).underlying ∈ Set.range g.left
      rw [← hq, Point.underlying_map]
      exact Set.mem_range_self _)
  have hk : g.left.ker ≤ f.left.ker := by
    rw [s2e_reduced_image_ideal g.left, s2e_reduced_image_ideal f.left]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono (closure_mono hr)
  let l := IsClosedImmersion.lift g.left f.left hk
  have hl : l ≫ g.left = f.left := IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
  rw [← Over.w g, ← Category.assoc, hl, Over.w f]

#print axioms paired_c3_factor_closed_immersion_of_point_image
end HodgeLean.Foundations.Program.G32Native
