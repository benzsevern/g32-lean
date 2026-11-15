import HodgeLean.Foundations.AbelianQuotient.ImageGeometry

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.AbelianQuotient

/-- A reduced source turns containment of topological images into containment of image ideals. -/
theorem kernel_le_of_range_subset {X Y Z : Scheme} (i : X ⟶ Z) (g : Y ⟶ Z)
    [QuasiCompact g] [IsReduced Y] (h : Set.range g ⊆ Set.range i) : i.ker ≤ g.ker := by
  rw [← radical_image_kernel g, ← Scheme.IdealSheafData.vanishingIdeal_support]
  apply (Scheme.IdealSheafData.gc _ _).mp
  change g.ker.support ≤ i.ker.support
  change (g.ker.support : Set Z) ⊆ (i.ker.support : Set Z)
  rw [Scheme.Hom.support_ker]
  exact closure_minimal (h.trans i.range_subset_ker_support) i.ker.support.isClosed

/-- Containment on complex points detects containment in a closed subscheme. -/
theorem range_subset_of_complex_points
    {X Y Z : Over (Spec ↧ℂ)} (i : X ⟶ Z) [IsClosedImmersion i.left]
    (g : Y ⟶ Z) [LocallyOfFiniteType Y.hom]
    (h : ∀ y : ComplexPoint Y, ∃ x : ComplexPoint X,
      Point.map i x =
        Point.map g y) :
    Set.range g.left ⊆ Set.range i.left := by
  letI := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hc : closedPoints Y.left ⊆ g.left ⁻¹' Set.range i.left := by
    intro y hy
    let z : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y hy) (pointOfClosedPoint_comp Y.hom y hy)
    have hz : z.underlying = y := pointOfClosedPoint_apply Y.hom y hy _
    obtain ⟨x, hx⟩ := h z
    have hh := congrArg Point.underlying hx
    rw [Point.underlying_map,
      Point.underlying_map, hz] at hh
    exact ⟨x.underlying, hh⟩
  have hd := closure_minimal hc (i.left.isClosedMap.isClosed_range.preimage g.left.continuous)
  rw [closure_closedPoints] at hd
  rintro _ ⟨y, rfl⟩
  exact hd (Set.mem_univ y)

/-- A map from a reduced source factors through a closed immersion when its complex points do. -/
theorem lift_of_complex_points {X Y Z : Over (Spec ↧ℂ)} (i : X ⟶ Z)
    [IsClosedImmersion i.left] (g : Y ⟶ Z) [IsReduced Y.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact g.left]
    (h : ∀ y : ComplexPoint Y, ∃ x : ComplexPoint X, Point.map i x = Point.map g y) :
    ∃ l : Y ⟶ X, l ≫ i = g := by
  have hker := kernel_le_of_range_subset i.left g.left (range_subset_of_complex_points i g h)
  let l := IsClosedImmersion.lift i.left g.left hker
  have hl : l ≫ i.left = g.left := IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk l ?_, ?_⟩
  · rw [← Over.w i, ← Category.assoc, hl, Over.w g]
  · apply Over.OverMorphism.ext
    exact hl

end HodgeLean.Foundations.AbelianQuotient
