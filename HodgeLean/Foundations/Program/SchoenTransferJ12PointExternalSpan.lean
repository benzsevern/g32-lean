import HodgeLean.Foundations.Program.SchoenTransferJ12PointExternalPrime

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- External multiplication by an actual point class preserves the source cycle span.
Source: prime-supported purity on the constant graph, extended rationally over cycle classes. -/
theorem s4_selected_point_external_span
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : ℕ) (hA : TopologicalSpace.dim A.left = a)
    (e : ComplexPoint A) (hec : Order.coheight e.underlying = a)
    (p : ℕ) (b : HQ Y (2 * p)) (hb : b ∈ cfd_cycleSpan Y p) :
    (cupProductOf (A ⊗ Y)).cup (by omega : 2 * a + 2 * p = 2 * (a + p))
      (homPullback (fst A Y) (2 * a) (cycleComponentSheafClass A e.underlying hec))
      (homPullback (snd A Y) (2 * p) b) ∈ cfd_cycleSpan (A ⊗ Y) (a + p) := by
  let f : Y ⟶ A := (Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e
  have he (y : ComplexPoint Y) : Point.map f y = e := by
    have hy : y ≫ (Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      exact Over.w y
    change y ≫ ((Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e) = e
    rw [← Category.assoc, hy, Category.id_comp]
  let L : HQ Y (2 * p) →ₗ[ℚ] HQ (A ⊗ Y) (2 * (a + p)) :=
    ((cupProductOf (A ⊗ Y)).cup (by omega : 2 * a + 2 * p = 2 * (a + p))
      (homPullback (fst A Y) (2 * a) (cycleComponentSheafClass A e.underlying hec))).comp
      (homPullback (snd A Y) (2 * p))
  have hL : cfd_cycleSpan Y p ≤ (cfd_cycleSpan (A ⊗ Y) (a + p)).comap L := by
    change algebraicCycleClassSpan Y p ≤ _
    rw [algebraicCycleClassSpan]
    refine sSup_le ?_
    rintro _ ⟨z, hz, rfl⟩
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact s4_selected_point_external_prime_mem A Y a (dim Y.left) hA rfl f e he hec z p hz
  exact hL hb

#print axioms s4_selected_point_external_span
end HodgeLean.Foundations.Program
