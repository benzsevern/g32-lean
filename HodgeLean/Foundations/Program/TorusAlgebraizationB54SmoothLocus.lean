import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Transitivity on closed points transports a smooth point to every closed point.
Source: EGA IV, 17.7.1 and 17.15.12; smoothness is invariant under isomorphisms. -/
theorem b54_smooth_of_transitive_isomorphisms {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType f] [IsReduced X] [Nonempty X]
    (hmove : ∀ (x y : X), IsClosed ({x} : Set X) → IsClosed ({y} : Set X) →
      ∃ α : Over.mk f ≅ Over.mk f, α.hom.left x = y) : Smooth f := by
  have := LocallyOfFiniteType.jacobsonSpace f
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints H f.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy : y ∈ f.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.2.isLocallyClosed
  obtain ⟨α, hα⟩ := hmove x y hxc hyc
  rw! [← hα, ← α.hom.left.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    show α.hom.left ≫ f = f from α.hom.w] at hy
  exact hx hy

end HodgeLean.Foundations.Program
