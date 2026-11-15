import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryFlatHelpers

/-! The smooth neighbourhood of the retained support primes. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- All given smooth ambient neighbourhoods lie in the canonical smooth locus.
For an integral finite-type complex target this locus is dense. -/
theorem s4_q3_retained_smooth_open
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left]
    [LocallyOfFinitePresentation W.hom]
    (z : AlgebraicCycle W.left ℚ)
    (hz : ∀ x ∈ z.support,
      ∃ V : W.left.Opens, x ∈ V ∧ Smooth (V.ι ≫ W.hom)) :
    Dense (W.hom.smoothLocus : Set W.left) ∧
      Smooth (W.hom.smoothLocus.ι ≫ W.hom) ∧
      ∀ x ∈ z.support, x ∈ W.hom.smoothLocus := by
  refine ⟨W.hom.dense_smoothLocus_of_perfectField,
    SingularCycles.boundary_smooth_restrict W.hom _ le_rfl, ?_⟩
  intro x hx
  obtain ⟨V, hxV, hV⟩ := hz x hx
  letI := hV
  have htop := (V.ι ≫ W.hom).smoothLocus_eq_top
  have hx' : (⟨x, hxV⟩ : V.toScheme) ∈ (V.ι ≫ W.hom).smoothLocus := by
    rw [htop]
    trivial
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at hx'

end HodgeLean.Foundations.Program
