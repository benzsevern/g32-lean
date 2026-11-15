import HodgeLean.Foundations.Program.SchoenSelectedGeometryComplexDominance
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
namespace HodgeLean.Foundations.Program

/-- Smoothness at every complex point implies smoothness for a complex scheme locally of finite presentation.
Source: openness of the smooth locus and the Jacobson property. -/
theorem s0_smooth_of_complex_points
    (X : Over (Spec ↧ℂ)) [LocallyOfFinitePresentation X.hom]
    (h : ∀ z : ComplexPoint X, z.underlying ∈ X.hom.smoothLocus) : Smooth X.hom := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    Set.eq_univ_iff_forall]
  intro x
  by_contra hx
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
    (show (↑X.hom.smoothLocus : Set X.left)ᶜ.Nonempty from ⟨x, hx⟩)
    X.hom.smoothLocus.isOpen.isClosed_compl.isLocallyClosed
  let z : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom y hyc)
    (pointOfClosedPoint_comp X.hom y hyc)
  have hz : z.underlying = y := pointOfClosedPoint_apply X.hom y hyc _
  exact hy (hz ▸ h z)

#print axioms s0_smooth_of_complex_points
end HodgeLean.Foundations.Program
