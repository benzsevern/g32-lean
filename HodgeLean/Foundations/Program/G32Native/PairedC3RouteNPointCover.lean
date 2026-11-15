import HodgeLean.Foundations.Program.G32Native.PairedC3ClosedPointCover
import HodgeLean.Foundations.Program.SchoenCycleC11ComponentHelpers

/-! # Scheme-point coverage from complex points on a closed locus -/
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- An open family covering every complex point of a closed locus covers
all its scheme points. The complement is a closed finite-type locus.
Source: Hartshorne, Algebraic Geometry, II.3.14; the Jacobson property. -/
theorem paired_c3_closed_locus_open_cover
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (C : Closeds X.left) {ι : Type*} (U : ι → X.left.Opens)
    (hU : ∀ p : ComplexPoint X, p.underlying ∈ C → ∃ i, p.underlying ∈ U i) :
    ∀ x : X.left, x ∈ C → ∃ i, x ∈ U i := by
  let V : X.left.Opens := ⨆ i, U i
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hc : (C : Set X.left) ⊆ V := paired_c3_closed_point_cover C.isClosed V.isOpen (by
    intro x hx hxclosed
    let p : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x hxclosed)
      (pointOfClosedPoint_comp X.hom x hxclosed)
    have hp : p.underlying = x := pointOfClosedPoint_apply X.hom x hxclosed _
    obtain ⟨i, hi⟩ := hU p (hp.symm ▸ hx)
    exact Opens.mem_iSup.mpr ⟨i, hp ▸ hi⟩)
  intro x hx
  exact Opens.mem_iSup.mp (hc hx)

end HodgeLean.Foundations.Program.G32Native
