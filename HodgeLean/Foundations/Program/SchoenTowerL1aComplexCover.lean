import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Complex points detect scheme open covers

Implication from local finite type over the complex numbers to detection of
an open cover by complex points. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An open subset containing the underlying point of every complex point is the whole scheme.
Source: Hartshorne, Algebraic Geometry, II.3, schemes of finite type over an algebraically closed field; Jacobson property. -/
theorem s2v_l1a_open_eq_top_of_complex_points
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) (hU : ∀ x : ComplexPoint X, x.underlying ∈ U) :
    U = ⊤ := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply top_unique
  intro x _
  by_contra hx
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
    (Z := (U : Set X.left)ᶜ) ⟨x, hx⟩ U.isOpen.isClosed_compl.isLocallyClosed
  let z : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom y hyc)
    (pointOfClosedPoint_comp X.hom y hyc)
  have hz : z.underlying = y := by
    change pointOfClosedPoint X.hom y hyc (IsLocalRing.closedPoint ℂ) = y
    exact pointOfClosedPoint_apply X.hom y hyc _
  exact hy (hz ▸ hU z)

/-- A finite complex scheme map surjective on complex points is surjective on scheme points.
Source: Hartshorne, Algebraic Geometry, II.3, finite maps and the Jacobson property. -/
theorem s2v_l1a_scheme_surjective_of_complex_surjective
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left]
    (hsurj : Function.Surjective (Point.map f)) :
    AlgebraicGeometry.Surjective f.left := by
  let : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hr : IsClosed (Set.range f.left) := f.left.isClosedMap.isClosed_range
  have hclosed : closedPoints Y.left ⊆ Set.range f.left := by
    intro y hy
    let z : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y hy)
      (pointOfClosedPoint_comp Y.hom y hy)
    obtain ⟨w, hw⟩ := hsurj z
    refine ⟨w.underlying, ?_⟩
    rw [← Point.underlying_map, hw]
    change pointOfClosedPoint Y.hom y hy (IsLocalRing.closedPoint ℂ) = y
    exact pointOfClosedPoint_apply Y.hom y hy _
  have hwhole : (Set.univ : Set Y.left) ⊆ Set.range f.left := by
    rw [← closure_closedPoints (X := Y.left)]
    exact hr.closure_subset_iff.mpr hclosed
  exact ⟨fun y => hwhole (Set.mem_univ y)⟩

/-- An open family covering complex points also covers the underlying scheme.
Source: Hartshorne, Algebraic Geometry, II.3, Jacobson schemes and algebraically closed base fields. -/
theorem s2v_l1a_scheme_cover_of_complex_cover
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    {κ : Type*} (V : κ → Over (Spec ↧ℂ)) (v : ∀ k, V k ⟶ X)
    [∀ k, IsOpenImmersion (v k).left]
    (hcover : ∀ x : ComplexPoint X, ∃ k, x ∈ Set.range (Point.map (v k))) :
    ∀ x : X.left, ∃ k, x ∈ Set.range (v k).left := by
  let U : X.left.Opens := ⨆ k, (v k).left.opensRange
  have hU : U = ⊤ := by
    apply s2v_l1a_open_eq_top_of_complex_points
    intro x
    obtain ⟨k, y, rfl⟩ := hcover x
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨k, ?_⟩
    rw [Point.underlying_map]
    exact ⟨y.underlying, rfl⟩
  intro x
  have hx : x ∈ U := hU.symm ▸ TopologicalSpace.Opens.mem_top x
  exact TopologicalSpace.Opens.mem_iSup.mp hx

end HodgeLean.Foundations.Program
