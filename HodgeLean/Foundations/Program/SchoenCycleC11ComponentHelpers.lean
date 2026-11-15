import HodgeLean.Foundations.Port.AlgebraicGeometry.ComplexPoint.SmoothConnected
import Mathlib.Analysis.Complex.Polynomial.Basic
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Connected analytic algebraic-open charts select an algebraic open for any analytic clopen set.
Source: Mathlib, IsPreconnected.subset_or_subset and the open-cover union construction. -/
theorem s2e_c11_open_preimage_of_clopen_connected_cover
    (X : Over (Spec ↧ℂ)) {ι : Type*} (U : ι → X.left.Opens)
    (hcover : ∀ p : Point ℂ X, ∃ i, p.underlying ∈ U i)
    (hconn : ∀ i, IsPreconnected (Point.underlying ⁻¹' (U i : Set X.left) : Set (Point ℂ X)))
    (A : Set (Point ℂ X)) (hA : IsClopen A) :
    ∃ V : X.left.Opens, Point.underlying ⁻¹' (V : Set X.left) = A := by
  classical
  let I := {i : ι // (Point.underlying ⁻¹' (U i : Set X.left) : Set (Point ℂ X)) ⊆ A}
  let V : X.left.Opens := ⨆ i : I, U i.1
  refine ⟨V, ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hp
    exact i.2 hi
  · intro hp
    obtain ⟨i, hi⟩ := hcover p
    have hsub : (Point.underlying ⁻¹' (U i : Set X.left) : Set (Point ℂ X)) ⊆ A := by
      obtain h | h := IsPreconnected.subset_or_subset hA.isOpen hA.isClosed.isOpen_compl
        disjoint_compl_right (by intro q _; exact Classical.em (q ∈ A)) (hconn i)
      · exact h
      · exact False.elim (h hi hp)
    exact Opens.mem_iSup.mpr ⟨⟨i, hsub⟩, hi⟩

/-- Nonempty locally closed subsets of a finite-type complex scheme contain complex points.
Source: Hartshorne, Algebraic Geometry, II.3.14; Mathlib, nonempty_inter_closedPoints. -/
theorem s2e_c11_complexPoint_in_locallyClosed
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (S : Set X.left) (hS : IsLocallyClosed S) (hne : S.Nonempty) :
    ∃ p : Point ℂ X, p.underlying ∈ S := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨z, hzS, hz⟩ := nonempty_inter_closedPoints hne hS
  let p : Point ℂ X := Over.homMk (pointOfClosedPoint X.hom z hz)
    (pointOfClosedPoint_comp X.hom z hz)
  refine ⟨p, ?_⟩
  have hp : p.underlying = z := pointOfClosedPoint_apply X.hom z hz _
  exact hp.symm ▸ hzS

/-- A connected analytic algebraic-open cover identifies analytic and algebraic clopen subsets.
Source: Hartshorne, Algebraic Geometry, II.3.14, and connected-chart clopen selection. -/
theorem s2e_c11_clopen_preimage_of_connected_cover
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] {ι : Type*} (U : ι → X.left.Opens)
    (hcover : ∀ p : Point ℂ X, ∃ i, p.underlying ∈ U i)
    (hconn : ∀ i, IsPreconnected (Point.underlying ⁻¹' (U i : Set X.left) : Set (Point ℂ X)))
    (A : Set (Point ℂ X)) (hA : IsClopen A) :
    ∃ V : X.left.Opens, IsClosed (V : Set X.left) ∧
      Point.underlying ⁻¹' (V : Set X.left) = A := by
  obtain ⟨V, hV⟩ := s2e_c11_open_preimage_of_clopen_connected_cover X U hcover hconn A hA
  obtain ⟨W, hW⟩ := s2e_c11_open_preimage_of_clopen_connected_cover X U hcover hconn Aᶜ hA.compl
  have hdisj : Disjoint (V : Set X.left) (W : Set X.left) := by
    apply Set.disjoint_left.mpr
    intro x hxV hxW
    obtain ⟨p, hp⟩ := s2e_c11_complexPoint_in_locallyClosed X
      ((V : Set X.left) ∩ W) (V.isOpen.inter W.isOpen).isLocallyClosed ⟨x, hxV, hxW⟩
    have hpA : p ∈ A := (Set.ext_iff.mp hV p).mp hp.1
    have hpAc : p ∈ Aᶜ := (Set.ext_iff.mp hW p).mp hp.2
    exact hpAc hpA
  have hcov : ∀ x : X.left, x ∈ V ∨ x ∈ W := by
    intro x
    by_contra hx
    have hxc : x ∈ ((V : Set X.left) ∪ W)ᶜ := hx
    obtain ⟨p, hp⟩ := s2e_c11_complexPoint_in_locallyClosed X
      (((V : Set X.left) ∪ W)ᶜ) (V.isOpen.union W.isOpen).isClosed_compl.isLocallyClosed ⟨x, hxc⟩
    apply hp
    by_cases h : p ∈ A
    · exact Or.inl ((Set.ext_iff.mp hV p).mpr h)
    · exact Or.inr ((Set.ext_iff.mp hW p).mpr h)
  have heq : (V : Set X.left)ᶜ = W := by
    ext x
    constructor
    · intro hx
      exact (hcov x).resolve_left hx
    · intro hxW hxV
      exact Set.disjoint_left.mp hdisj hxV hxW
  refine ⟨V, ?_, hV⟩
  apply isOpen_compl_iff.mp
  rw [heq]
  exact W.isOpen

/-- Smooth integral affine neighbourhoods provide the connected charts for clopen comparison.
Source: ComplexPoint.connectedSpace for smooth integral schemes and ComplexPoint.openHomeomorph. -/
theorem s2e_c11_smooth_clopen_of_integral_affine_cover
    (X : Over (Spec ↧ℂ)) [Smooth X.hom] {ι : Type*} (U : ι → X.left.Opens)
    (hcover : ∀ p : Point ℂ X, ∃ i, p.underlying ∈ U i)
    (hIntegral : ∀ i, IsIntegral (U i).toScheme) (hAffine : ∀ i, IsAffine (U i).toScheme)
    (A : Set (Point ℂ X)) (hA : IsClopen A) :
    ∃ V : X.left.Opens, IsClosed (V : Set X.left) ∧
      Point.underlying ⁻¹' (V : Set X.left) = A := by
  apply s2e_c11_clopen_preimage_of_connected_cover X U hcover
  · intro i
    letI : IsIntegral (openScheme X (U i)).left := hIntegral i
    letI : IsAffine (openScheme X (U i)).left := hAffine i
    letI : Smooth (openScheme X (U i)).hom := by
      change Smooth ((U i).ι ≫ X.hom)
      infer_instance
    letI : ConnectedSpace (Point ℂ (openScheme X (U i))) :=
      AlgebraicGeometry.ComplexPoint.connectedSpace _
    haveI : ConnectedSpace
        (Point.underlying ⁻¹' (U i : Set X.left) : Set (Point ℂ X)) :=
      (openHomeomorph X (U i)).connectedSpace_iff.mp inferInstance
    exact isPreconnected_iff_preconnectedSpace.mpr inferInstance
  · exact hA

end HodgeLean.Foundations.Program
