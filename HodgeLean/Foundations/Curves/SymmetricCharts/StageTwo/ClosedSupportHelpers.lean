import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Defs
import HodgeLean.Foundations.Program.SchoenReducedClosedImages
import HodgeLean.Foundations.Program.SchoenSelectedGeometryReducedImage
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Detection and transport of reduced subschemes by their actual support

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

/-- Complex points detect inclusion between closed subsets of a finite-type complex scheme.
Source: Hartshorne, Algebraic Geometry, II.3, Jacobson schemes over an algebraically closed field.
HC no distance; AV milestone no distance.
-/
theorem closed_subset_of_complex_points (B : Over (Spec ↧ℂ)) [LocallyOfFiniteType B.hom]
    (S T : TopologicalSpace.Closeds B.left)
    (h : ∀ p : ComplexPoint B, p.underlying ∈ S → p.underlying ∈ T) : S ≤ T := by
  letI : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  intro x hx
  by_contra hxt
  have hloc : IsLocallyClosed ((S : Set B.left) ∩ (T : Set B.left)ᶜ) :=
    S.isClosed.isLocallyClosed.inter T.isClosed.isOpen_compl.isLocallyClosed
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints
    (Z := (S : Set B.left) ∩ (T : Set B.left)ᶜ) ⟨x, hx, hxt⟩ hloc
  let p : ComplexPoint B := Over.homMk (pointOfClosedPoint B.hom y hc) (by simp)
  have hp : p.underlying = y := pointOfClosedPoint_apply B.hom y hc _
  have H := h p (by rw [hp]; exact hy.1)
  rw [hp] at H
  exact hy.2 H

/-- A radical ideal gives the reduced subscheme with exactly its support.
Source: Hartshorne, Algebraic Geometry, II.5, reduced induced subscheme.
HC no distance; AV milestone no distance.
-/
theorem subscheme_reduced_of_radical (X : Scheme.{0}) (I : X.IdealSheafData)
    (hI : I.radical = I) : IsReduced I.subscheme := by
  have hEq : I = Scheme.IdealSheafData.vanishingIdeal I.support :=
    (Scheme.IdealSheafData.vanishingIdeal_support.trans hI).symm
  rw [hEq]
  exact s0_vanishing_subscheme_reduced X I.support

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
