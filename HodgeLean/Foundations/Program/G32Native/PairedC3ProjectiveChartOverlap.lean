import HodgeLean.Foundations.Program.G32Native.PairedC3RatioNormalization
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineReciprocalPoints
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Agreement of the normalized residual maps into the projective line -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- Opposite normalized affine parameters give equal scheme morphisms into
the projective line on a reduced finite-type overlap. The equality is of
morphisms, rather than just a comparison of complex-point coordinates.
Source: Hartshorne, Algebraic Geometry, II.2 and II.7.13. -/
theorem pairedC3_projective_normalized_overlap
    {B : Type} [CommRing B] [Algebra ℂ B]
    [IsReduced (Spec (CommRingCat.of B))]
    [LocallyOfFiniteType (ComplexPoint.affineSpecStructureMap B)]
    [IsSeparated projectiveLine.hom] [LocallyOfFiniteType projectiveLine.hom]
    (α : Bˣ) (s t : B) (hst : s * t = 1) :
    projectiveLineChart 1 ((↑α⁻¹ : B) * t) =
      projectiveLineChart 0 ((↑α : B) * s) := by
  letI : IsReduced (Over.mk (ComplexPoint.affineSpecStructureMap B)).left :=
    (inferInstance : IsReduced (Spec (CommRingCat.of B)))
  let f := projectiveLineChart 1 ((↑α⁻¹ : B) * t)
  let g := projectiveLineChart 0 ((↑α : B) * s)
  have hm : Point.map f = Point.map g := by
    funext p
    apply projectiveLineChart_reciprocal_points
    rw [← map_mul, mul_comm]
    rw [pairedC3_normalized_overlap α s t hst, map_one]
  apply Over.OverMorphism.ext
  have hf : f.left ≫ projectiveLine.hom = ComplexPoint.affineSpecStructureMap B := Over.w f
  have hg : g.left ≫ projectiveLine.hom = ComplexPoint.affineSpecStructureMap B := Over.w g
  letI : LocallyOfFiniteType (f.left ≫ projectiveLine.hom) := by rw [hf]; infer_instance
  apply ext_of_apply_eq (K := ℂ) projectiveLine.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ ?_ (hf.trans hg.symm)
  intro x _ hx
  obtain ⟨a⟩ : Nonempty (Spec ↧ℂ) := inferInstance
  rw [← pointOfClosedPoint_apply (ComplexPoint.affineSpecStructureMap B) x hx a]
  have hp := congrArg (fun z => z.left)
    (congrFun hm (Over.homMk
      (pointOfClosedPoint (ComplexPoint.affineSpecStructureMap B) x hx)
      (by simp)))
  exact congrArg (fun φ : Spec ↧ℂ ⟶ projectiveLine.left => φ a) hp

#print axioms pairedC3_projective_normalized_overlap
end HodgeLean.Foundations.Program.G32Native
