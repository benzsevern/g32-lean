import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProperReducedComparison
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProperDominantPoints
import HodgeLean.Foundations.Program.SchoenSelectedGeometryReducedImage

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A proper complex-point bijection onto a normal integral target has a closed immersion section covering every complex point, allowing a nonreduced source. -/
theorem proper_normal_point_bijective_section
    (X Y : Over (Spec ↧ℂ)) [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (hY : zmtiso_IsNormal Y.left)
    (hbij : Function.Bijective (Point.map f)) :
    ∃ j : Y ⟶ X, IsClosedImmersion j.left ∧ j ≫ f = 𝟙 Y ∧
      ∀ x : ComplexPoint X, Point.map j (Point.map f x) = x := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds X.left)
  let U : Over (Spec ↧ℂ) := Over.mk (I.subschemeι ≫ X.hom)
  let i : U ⟶ X := Over.homMk I.subschemeι rfl
  haveI : IsReduced U.left := s0_vanishing_subscheme_reduced X.left ⊤
  haveI : IsClosedImmersion i.left := by
    change IsClosedImmersion I.subschemeι
    infer_instance
  haveI : LocallyOfFiniteType U.hom := by
    change LocallyOfFiniteType (I.subschemeι ≫ X.hom)
    infer_instance
  have hrange : Set.range i.left = Set.univ := by
    change Set.range I.subschemeι = _
    rw [I.range_subschemeι]
    rfl
  haveI : IsDominant i.left := by
    rw [isDominant_iff, denseRange_iff_closure_range, hrange, closure_univ]
  have hisurj : Function.Surjective (Point.map i) := proper_dominant_complex_points_surjective i
  haveI : Mono i := Over.mono_of_mono_left i
  have hiinj : Function.Injective (Point.map i) := by
    intro x y h
    exact (cancel_mono i).mp h
  let q := i ≫ f
  haveI : IsProper q.left := by
    change IsProper (i.left ≫ f.left)
    infer_instance
  haveI : IsIso q.left := proper_reduced_point_bijective_isIso U Y q hY
    (hbij.comp ⟨hiinj, hisurj⟩)
  let E : U ≅ Y := Over.isoMk (asIso q.left) q.w
  have hE : E.hom = q := by apply Over.OverMorphism.ext; rfl
  let j := E.inv ≫ i
  have hj : j ≫ f = 𝟙 Y := by
    change E.inv ≫ q = _
    rw [← hE]
    exact E.inv_hom_id
  refine ⟨j, ?_, hj, ?_⟩
  · change IsClosedImmersion (E.inv.left ≫ i.left)
    infer_instance
  · intro x
    apply hbij.injective
    rw [← Point.map_comp_apply, hj, Point.map_id]

end AlgebraicGeometry.RamifiedNormalization.StageFour
