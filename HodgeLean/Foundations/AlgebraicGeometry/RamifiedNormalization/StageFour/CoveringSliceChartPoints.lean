import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CompositeSlicePoints
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OpenChartFibreRange

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual normal chart point fibre identifies exactly the covering-slice locus above its specified base chart. -/
theorem covering_slice_chart_point_homeomorph
    {U V W B' B : Over (Spec ↧ℂ)} [IsSeparated B.hom]
    (β : W ⟶ B') (b : B' ⟶ B) (x : ComplexPoint B)
    (i : U ⟶ W) [IsOpenImmersion i.left] (j : V ⟶ B')
    (hirange : Set.range i.left = β.left ⁻¹' Set.range j.left) :
    ∃ H : {u : ComplexPoint U // Point.map (i ≫ β ≫ b) u = x} ≃ₜ
        {z : ComplexPoint (coveringSlice β b x) //
          (Point.map (pullback.fst b x) (Point.map (sliceProjection β b x) z)).left
            (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left},
      ∀ u, Point.map (pullback.fst β (pullback.fst b x)) (H u).val = Point.map i u.val := by
  let H₀ := coveringSlicePointHomeomorph β b x
  obtain ⟨Hlocal, hHlocal⟩ := open_chart_fibre_range_homeomorph (β ≫ b) i
    (i ≫ β ≫ b) rfl x
  have hβpoint (z : ComplexPoint (coveringSlice β b x)) :
      Point.map β (H₀ z).val = Point.map (pullback.fst b x)
        (Point.map (sliceProjection β b x) z) := by
    rw [coveringSlicePointHomeomorph_projection, ← Point.map_comp_apply,
      ← Point.map_comp_apply]
    exact congrArg (fun f => Point.map f z) (pullback.condition (f := β) (g := pullback.fst b x))
  let Hrange : {z : ComplexPoint (coveringSlice β b x) //
        (Point.map (pullback.fst b x) (Point.map (sliceProjection β b x) z)).left
          (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left} ≃ₜ
      {w : {w : ComplexPoint W // Point.map (β ≫ b) w = x} //
        w.val.left (IsLocalRing.closedPoint ℂ) ∈ Set.range i.left} :=
    H₀.subtype (fun z => by
      rw [hirange]
      change (Point.map (pullback.fst b x) (Point.map (sliceProjection β b x) z)).left
          (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left ↔
        β.left ((H₀ z).val.left (IsLocalRing.closedPoint ℂ)) ∈ Set.range j.left
      have he := congrArg (fun a : ComplexPoint B' => a.left (IsLocalRing.closedPoint ℂ)) (hβpoint z)
      change β.left ((H₀ z).val.left (IsLocalRing.closedPoint ℂ)) = _ at he
      rw [he])
  refine ⟨Hlocal.trans Hrange.symm, ?_⟩
  intro u
  have he := congrArg (fun w => w.val.val) (Hrange.apply_symm_apply (Hlocal u))
  change (H₀ (Hrange.symm (Hlocal u)).val).val = (Hlocal u).val.val at he
  rw [coveringSlicePointHomeomorph_projection, hHlocal] at he
  exact he

end AlgebraicGeometry.RamifiedNormalization.StageFour
