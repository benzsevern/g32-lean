import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ChartSliceMaps

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A complex point in the image of an actual open immersion lifts to a complex point of that chart. -/
theorem complex_point_lifts_open_chart
    {X Y : Over (Spec ↧ℂ)} (j : X ⟶ Y) [IsOpenImmersion j.left]
    (z : ComplexPoint Y)
    (hz : z.left (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left) :
    ∃ a : ComplexPoint X, Point.map j a = z := by
  have hrange : Set.range z.left ⊆ Set.range j.left := by
    rintro y ⟨s, rfl⟩
    have hs : s = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := Spec ↧ℂ) _ _
    subst s
    exact hz
  let l := IsOpenImmersion.lift j.left z.left hrange
  have hl : l ≫ j.left = z.left := IsOpenImmersion.lift_fac _ _ _
  have hscalar : l ≫ X.hom = 𝟙 (Spec ↧ℂ) := by
    rw [← j.w, ← Category.assoc, hl]
    exact z.w
  refine ⟨Over.homMk l hscalar, ?_⟩
  apply Over.OverMorphism.ext
  exact hl

/-- The literal ratio chart covers exactly the actual point fibre above its scheme-theoretic open image. -/
theorem mem_range_affineChartSliceMap
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0)
    (X : Over (Spec ↧ℂ))
    (p : X ⟶ Over.mk (ComplexPoint.affineSpecStructureMap R))
    (j : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)) ⟶ X)
    [IsOpenImmersion j.left]
    (hj : ∀ a, Point.map p (Point.map j a) =
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) a)
    (x : {x : ComplexPoint X // Point.map p x = (ComplexPoint.affineSpecEquiv R).symm φ}) :
    x ∈ Set.range (affineChartSliceMap u v φ hu hv X p j hj) ↔
      x.val.left (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left := by
  let H := affineChartPointFibreHomeomorph u v φ hu hv
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(H.symm z).val.left (IsLocalRing.closedPoint ℂ), rfl⟩
  · intro hx
    obtain ⟨a, ha⟩ := complex_point_lifts_open_chart j x.val hx
    have hpa : Point.map p (Point.map j a) = (ComplexPoint.affineSpecEquiv R).symm φ :=
      (congrArg (Point.map p) ha).trans x.property
    have hbase := (hj a).symm.trans hpa
    let aF := (⟨a, hbase⟩ : {a : ComplexPoint (Over.mk
      (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v))) //
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) a =
        (ComplexPoint.affineSpecEquiv R).symm φ})
    refine ⟨H aF, ?_⟩
    apply Subtype.ext
    change Point.map j ((H.symm (H aF)).val) = x.val
    rw [H.symm_apply_apply]
    exact ha

end AlgebraicGeometry.RamifiedNormalization.StageFour
