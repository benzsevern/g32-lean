import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.PointChartLifts

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A specified actual open chart identifies its point fibre with exactly the chart-image locus in the original point fibre. -/
theorem open_chart_fibre_range_homeomorph
    {U X B : Over (Spec ↧ℂ)} (p : X ⟶ B) (j : U ⟶ X) [IsOpenImmersion j.left]
    (q : U ⟶ B) (hq : j ≫ p = q) (x : ComplexPoint B) :
    ∃ H : {u : ComplexPoint U // Point.map q u = x} ≃ₜ
        {z : {z : ComplexPoint X // Point.map p z = x} //
          z.val.left (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left},
      ∀ u, (H u).val.val = Point.map j u.val := by
  have hj := HodgeLean.Foundations.ComplexTopology.openImmersion_points j
  have hcomm (u : ComplexPoint U) : Point.map p (Point.map j u) = Point.map q u := by
    rw [← Point.map_comp_apply, hq]
  let g : {u : ComplexPoint U // Point.map q u = x} →
      {z : ComplexPoint X // Point.map p z = x} :=
    fun u => ⟨Point.map j u.val, (hcomm u.val).trans u.property⟩
  let f : {u : ComplexPoint U // Point.map q u = x} →
      {z : {z : ComplexPoint X // Point.map p z = x} //
        z.val.left (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left} :=
    fun u => ⟨g u, ⟨u.val.left (IsLocalRing.closedPoint ℂ), rfl⟩⟩
  have hinj : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    exact hj.injective (congrArg (fun z => z.val.val) h)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨u, hu⟩ := complex_point_lifts_open_chart j z.val.val z.property
    have hqu : Point.map q u = x := by
      rw [← hcomm u, hu]
      exact z.val.property
    refine ⟨⟨u, hqu⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hu
  have hbase : Topology.IsEmbedding (fun u : {u : ComplexPoint U // Point.map q u = x} =>
      Point.map j u.val) := hj.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hg : Topology.IsEmbedding g := hbase.codRestrict _
    (fun u => (hcomm u.val).trans u.property)
  have hf : Topology.IsEmbedding f := hg.codRestrict
    {z : {z : ComplexPoint X // Point.map p z = x} |
      z.val.left (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left}
    (fun u => ⟨u.val.left (IsLocalRing.closedPoint ℂ), rfl⟩)
  let H := (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfIsInducing hf.isInducing
  exact ⟨H, fun _ => rfl⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
