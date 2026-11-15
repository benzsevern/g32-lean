import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.PointChartLifts

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- An open chart square containing an entire actual fibre identifies its local and global point fibres. -/
theorem open_chart_point_fibre_homeomorph
    {U X V B : Over (Spec ↧ℂ)}
    (p : X ⟶ B) (q : U ⟶ V) (i : U ⟶ X) (j : V ⟶ B)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (hsq : i ≫ p = q ≫ j) (y : ComplexPoint V)
    (hcover : ∀ x : ComplexPoint X, Point.map p x = Point.map j y →
      x.left (IsLocalRing.closedPoint ℂ) ∈ Set.range i.left) :
    ∃ e : {u : ComplexPoint U // Point.map q u = y} ≃ₜ
        {x : ComplexPoint X // Point.map p x = Point.map j y},
      ∀ u, (e u).val = Point.map i u.val := by
  have hi := HodgeLean.Foundations.ComplexTopology.openImmersion_points i
  have hj := HodgeLean.Foundations.ComplexTopology.openImmersion_points j
  have hcomm (u : ComplexPoint U) :
      Point.map p (Point.map i u) = Point.map j (Point.map q u) := by
    rw [← Point.map_comp_apply, hsq, Point.map_comp_apply]
  let f : {u : ComplexPoint U // Point.map q u = y} →
      {x : ComplexPoint X // Point.map p x = Point.map j y} :=
    fun u => ⟨Point.map i u.val, (hcomm u.val).trans (congrArg (Point.map j) u.property)⟩
  have hinj : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    exact hi.injective (congrArg Subtype.val he)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨u, hu⟩ := complex_point_lifts_open_chart i x.val (hcover x.val x.property)
    have hqy : Point.map q u = y := by
      apply hj.injective
      rw [← hcomm, hu]
      exact x.property
    exact ⟨⟨u, hqy⟩, Subtype.ext hu⟩
  let e : {u : ComplexPoint U // Point.map q u = y} ≃ₜ
      {u : ComplexPoint U // Point.map p (Point.map i u) = Point.map j y} :=
    (Homeomorph.refl _).subtype (fun u => by
      change Point.map q u = y ↔ Point.map p (Point.map i u) = Point.map j y
      rw [hcomm]
      exact hj.injective.eq_iff.symm)
  have hopen : Topology.IsOpenEmbedding f :=
    (hi.restrictPreimage {x : ComplexPoint X | Point.map p x = Point.map j y}).comp e.isOpenEmbedding
  let H := (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen
    hopen.continuous hopen.isOpenMap
  exact ⟨H, fun _ => rfl⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
