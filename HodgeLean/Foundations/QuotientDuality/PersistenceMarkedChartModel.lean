import HodgeLean.Foundations.QuotientDuality.PersistenceComplexTruncationModel
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.MarkedDefs

/-! Compact Boolean models on actual marked chart truncations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Foundations.Program HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_marked_chart_truncation_model
    {X : Type} [TopologicalSpace X] {s : ℕ} {D : Fin s → Set X}
    (c : Marked.SubsetChart X D) (j : Fin s)
    (a : EuclideanSpace ℝ (Fin (c.n + c.n))) (r : ℝ) (hr : 0 ≤ r) :
    let V : Set c.domain := {x | complexEuclideanCoordinates c.n (c.coordinates x).val ∈
      Metric.closedBall a r}
    ∃ f b : s2v_t11b_Formula (c.n + c.n), IsCompact f.realize ∧
      IsClosed (Subtype.val ⁻¹' b.realize : Set f.realize) ∧
      ∃ e : V ≃ₜ f.realize, ∀ x : V, (e x).val ∈ b.realize ↔ x.val.val ∈ D j := by
  let V : Set c.domain := {x | complexEuclideanCoordinates c.n (c.coordinates x).val ∈
    Metric.closedBall a r}
  let T := zeroSet c.equations ∩
    (complexEuclideanCoordinates c.n) ⁻¹' Metric.closedBall a r
  obtain ⟨f, b, hf, hb, e, hmark⟩ :=
    persistence_complex_equation_truncation_model c.equations (c.marked j) a r hr
  let back : C(T, zeroSet c.equations) :=
    ⟨fun z => ⟨z.val, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩
  let eVT : V ≃ₜ T := {
    toFun := fun x => ⟨(c.coordinates x.val).val,
      (c.coordinates x.val).property, x.property⟩
    invFun := fun z => ⟨c.coordinates.symm (back z), by
      change complexEuclideanCoordinates c.n
        (c.coordinates (c.coordinates.symm (back z))).val ∈ Metric.closedBall a r
      rw [c.coordinates.apply_symm_apply]
      exact z.property.2⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact c.coordinates.symm_apply_apply x.val
    right_inv := by
      intro z
      exact Subtype.ext (congrArg (fun w : zeroSet c.equations => w.val)
        (c.coordinates.apply_symm_apply (back z)))
    continuous_toFun := (continuous_subtype_val.comp
      (c.coordinates.continuous.comp continuous_subtype_val)).subtype_mk _
    continuous_invFun := (c.coordinates.symm.continuous.comp back.continuous).subtype_mk (by
      intro z
      change complexEuclideanCoordinates c.n
        (c.coordinates (c.coordinates.symm (back z))).val ∈ Metric.closedBall a r
      rw [c.coordinates.apply_symm_apply]
      exact z.property.2) }
  refine ⟨f, b, hf, hb, eVT.trans e, ?_⟩
  intro x
  change (e (eVT x)).val ∈ b.realize ↔ x.val.val ∈ D j
  rw [hmark]
  exact (c.membership x.val j).symm

lemma persistence_marked_chart_truncation_mem_nhds
    {X : Type} [TopologicalSpace X] {s : ℕ} {D : Fin s → Set X}
    (c : Marked.SubsetChart X D) (x : c.domain) (r : ℝ) (hr : 0 < r) :
    {y : c.domain | complexEuclideanCoordinates c.n (c.coordinates y).val ∈
      Metric.closedBall (complexEuclideanCoordinates c.n (c.coordinates x).val) r} ∈
        nhds x := by
  have hc : Continuous (fun y : c.domain =>
      complexEuclideanCoordinates c.n (c.coordinates y).val) :=
    (complexEuclideanCoordinates c.n).continuous.comp
      (continuous_subtype_val.comp c.coordinates.continuous)
  exact hc.continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr)

end HodgeLean.Foundations.QuotientDuality
