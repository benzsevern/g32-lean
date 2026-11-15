import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- Any supplied algebraic étale coordinates give an analytic chart with analytic inverse in the native manifold.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_etale_analytic_coordinate_chart
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (D : LocalEtaleCoordinates X d p.underlying) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ),
      p ∈ e.source ∧
      (∀ q, q ∈ e.source → ∀ i,
        e q i = Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i) q) ∧
      AnalyticAt ℂ (fun v => e ((ComplexPoint.localChart X d p).symm v))
        (ComplexPoint.localChart X d p p) ∧
      AnalyticAt ℂ (fun v => ComplexPoint.localChart X d p (e.symm v)) (e p) := by
  let z : {q : ComplexPoint X // q ∈ Point.overOpen D.neighborhood} := ⟨p, D.mem⟩
  let E := D.ambientProjectionChart z
  let e := E.lift_openEmbedding
    (Point.isOpen_overOpen (X := X) D.neighborhood).isOpenEmbedding_subtypeVal
  have hp : p ∈ e.source := ⟨z, D.mem_ambientProjectionChart_source z, rfl⟩
  have hev (q : ComplexPoint X) (hq : q ∈ e.source) (i : Fin d) :
      e q i = Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i) q := by
    obtain ⟨q', hq', rfl⟩ := hq
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply,
      D.ambientProjectionChart_apply_of_mem z q' hq']
    exact D.ambientAnalyticCoordinates_apply_eq_evaluate q' i
  let C := ComplexPoint.localChart X d p
  have hpC : p ∈ C.source := ComplexPoint.mem_localChart_source X d p
  have hCp : C.symm (C p) = p := C.left_inv hpC
  have heU (q : ComplexPoint X) (hq : q ∈ e.source) : q ∈ Point.overOpen D.ambientCoordinateOpen := by
    obtain ⟨q', hq', rfl⟩ := hq
    simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top] using q'.property
  have hf : AnalyticAt ℂ (fun v => e (C.symm v)) (C p) := by
    apply AnalyticAt.pi
    intro i
    have ha := ComplexPoint.analyticAt_localChart_symm_evaluate X d p
      (C.map_source hpC) D.ambientCoordinateOpen (D.ambientCoordinateSection i)
      (by rw [hCp]; exact heU p hp)
    apply ha.congr
    have hn : ∀ᶠ v in 𝓝 (C p), C.symm v ∈ e.source := by
      have ht := (C.continuousAt_symm (C.map_source hpC)).tendsto
      rw [hCp] at ht
      exact ht (e.open_source.mem_nhds hp)
    filter_upwards [hn] with v hv
    exact (hev _ hv i).symm
  have hi : AnalyticAt ℂ (fun v => C (e.symm v)) (e p) := by
    apply AnalyticAt.pi
    intro i
    let D0 := ComplexPoint.localEtaleCoordinates X d p
    have hU0 : p ∈ Point.overOpen D0.ambientCoordinateOpen := by
      simpa only [D0, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top]
        using ComplexPoint.mem_localEtaleCoordinates X d p
    have ha := D.analyticAt_ambientProjectionChart_symm_evaluate z
      (show e p ∈ E.target from e.map_source hp)
      D0.ambientCoordinateOpen (D0.ambientCoordinateSection i)
      (by change e.symm (e p) ∈ _; rw [e.left_inv hp]; exact hU0)
    apply ha.congr
    have hn : ∀ᶠ v in 𝓝 (e p), e.symm v ∈ C.source := by
      have ht := (e.continuousAt_symm (e.map_source hp)).tendsto
      rw [e.left_inv hp] at ht
      exact ht (C.open_source.mem_nhds hpC)
    filter_upwards [hn] with v hv
    exact (ComplexPoint.localChart_apply_component_eq_evaluate X d p (e.symm v) hv i).symm
  exact ⟨e, hp, hev, hf, hi⟩

#print axioms s2e_etale_analytic_coordinate_chart
end HodgeLean.Foundations.Program
