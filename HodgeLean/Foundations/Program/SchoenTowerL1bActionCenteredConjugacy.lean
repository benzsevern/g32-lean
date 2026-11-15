import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A chart translated so that its specified point has coordinate zero. -/
def s2v_l1b_action_centerChart {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) (x : M) : OpenPartialHomeomorph M ℂ :=
  e.trans (Homeomorph.subRight (e x)).toOpenPartialHomeomorph

/-- Translation preserves the source of a chart. -/
theorem s2v_l1b_action_centerChart_source {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) (x : M) :
    (s2v_l1b_action_centerChart e x).source = e.source := by
  change e.source ∩ e ⁻¹' Set.univ = e.source
  rw [Set.preimage_univ, Set.inter_univ]

/-- The distinguished point has coordinate zero in the translated chart. -/
theorem s2v_l1b_action_centerChart_zero {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) (x : M) :
    s2v_l1b_action_centerChart e x x = 0 := sub_self _

/-- The centered coordinate representative of a homeomorphism is an actual
partial homeomorphism of the plane. -/
def s2v_l1b_action_centeredConjugacy
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M ℂ) (d : OpenPartialHomeomorph N ℂ)
    (E : M ≃ₜ N) (x : M) : OpenPartialHomeomorph ℂ ℂ :=
  (s2v_l1b_action_centerChart e x).symm.trans
    (E.toOpenPartialHomeomorph.trans (s2v_l1b_action_centerChart d (E x)))

/-- The coordinate representative is defined at the origin. -/
theorem s2v_l1b_action_centeredConjugacy_source
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M ℂ) (d : OpenPartialHomeomorph N ℂ)
    (E : M ≃ₜ N) (x : M) (he : x ∈ e.source) (hd : E x ∈ d.source) :
    0 ∈ (s2v_l1b_action_centeredConjugacy e d E x).source := by
  let C := s2v_l1b_action_centerChart e x
  have hx : x ∈ C.source := by rwa [s2v_l1b_action_centerChart_source]
  have hz : C x = 0 := s2v_l1b_action_centerChart_zero e x
  have hi : C.symm 0 = x := by rw [← hz, C.left_inv hx]
  refine ⟨?_, ?_⟩
  · change 0 ∈ C.target
    rw [← hz]
    exact C.map_source hx
  · change C.symm 0 ∈ Set.univ ∩ E ⁻¹' (s2v_l1b_action_centerChart d (E x)).source
    rw [hi]
    exact ⟨Set.mem_univ _, by rwa [s2v_l1b_action_centerChart_source]⟩

/-- The actual coordinate representative fixes the origin. -/
theorem s2v_l1b_action_centeredConjugacy_zero
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M ℂ) (d : OpenPartialHomeomorph N ℂ)
    (E : M ≃ₜ N) (x : M) (he : x ∈ e.source) :
    s2v_l1b_action_centeredConjugacy e d E x 0 = 0 := by
  change d (E (e.symm (0 + e x))) - d (E x) = 0
  rw [zero_add, e.left_inv he, sub_self]

/-- A centered partial homeomorphism has an actual punctured disk on which
it is continuous and avoids zero away from the origin. -/
theorem s2v_l1b_action_centered_partial_disk
    (H : OpenPartialHomeomorph ℂ ℂ) (h0 : 0 ∈ H.source) (hz : H 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ H.source ∧
      ContinuousOn H (Metric.ball 0 r) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → H z ≠ 0 := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp (H.open_source.mem_nhds h0)
  refine ⟨r, hr, hb, H.continuousOn.mono hb, ?_⟩
  intro z hzb hzne hzero
  apply hzne
  exact H.injOn (hb hzb) h0 (hzero.trans hz.symm)

/-- An actual conjugacy intertwines the chart representatives on a
neighbourhood of the fixed point, with all partial inverse domains checked. -/
theorem s2v_l1b_action_chart_conjugacy_eventually
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (C : OpenPartialHomeomorph M ℂ) (D : OpenPartialHomeomorph N ℂ)
    (E : M ≃ₜ N) (x : M) (hx : x ∈ C.source) (hy : E x ∈ D.source)
    (f : M → M) (q : N → N) (hf : ContinuousAt f x) (hfix : f x = x)
    (hequiv : ∀ y, q (E y) = E (f y)) :
    let H := C.symm.trans (E.toOpenPartialHomeomorph.trans D)
    ∀ᶠ z : ℂ in 𝓝 (C x),
      H (C (f (C.symm z))) = D (q (D.symm (H z))) := by
  dsimp only
  have hci := C.continuousAt_symm (C.map_source hx)
  have hft : Tendsto (fun z => f (C.symm z)) (𝓝 (C x)) (𝓝 x) := by
    have hf' : ContinuousAt f (C.symm (C x)) := by rwa [C.left_inv hx]
    simpa only [Function.comp_def, C.left_inv hx, hfix] using (hf'.comp hci).tendsto
  have hEt : Tendsto (fun z => E (C.symm z)) (𝓝 (C x)) (𝓝 (E x)) := by
    simpa only [Function.comp_def, C.left_inv hx] using (E.continuous.continuousAt.comp hci).tendsto
  filter_upwards [hft.eventually (C.open_source.mem_nhds hx),
    hEt.eventually (D.open_source.mem_nhds hy)] with z hfz hEz
  change D (E (C.symm (C (f (C.symm z))))) =
    D (q (D.symm (D (E (C.symm z)))))
  rw [C.left_inv hfz, D.left_inv hEz, hequiv]

end HodgeLean.Foundations.Program
