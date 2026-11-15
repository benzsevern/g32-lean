import HodgeLean.Foundations.QuotientDuality.ProperCycleCofinalTruncation

/-! # Cofinal actual finite marked models in the original space -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology TopologicalSpace HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

/-- A retained polynomial chart supplies finite marked neighborhood models inside any requested original open.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry, theorem 9.2.1;
Munkres, Topology, sections 18 and 20.
HC no distance; AV milestone no distance. -/
lemma properCycle_cofinal_marked_chart_model {X : Type} [TopologicalSpace X] {r : ℕ}
    {D : Fin r → Set X} (c : Marked.SubsetChart X D) (x : c.domain)
    (P : Opens X) (hxP : x.val ∈ P) :
    ∃ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (c.n + c.n)))),
      K.faces.Finite ∧ ∃ f : K.space → X, IsEmbedding f ∧
        IsCompact (Set.range f) ∧ Set.range f ⊆ P ∧ Set.range f ∈ 𝓝 x.val ∧
          ∀ j : Fin r, ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (c.n + c.n))),
            L.faces.Finite ∧ L.faces ⊆ K.faces ∧
              ∀ z : K.space, f z ∈ D j ↔ z.val ∈ L.space := by
  let center := complexEuclideanCoordinates c.n (c.coordinates x).val
  obtain ⟨R, hR, hinside⟩ := properCycle_chart_closed_ball_inside c.toChart x P hxP
  obtain ⟨K, hK, h, hmarks⟩ := properCycle_marked_chart_truncation c center R hR.le
  let f : K.space → X := fun z => (h z).val.val
  have hf : IsEmbedding f :=
    IsEmbedding.subtypeVal.comp (IsEmbedding.subtypeVal.comp h.isEmbedding)
  have hcompact : IsCompact K.space :=
    hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp hcompact
  have hrange : IsCompact (Set.range f) := isCompact_range hf.continuous
  have hsub : Set.range f ⊆ P := by
    rintro _ ⟨z, rfl⟩
    exact hinside (h z).val (h z).property
  let W : Set c.domain := {z | complexEuclideanCoordinates c.n (c.coordinates z).val ∈
    Metric.ball center R}
  have hW : IsOpen W := Metric.isOpen_ball.preimage
    ((complexEuclideanCoordinates c.n).continuous.comp
      (continuous_subtype_val.comp c.coordinates.continuous))
  have hxW : x ∈ W := Metric.mem_ball_self hR
  have hnb : Subtype.val '' W ∈ 𝓝 x.val :=
    c.domain.isOpen.isOpenMap_subtype_val.image_mem_nhds (hW.mem_nhds hxW)
  have hWsub : Subtype.val '' W ⊆ Set.range f := by
    rintro _ ⟨z, hz, rfl⟩
    let t : {z : c.domain | complexEuclideanCoordinates c.n (c.coordinates z).val ∈
        Metric.closedBall center R} := ⟨z, Metric.ball_subset_closedBall hz⟩
    refine ⟨h.symm t, ?_⟩
    exact congrArg (fun a => a.val.val) (h.apply_symm_apply t)
  exact ⟨K, hK, f, hf, hrange, hsub, Filter.mem_of_superset hnb hWsub, hmarks⟩

end HodgeLean.Foundations.QuotientDuality
