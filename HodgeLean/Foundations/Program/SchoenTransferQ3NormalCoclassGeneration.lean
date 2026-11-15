import HodgeLean.Foundations.Program.SchoenTransferQ3NormalCoclassTransport

/-! Scalar detection on the actual flattened support neighbourhood. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Evaluation on the actual normal homology class gives the coefficient of every
supported coclass on the flattened neighbourhood. -/
theorem s4_q3_normal_coclass_coefficient
    {M : Type} [TopologicalSpace M]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)
    (α : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S)
      (2 * c)) :
    α = (relativeCohomologyEquivDualHomology ℚ
      (neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S)
      (2 * c) α (flattenedSupportNormalClass E c e x hx S hS h0)) •
      chartNormalProjectionCoclass E c e S hS (flattenedSupportNeighborhood E c e x hx)
        (flattenedSupportNeighborhood_subset_source E c e x hx) := by
  apply (relativeCohomologyEquivDualHomology ℚ
    (neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S)
    (2 * c)).injective
  ext v
  obtain ⟨r, rfl⟩ := (Submodule.span_singleton_eq_top_iff ℚ
    (flattenedSupportNormalClass E c e x hx S hS h0)).mp
      (span_flattenedSupportNormalClass_eq_top E c e S hS x hx h0) v
  simp only [map_smul, LinearMap.smul_apply,
    chartNormalProjectionCoclass_apply_normalClass, smul_eq_mul]
  ring

/-- A map retaining normal coordinates detects supported coclasses whenever
both neighbourhoods carry their actual flattened normal generators. -/
theorem s4_q3_normal_coordinate_pullback_injective
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (d : OpenPartialHomeomorph N (F × (Fin c → ℂ)))
    (S : Set M) (T : Set N)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hT : ∀ y ∈ d.source, y ∈ T ↔ (d y).2 = 0)
    (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)
    (z : N) (hz : z ∈ d.source) (hz0 : (d z).2 = 0)
    (φ : neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S ⟶
      neighborhoodSupportComplementPair (flattenedSupportNeighborhood F c d z hz) T)
    (hnormal : φ ≫ chartNormalProjectionPair F c d T hT
      (flattenedSupportNeighborhood F c d z hz)
      (flattenedSupportNeighborhood_subset_source F c d z hz) =
      chartNormalProjectionPair E c e S hS (flattenedSupportNeighborhood E c e x hx)
        (flattenedSupportNeighborhood_subset_source E c e x hx)) :
    Function.Injective (relativeCohomologyMap ℚ (2 * c) φ) := by
  have htransport : relativeCohomologyMap ℚ (2 * c) φ
      (chartNormalProjectionCoclass F c d T hT (flattenedSupportNeighborhood F c d z hz)
        (flattenedSupportNeighborhood_subset_source F c d z hz)) =
      chartNormalProjectionCoclass E c e S hS (flattenedSupportNeighborhood E c e x hx)
        (flattenedSupportNeighborhood_subset_source E c e x hx) := by
    unfold chartNormalProjectionCoclass
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hnormal]
  have hne : chartNormalProjectionCoclass E c e S hS
      (flattenedSupportNeighborhood E c e x hx)
      (flattenedSupportNeighborhood_subset_source E c e x hx) ≠ 0 := by
    intro heq
    have h := chartNormalProjectionCoclass_apply_normalClass E c e S hS x hx h0
    rw [heq, map_zero, LinearMap.zero_apply] at h
    exact zero_ne_one h
  intro α β hab
  have hα := s4_q3_normal_coclass_coefficient F c d T hT z hz hz0 α
  have hβ := s4_q3_normal_coclass_coefficient F c d T hT z hz hz0 β
  rw [hα, hβ, map_smul, map_smul, htransport] at hab
  have hc := smul_left_injective ℚ hne hab
  rw [hα, hβ, hc]

end HodgeLean.Foundations.Program
