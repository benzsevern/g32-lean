import HodgeLean.Adapters.NormalConeB4aClassNormalization
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionOverlap

/-! # Normal homology generators inside prescribed neighborhoods

A normal generator can be represented in any open neighborhood of its base
point. This permits a local chart normalization to compute the evaluation on
the fixed flattened-support generator.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicTopology.Singular

/-- A normal disk inside any prescribed neighborhood represents the fixed normal generator. -/
theorem a3b4a_gysin_normalClass_from_small_disk
    {M : Type} [TopologicalSpace M] {r c : ℕ}
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin c → ℂ)))
    (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)
    (W : Set M) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ (V : Set (Fin c → ℂ))
      (hV : ∀ v ∈ V, ((e x).1, v) ∈ e.target ∧
        e.symm ((e x).1, v) ∈ flattenedSupportNeighborhood (Fin r → ℂ) c e x hx),
      IsOpen V ∧ (0 : Fin c → ℂ) ∈ V ∧
      (∀ v ∈ V, e.symm ((e x).1, v) ∈ W) ∧
      ∃ z : RelativeHomology ℚ (neighborhoodPointComplementPair V 0) (2 * c),
        relativeHomologyMap ℚ (2 * c) (neighborhoodPointComplementPairMap V 0) z =
          standardComplexLocalClass ℚ c ∧
        relativeHomologyMap ℚ (2 * c)
          (chartNormalFiberPair c e S hS (e x).1
            (flattenedSupportNeighborhood (Fin r → ℂ) c e x hx) V hV) z =
          flattenedSupportNormalClass (Fin r → ℂ) c e x hx S hS h0 := by
  let W₀ := flattenedSupportNeighborhood (Fin r → ℂ) c e x hx
  let V : Set (Fin c → ℂ) :=
    {v | ((e x).1, v) ∈ e.target ∧ e.symm ((e x).1, v) ∈ W ∩ W₀}
  have hVo : IsOpen V :=
    (e.isOpen_inter_preimage_symm (hW.inter W₀.isOpen)).preimage
      (continuous_const.prodMk continuous_id)
  have heq : ((e x).1, (0 : Fin c → ℂ)) = e x := Prod.ext rfl h0.symm
  have h0V : (0 : Fin c → ℂ) ∈ V := by
    change ((e x).1, (0 : Fin c → ℂ)) ∈ e.target ∧
      e.symm ((e x).1, 0) ∈ W ∩ W₀
    rw [heq, e.left_inv hx]
    exact ⟨e.map_source hx, hxW,
      mem_flattenedSupportNeighborhood (Fin r → ℂ) c e x hx⟩
  have hV : ∀ v ∈ V, ((e x).1, v) ∈ e.target ∧ e.symm ((e x).1, v) ∈ W₀ :=
    fun _ hv => ⟨hv.1, hv.2.2⟩
  obtain ⟨z, hz⟩ := (neighborhoodPointComplement_relativeHomologyMap_bijective
    V 0 hVo h0V (2 * c)).2 (standardComplexLocalClass ℚ c)
  refine ⟨V, hV, hVo, h0V, fun _ hv => hv.2.1, z, hz, ?_⟩
  apply chartNormalProjection_relativeHomologyMap_injective (Fin r → ℂ) c e S hS x hx h0
  rw [chartNormalProjection_normalClass, ← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  change relativeHomologyMap ℚ (2 * c)
    (chartNormalFiberPair c e S hS (e x).1 W₀ V hV ≫
      chartNormalProjectionPair (Fin r → ℂ) c e S hS W₀ _) z = _
  rw [chartNormalFiber_comp_projection]
  exact hz

/-- Normalization on one open neighborhood computes the evaluation on the fixed generator. -/
theorem a3b4a_gysin_normal_evaluation_of_local_normalization
    {M : Type} [TopologicalSpace M] {r c : ℕ}
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin c → ℂ)))
    (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)
    (β : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of M) Sᶜ) (2 * c))
    (m : ℚ) (W : Set M) (hW : IsOpen W) (hxW : x ∈ W) (hWe : W ⊆ e.source)
    (hβ : relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap W S) β =
      m • chartNormalProjectionCoclass (Fin r → ℂ) c e S hS W hWe) :
    relativeCohomologyEquivDualHomology ℚ _ (2 * c)
      (relativeCohomologyMap ℚ (2 * c)
        (a3b4_neighborhoodPairMap (flattenedSupportNeighborhood (Fin r → ℂ) c e x hx) S) β)
      (flattenedSupportNormalClass (Fin r → ℂ) c e x hx S hS h0) = m := by
  let W₀ := flattenedSupportNeighborhood (Fin r → ℂ) c e x hx
  obtain ⟨V, hV, _, _, hVW, z, hz, hFz⟩ :=
    a3b4a_gysin_normalClass_from_small_disk e S hS x hx h0 W hW hxW
  have hVW' : ∀ v ∈ V, ((e x).1, v) ∈ e.target ∧ e.symm ((e x).1, v) ∈ W :=
    fun v hv => ⟨(hV v hv).1, hVW v hv⟩
  let F₀ := chartNormalFiberPair c e S hS (e x).1 W₀ V hV
  let F := chartNormalFiberPair c e S hS (e x).1 W V hVW'
  have hpair :
      relativeCohomologyEquivDualHomology ℚ _ (2 * c)
        (relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap W₀ S) β)
        (relativeHomologyMap ℚ (2 * c) F₀ z) =
      relativeCohomologyEquivDualHomology ℚ _ (2 * c)
        (relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap W S) β)
        (relativeHomologyMap ℚ (2 * c) F z) := by
    rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
      relativeCohomologyEquivDualHomology_relativeCohomologyMap,
      ← LinearMap.comp_apply (relativeHomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap W₀ S)),
      ← LinearMap.comp_apply (relativeHomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap W S)),
      ← relativeHomologyMap_comp, ← relativeHomologyMap_comp]
    rfl
  rw [← hFz]
  change relativeCohomologyEquivDualHomology ℚ _ (2 * c)
    (relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap W₀ S) β)
    (relativeHomologyMap ℚ (2 * c) F₀ z) = m
  rw [hpair, hβ, map_smul, LinearMap.smul_apply, chartNormalProjectionCoclass,
    relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    relativeCohomologyEquivDualHomology_normalizedRelativeCoclass,
    ← LinearMap.comp_apply (relativeHomologyMap ℚ (2 * c)
      (chartNormalProjectionPair (Fin r → ℂ) c e S hS W hWe)),
    ← relativeHomologyMap_comp]
  change m • normalizedDual (standardComplexLocalClass ℚ c) _
    (relativeHomologyMap ℚ (2 * c)
      (chartNormalFiberPair c e S hS (e x).1 W V hVW' ≫
        chartNormalProjectionPair (Fin r → ℂ) c e S hS W hWe) z) = m
  rw [chartNormalFiber_comp_projection, hz, normalizedDual_apply_self, smul_eq_mul, mul_one]

end HodgeLean.Adapters
