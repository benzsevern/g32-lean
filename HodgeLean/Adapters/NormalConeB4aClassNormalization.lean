import HodgeLean.Adapters.NormalConeB4aClassRestriction

/-! # Scalar normalization on a flattened support

Pairing with the explicit complex normal class determines a local class,
including zero and arbitrary rational multiplicities. This is the local
uniqueness step before gluing or extension across singular strata.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicTopology.Singular

/-- Evaluation on the complex normal class detects equality of local classes. -/
theorem a3b4a_classLocal_ext_normalClass
    {M : Type} [TopologicalSpace M] {r c : ℕ}
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin c → ℂ)))
    (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : M) (hx : x ∈ e.source) (hxS : x ∈ S)
    (α β : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair
        (flattenedSupportNeighborhood (Fin r → ℂ) c e x hx) S) (2 * c))
    (h : relativeCohomologyEquivDualHomology ℚ _ (2 * c) α
        (flattenedSupportNormalClass (Fin r → ℂ) c e x hx S hS ((hS x hx).mp hxS)) =
      relativeCohomologyEquivDualHomology ℚ _ (2 * c) β
        (flattenedSupportNormalClass (Fin r → ℂ) c e x hx S hS ((hS x hx).mp hxS))) :
    α = β := by
  apply (relativeCohomologyEquivDualHomology ℚ _ (2 * c)).injective
  ext v
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff ℚ _).mp
    (span_flattenedSupportNormalClass_eq_top (Fin r → ℂ) c e S hS x hx
      ((hS x hx).mp hxS)) v
  rw [map_smul, map_smul, h]

/-- A prescribed rational evaluation gives exactly that multiple of the
normal-projection coclass. -/
theorem a3b4a_classLocal_eq_smul_normalCoclass
    {M : Type} [TopologicalSpace M] {r c : ℕ}
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin c → ℂ)))
    (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : M) (hx : x ∈ e.source) (hxS : x ∈ S)
    (α : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair
        (flattenedSupportNeighborhood (Fin r → ℂ) c e x hx) S) (2 * c))
    (m : ℚ)
    (h : relativeCohomologyEquivDualHomology ℚ _ (2 * c) α
      (flattenedSupportNormalClass (Fin r → ℂ) c e x hx S hS ((hS x hx).mp hxS)) = m) :
    α = m • chartNormalProjectionCoclass (Fin r → ℂ) c e S hS
      (flattenedSupportNeighborhood (Fin r → ℂ) c e x hx)
      (flattenedSupportNeighborhood_subset_source (Fin r → ℂ) c e x hx) := by
  apply a3b4a_classLocal_ext_normalClass e S hS x hx hxS
  rw [h, map_smul, LinearMap.smul_apply,
    chartNormalProjectionCoclass_apply_normalClass, smul_eq_mul, mul_one]

end HodgeLean.Adapters
