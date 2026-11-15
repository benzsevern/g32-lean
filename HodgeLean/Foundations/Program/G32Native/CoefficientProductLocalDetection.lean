import HodgeLean.Foundations.BundleThom.ImmersionDefs

/-! # Detection of normal coclasses on arbitrary open base covers -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.BundleThom

/-- Local base restrictions detect positive-degree product coclasses through the normal degree. -/
theorem productNormalCoclass_ext_of_locally_eq {B : Type} [TopologicalSpace B]
    (k n : ℕ) (hn : n < 2 * k)
    (u v : RelativeCohomology ℚ (i1_productNormalPair B k) (n + 1))
    (hlocal : ∀ b : B, ∃ U : Opens B, b ∈ U ∧
      relativeCohomologyMap ℚ (n + 1)
        (i1_productBaseMap k (Subtype.val : U → B) continuous_subtype_val) u =
      relativeCohomologyMap ℚ (n + 1)
        (i1_productBaseMap k (Subtype.val : U → B) continuous_subtype_val) v) : u = v := by
  apply i1_productCoclass_ext_of_compact_restrictions k (n + 1)
  intro K
  apply i1_compactProductSuccessorCoclass_ext_of_locally_eq k n hn
  intro b
  obtain ⟨U, hb, he⟩ := hlocal b.1
  let V : Opens K := ⟨Subtype.val ⁻¹' U, U.isOpen.preimage continuous_subtype_val⟩
  let f : V → U := fun x => ⟨x.1.1, x.2⟩
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  refine ⟨V, hb, ?_⟩
  have h := congrArg
    (relativeCohomologyMap ℚ (n + 1) (i1_productBaseMap k f hf)) he
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, i1_productBaseMap_comp,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp, i1_productBaseMap_comp] at h
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, i1_productBaseMap_comp,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp, i1_productBaseMap_comp]
  exact h

/-- Local base restrictions detect the Thom-degree product coclass in every positive rank. -/
theorem productThomCoclass_ext_of_locally_eq {B : Type} [TopologicalSpace B]
    (k : ℕ) (hk : 0 < k)
    (u v : RelativeCohomology ℚ (i1_productNormalPair B k) (2 * k))
    (hlocal : ∀ b : B, ∃ U : Opens B, b ∈ U ∧
      relativeCohomologyMap ℚ (2 * k)
        (i1_productBaseMap k (Subtype.val : U → B) continuous_subtype_val) u =
      relativeCohomologyMap ℚ (2 * k)
        (i1_productBaseMap k (Subtype.val : U → B) continuous_subtype_val) v) : u = v := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show 2 * k ≠ 0 by omega)
  revert u v
  rw [hn]
  intro u v hlocal
  exact productNormalCoclass_ext_of_locally_eq k n (by omega) u v hlocal

end HodgeLean.Foundations.BundleThom
