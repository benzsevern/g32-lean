import HodgeLean.Foundations.BundleThom.ProductCompactRestrictionDetectionHelpers
import HodgeLean.Foundations.BundleThom.CompactProductMatrixSuccessorOrientationHelpers

/-! # Global successor-degree normal comparison over arbitrary bases

Compact inverse-image restrictions detect the actual global coclasses.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Every continuous invertible complex matrix family over an arbitrary base preserves successor-degree normal coclass pullback through the full normal degree.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex orientation; Hatcher, §2.1 and §3.1. -/
theorem i1_productMatrixNormalMap_successor_pullback {B : Type} [TopologicalSpace B]
    (k n : ℕ) (hn : n < 2 * k) (A : B → Matrix (Fin k) (Fin k) ℂ) (hA : Continuous A)
    (hd : ∀ b, (A b).det ≠ 0) (u : RelativeCohomology ℚ (puncturedPair ℂ k) (n + 1)) :
    relativeCohomologyMap ℚ (n + 1) (i1_productMatrixNormalMap k A hA hd) u =
      relativeCohomologyMap ℚ (n + 1) (i1_productNormalProjection B k) u := by
  apply i1_productCoclass_ext_of_compact_restrictions k (n + 1)
  intro K
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_productBaseMap_comp_matrixNormalMap,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_productBaseMap_comp_projection]
  exact i1_compactProductMatrixNormalMap_successor_pullback k n hn
    (A ∘ (Subtype.val : K → B)) (hA.comp continuous_subtype_val)
    (fun b => hd b.1) u

/-- Every varying invertible complex frame preserves the actual normal coclass pullback in the Thom degree over an arbitrary base.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex orientation. -/
theorem i1_productMatrixNormalMap_thomDegree_pullback {B : Type} [TopologicalSpace B]
    (k : ℕ) (hk : 0 < k) (A : B → Matrix (Fin k) (Fin k) ℂ) (hA : Continuous A)
    (hd : ∀ b, (A b).det ≠ 0) (u : RelativeCohomology ℚ (puncturedPair ℂ k) (2 * k)) :
    relativeCohomologyMap ℚ (2 * k) (i1_productMatrixNormalMap k A hA hd) u =
      relativeCohomologyMap ℚ (2 * k) (i1_productNormalProjection B k) u := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show 2 * k ≠ 0 by omega)
  revert u
  rw [hn]
  intro u
  exact i1_productMatrixNormalMap_successor_pullback k n (by omega) A hA hd u

end HodgeLean.Foundations.BundleThom
