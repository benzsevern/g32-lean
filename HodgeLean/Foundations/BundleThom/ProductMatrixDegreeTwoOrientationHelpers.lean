import HodgeLean.Foundations.BundleThom.ProductCompactRestrictionDetectionHelpers
import HodgeLean.Foundations.BundleThom.CompactProductMatrixOrientationHelpers

/-! # Global degree-two normal comparison over arbitrary bases

Compact inverse-image restrictions detect the actual global coclasses.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Every continuous invertible complex matrix family over an arbitrary base preserves degree-two normal coclass pullback in positive rank.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex orientation; Hatcher, §2.1 and §3.1. -/
theorem i1_productMatrixNormalMap_degreeTwo_pullback {B : Type} [TopologicalSpace B]
    (k : ℕ) (hk : 0 < k) (A : B → Matrix (Fin k) (Fin k) ℂ) (hA : Continuous A)
    (hd : ∀ b, (A b).det ≠ 0) (u : RelativeCohomology ℚ (puncturedPair ℂ k) 2) :
    relativeCohomologyMap ℚ 2 (i1_productMatrixNormalMap k A hA hd) u =
      relativeCohomologyMap ℚ 2 (i1_productNormalProjection B k) u := by
  apply i1_productCoclass_ext_of_compact_restrictions k 2
  intro K
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_productBaseMap_comp_matrixNormalMap,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_productBaseMap_comp_projection]
  exact i1_compactProductMatrixNormalMap_degreeTwo_pullback k hk
    (A ∘ (Subtype.val : K → B)) (hA.comp continuous_subtype_val)
    (fun b => hd b.1) u

end HodgeLean.Foundations.BundleThom
