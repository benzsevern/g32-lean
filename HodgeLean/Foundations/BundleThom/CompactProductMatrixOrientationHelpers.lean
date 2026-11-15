import HodgeLean.Foundations.BundleThom.CompactProductCoclassDetectionHelpers
import HodgeLean.Foundations.BundleThom.LocalNormalOrientationHelpers

/-! # Global degree-two normal comparison over compact bases

Local invertible interpolations are assembled by actual relative restriction detection.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Every continuous invertible complex matrix family over a compact base preserves the degree-two normal coclass pullback in positive rank.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex orientation; Hatcher, §2.2 and §3.1. -/
theorem i1_compactProductMatrixNormalMap_degreeTwo_pullback {B : Type}
    [TopologicalSpace B] [CompactSpace B] (k : ℕ) (hk : 0 < k)
    (A : B → Matrix (Fin k) (Fin k) ℂ) (hA : Continuous A)
    (hd : ∀ b, (A b).det ≠ 0)
    (u : RelativeCohomology ℚ (puncturedPair ℂ k) 2) :
    relativeCohomologyMap ℚ 2 (i1_productMatrixNormalMap k A hA hd) u =
      relativeCohomologyMap ℚ 2 (i1_productNormalProjection B k) u := by
  apply i1_compactProductCoclass_ext_of_locally_eq k hk
  intro b
  obtain ⟨U, hb, hU⟩ := i1_productMatrixNormalMap_locally_pullback k A hA hd b
  refine ⟨U, hb, ?_⟩
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_productBaseMap_comp_matrixNormalMap,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_productBaseMap_comp_projection]
  exact hU 2 u

end HodgeLean.Foundations.BundleThom
