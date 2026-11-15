import HodgeLean.Foundations.BundleThom.RankOneCompactThomHelpers
import HodgeLean.Foundations.BundleThom.ZeroRankThomUniquenessHelpers

/-! # Every-chart normalized Thom existence in complex ranks zero and one

Both ranks use independently checked constructions for the actual supplied bundle.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- An actual complex bundle of rank at most one over a compact base has a unique every-chart normalized rational supported Thom class.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Hatcher, Algebraic Topology, §4.D. -/
theorem i1_bundleThom_exists_unique_of_rank_le_one {B : Type} [TopologicalSpace B] [CompactSpace B]
    (k : ℕ) (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E] (hk : k ≤ 1) :
    ∃! u : i1_supportedClass k E,
      ∀ (g : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
        (hg : g.IsLinear ℂ),
        relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E g) u = i1_chartOrientation k E g := by
  by_cases h0 : k = 0
  · subst k
    exact i1_zeroRankThom_exists_unique E
  · have h1 : k = 1 := by omega
    subst k
    exact i1_rankOne_bundleThom_exists_unique E

end HodgeLean.Foundations.BundleThom
