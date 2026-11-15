import HodgeLean.Foundations.BundleThom.RelativeHomologySuccessorVanishingHelpers
import HodgeLean.Foundations.BundleThom.ProductRelativeDegreeZeroHelpers
import HodgeLean.Foundations.BundleThom.ChartProductIsoHelpers

/-! # Low-degree relative homology on arbitrary bundle chart domains

No local contractibility assumption on the base domain is required.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
variable (e : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
variable [e.IsLinear ℂ]

/-- Positive-rank chart pairs have zero degree-zero rational homology over arbitrary base domains.
Source: Hatcher, Algebraic Topology, §2.1, relative product homology. -/
theorem i1_chartRelativeHomologyZero_isZero (hk : 0 < k) :
    IsZero (RelativeHomology ℚ (i1_chartPair k E e) 0) :=
  (i1_productNormalRelativeHomologyZero_isZero_of_pos (B := e.baseSet) k hk).of_iso
    ((relativeHomologyFunctor ℚ 0).mapIso (i1_chartPairProductIso k E e))

/-- Positive-rank chart pairs have zero degree-one rational homology over arbitrary base domains.
Source: Hatcher, Algebraic Topology, §2.1, relative product homology. -/
theorem i1_chartRelativeHomologyOne_isZero (hk : 0 < k) :
    IsZero (RelativeHomology ℚ (i1_chartPair k E e) 1) :=
  (i1_productNormalRelativeHomologyOne_isZero (B := e.baseSet) k hk).of_iso
    ((relativeHomologyFunctor ℚ 1).mapIso (i1_chartPairProductIso k E e))

end HodgeLean.Foundations.BundleThom
