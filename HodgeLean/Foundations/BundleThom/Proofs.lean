import HodgeLean.Foundations.BundleThom.PositiveRankCompactThomHelpers
import HodgeLean.Foundations.BundleThom.Defs
import HodgeLean.Foundations.BundleThom.LowRankThomExistenceHelpers

/-! # Thom existence and uniqueness obligation

Compact Hausdorff bases suffice for the topological construction; compact smooth
bases are included. Normalization is required on every complex linear chart.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
variable [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]

/-- Existence and uniqueness of the rational complex Thom class, with chart normalization.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Thom isomorphism;
Hatcher, Algebraic Topology, §4.D, Thom classes with rational coefficients. -/
theorem i1_bundleThom_exists_unique_aux :
    ∃! u : i1_supportedClass k E,
      ∀ (e : Trivialization (Fin k → ℂ) (Bundle.TotalSpace.proj :
        TotalSpace (Fin k → ℂ) E → B)) (he : e.IsLinear ℂ),
        relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E e) u =
          i1_chartOrientation k E e := by
  by_cases hk : k = 0
  · subst k
    exact i1_zeroRankThom_exists_unique E
  · exact i1_positiveRank_bundleThom_exists_unique k (Nat.pos_of_ne_zero hk) E

example (e : Trivialization (Fin k → ℂ) (Bundle.TotalSpace.proj :
    TotalSpace (Fin k → ℂ) E → B)) [e.IsLinear ℂ] :
    RelativeCohomology ℚ (i1_chartPair k E e) (2 * k) :=
  relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E e) 0

end HodgeLean.Foundations.BundleThom
