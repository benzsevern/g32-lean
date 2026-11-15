import HodgeLean.Foundations.BundleThom.ProductComplexRealPairHelpers
import HodgeLean.Foundations.BundleThom.RestrictedChartLowHomologyHelpers
import HodgeLean.Foundations.BundleThom.ChartIntersectionProductHelpers

/-! # All lower normal degrees on actual bundle chart pairs

HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
variable (e : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
variable [e.IsLinear ℂ]

/-- Actual chart relative homology vanishes in every degree below twice the complex rank over arbitrary base domains.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Hatcher, §2.2, relative product charts. -/
theorem i1_chartRelativeHomology_isZero_of_lt (n : ℕ) (hn : n < 2 * k) :
    IsZero (RelativeHomology ℚ (i1_chartPair k E e) n) :=
  (i1_productNormalRelativeHomology_isZero_of_lt e.baseSet k n hn).of_iso
    ((relativeHomologyFunctor ℚ n).mapIso (i1_chartPairProductIso k E e))

/-- Open base restriction of an actual chart retains vanishing in every degree below twice the complex rank.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Hatcher, §2.2, restricted product charts. -/
theorem i1_chartBaseRestrictionRelativeHomology_isZero_of_lt
    (n : ℕ) (hn : n < 2 * k) (S : Set B) (hS : IsOpen S) :
    IsZero (RelativeHomology ℚ
      (i1_subsetRelativePair (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ
        (e.source ∩ TotalSpace.proj ⁻¹' S)) n) := by
  let r := e.restrOpen S hS
  letI : r.IsLinear ℂ := i1_chartRestrOpen_isLinear k E e S hS
  have h := i1_chartRelativeHomology_isZero_of_lt k E r n hn
  rw [i1_chartPair_eq_actualDomain, i1_chartRestrOpen_source] at h
  exact h

/-- Actual chart intersections retain vanishing in every degree below twice the complex rank.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Hatcher, §2.2, relative intersection product coordinates. -/
theorem i1_chartIntersectionRelativeHomology_isZero_of_lt
    (e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    (n : ℕ) (hn : n < 2 * k) :
    IsZero (RelativeHomology ℚ
      (i1_subsetRelativePair (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ
        (e.source ∩ e'.source)) n) :=
  (i1_productNormalRelativeHomology_isZero_of_lt ↥(e.baseSet ∩ e'.baseSet) k n hn).of_iso
    ((relativeHomologyFunctor ℚ n).mapIso (i1_chartIntersectionProductIso k E e e'))

end HodgeLean.Foundations.BundleThom
