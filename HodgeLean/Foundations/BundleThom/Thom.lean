import HodgeLean.Foundations.BundleThom.Proofs

/-! # Rational Thom and Euler operations

The selected Thom class is obtained from existence, without a class argument.
Euler is its zero-section pullback in actual rational singular cohomology.
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

/-- Unique rational Thom class normalized on actual complex linear bundle charts.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Hatcher, §4.D. -/
theorem i1_bundleThom_exists_unique :
    ∃! u : i1_supportedClass k E,
      ∀ (e : Trivialization (Fin k → ℂ) (Bundle.TotalSpace.proj :
        TotalSpace (Fin k → ℂ) E → B)) (he : e.IsLinear ℂ),
        relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E e) u =
          i1_chartOrientation k E e :=
  i1_bundleThom_exists_unique_aux k E

/-- The rational Thom class selected from the unique normalized class.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Thom class. -/
def i1_bundleThom : i1_supportedClass k E :=
  Classical.choose (i1_bundleThom_exists_unique k E).exists

/-- Independent bundle Euler operation, using the bundle's own zero section.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Euler class. -/
def i1_bundleEuler : Cohomology ℚ (TopCat.of B) (2 * k) :=
  i1_zeroPullback k E (i1_bundleThom k E)

example (e : Trivialization (Fin k → ℂ) (Bundle.TotalSpace.proj :
    TotalSpace (Fin k → ℂ) E → B)) [e.IsLinear ℂ] :
    RelativeCohomology ℚ (i1_chartPair k E e) (2 * k) := i1_chartOrientation k E e
example (b : B) (v : E b) (hv : v ≠ 0) :
    (⟨b, v⟩ : TotalSpace (Fin k → ℂ) E) ∉ i1_zeroSupport k E := hv
example : i1_zeroPullback k E (0 + 0) = 0 := by
  rw [add_zero, map_zero]

-- Selection retains the chart normalization used in the defining existence data.
example (e : Trivialization (Fin k → ℂ) (Bundle.TotalSpace.proj :
    TotalSpace (Fin k → ℂ) E → B)) [he : e.IsLinear ℂ] :
    relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E e)
      (i1_bundleThom k E) = i1_chartOrientation k E e :=
  Classical.choose_spec (i1_bundleThom_exists_unique k E).exists e he

example : i1_bundleEuler k E = i1_zeroPullback k E (i1_bundleThom k E) := rfl

end HodgeLean.Foundations.BundleThom
