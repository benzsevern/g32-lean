import HodgeLean.RealDefs.FundamentalClass.Point
import Mathlib.Topology.VectorBundle.Constructions

/-! # Rational classes on actual complex bundle total spaces

The complex model fibre fixes the orientation through `normalizedPointCoclass`.
No cohomology class is part of the bundle data.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
variable [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]

/-- The total space of the given rank-k complex vector bundle.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6. -/
abbrev i1_totalSpace : TopCat := TopCat.of (TotalSpace (Fin k → ℂ) E)

/-- The actual continuous zero section.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6. -/
def i1_zeroSection : C(B, i1_totalSpace k E) :=
  ⟨zeroSection (Fin k → ℂ) E, Bundle.Trivialization.continuous_zeroSection ℂ⟩

/-- The image of the zero section, written fibrewise.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6. -/
def i1_zeroSupport : Set (i1_totalSpace k E) := {v | v.2 = 0}

/-- Rational singular cohomology supported on the zero section.
Source: Bott–Tu, §6; `AlgebraicTopology.Singular.CohomologyWithSupport`. -/
abbrev i1_supportedClass :=
  CohomologyWithSupport ℚ (i1_totalSpace k E) (i1_zeroSupport k E) (2 * k)

/-- Zero-section pullback after forgetting support; defined for every supported class.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Euler class. -/
def i1_zeroPullback : i1_supportedClass k E →ₗ[ℚ]
    Cohomology ℚ (TopCat.of B) (2 * k) :=
  (cohomologyMap ℚ (2 * k) (TopCat.ofHom (i1_zeroSection k E))).comp
    (forgetSupport ℚ (i1_totalSpace k E) (i1_zeroSupport k E) (2 * k))

example (b : B) : (i1_zeroSection k E b).proj = b := rfl
example (b : B) : i1_zeroSection k E b ∈ i1_zeroSupport k E := rfl
example : i1_zeroPullback k E 0 = 0 := map_zero _
example (b : B) (v : E b) (hv : v ≠ 0) :
    (⟨b, v⟩ : TotalSpace (Fin k → ℂ) E) ∉ i1_zeroSupport k E := hv
example (b : B) (v : E b) : i1_totalSpace k E := ⟨b, v⟩
example : i1_supportedClass k E := 0

variable (e : Trivialization (Fin k → ℂ) (Bundle.TotalSpace.proj :
  TotalSpace (Fin k → ℂ) E → B)) [e.IsLinear ℂ]

/-- The complement pair in an actual bundle chart, with its inherited zero support.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6. -/
def i1_chartPair : TopPair :=
  TopPair.ofSubset (X := TopCat.of e.source) {v | (v.1 : TotalSpace (Fin k → ℂ) E).2 ≠ 0}

/-- Inclusion of an actual bundle chart as a map of complement pairs.
Source: Hatcher, Algebraic Topology, §3.1, relative naturality. -/
def i1_chartInclusion : i1_chartPair k E e ⟶
    TopPair.ofSubset (X := i1_totalSpace k E) (i1_zeroSupport k E)ᶜ :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) (fun _ h => h)

/-- Complex normal coordinates on the chart, as a map of complement pairs.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex orientation. -/
def i1_chartNormal : i1_chartPair k E e ⟶ puncturedPair ℂ k :=
  TopPair.ofSubsetHom (TopCat.ofHom
    ⟨fun v : e.source => (e v.1).2,
      (e.continuousOn.comp_continuous continuous_subtype_val (fun v => v.2)).snd⟩) (by
    intro v hv hz
    apply hv
    exact (e.continuousLinearEquivAt ℂ v.1.proj (e.mem_source.mp v.2)).injective
      (hz.trans (map_zero _).symm))

/-- The oriented class on a chart, pulled back from the existing complex normal coclass.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; `normalizedPointCoclass`. -/
def i1_chartOrientation : RelativeCohomology ℚ (i1_chartPair k E e) (2 * k) :=
  relativeCohomologyMap ℚ (2 * k) (i1_chartNormal k E e) (normalizedPointCoclass k)

example (v : e.source) : (i1_chartInclusion k E e).right v = v.1 := rfl
example (v : e.source) : (i1_chartNormal k E e).right v = (e v.1).2 := rfl
example : RelativeCohomology ℚ (i1_chartPair k E e) (2 * k) :=
  i1_chartOrientation k E e
example (v : e.source) (hv : v.1.2 ≠ 0) :
    (i1_chartPair k E e).snd := ⟨v, hv⟩

end HodgeLean.Foundations.BundleThom
