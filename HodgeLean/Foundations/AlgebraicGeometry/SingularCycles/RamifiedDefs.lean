import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Defs
import HodgeLean.Adapters.SupportedCycleClassesLocal
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClass
import Other.AlgebraicTopology.LocalHomology.PairExcision

/-! # Ramified local pairs and collected rational components

The constructions retain the scheme fibre stalk, actual maps of punctured
neighbourhoods, complex chart orientations, and finite coefficient collection.
The regular separated locus removes intersections only where local tests run.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace AlgebraicGeometry.SingularCycles

/-- A map on a neighbourhood with a single inverse image of the marked point.
Source: Hatcher, Algebraic Topology, §2.1, maps of relative pairs. -/
def isolatedPairMap {X Y : TopCat.{0}} (f : X ⟶ Y) (U : Set X) (x : X)
    (h : ∀ z ∈ U, f z = f x → z = x) :
    neighborhoodPointComplementPair U x ⟶ pointComplementPair (f x) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun z => f z, by fun_prop⟩)
    (TopCat.ofHom ⟨fun z => ⟨f z.1, fun hz => z.2 (h z.1 z.1.2 hz)⟩,
      by fun_prop⟩) (by ext; rfl)

example : TopPair.Hom.fst (isolatedPairMap (𝟙 (TopCat.of ℂ)) Set.univ (0 : ℂ)
    (fun _ _ h => h)) ⟨(2 : ℂ), by trivial⟩ = (2 : ℂ) := rfl

/-- Remove the zero-dimensional tangential factor from a normal chart.
Source: Hatcher, Algebraic Topology, §3.3; the ordered complex orientation. -/
def pointChart {M : Type} [TopologicalSpace M] {d : ℕ}
    (e : OpenPartialHomeomorph M ((Fin 0 → ℂ) × (Fin d → ℂ))) :
    OpenPartialHomeomorph M (Fin d → ℂ) :=
  e.trans (Homeomorph.uniqueProd (Fin 0 → ℂ) (Fin d → ℂ)).toOpenPartialHomeomorph

example {M : Type} [TopologicalSpace M] {d : ℕ}
    (e : OpenPartialHomeomorph M ((Fin 0 → ℂ) × (Fin d → ℂ))) (x : M) :
    pointChart e x = (e x).2 := rfl

/-- The local chart orientation restricted by the inverse of open excision.
Source: Hatcher, Algebraic Topology, Proposition 3.26; upstream
`localClassOfChart` and `neighborhoodPointComplementRelativeHomologyIso`. -/
def neighborhoodOrientation {M : Type} [TopologicalSpace M] [T1Space M] (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    (U : Set M) (hU : IsOpen U) (hxU : x ∈ U) :
    RelativeHomology ℚ (neighborhoodPointComplementPair U x) (2 * d) :=
  (neighborhoodPointComplementRelativeHomologyIso U x hU hxU (2 * d)).inv.hom
    (localClassOfChart d e x hx)

example {M : Type} [TopologicalSpace M] [T1Space M] (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    (U : Set M) (hU : IsOpen U) (hxU : x ∈ U) :
    (neighborhoodPointComplementRelativeHomologyIso U x hU hxU (2 * d)).hom.hom
      (neighborhoodOrientation d e x hx U hU hxU) = localClassOfChart d e x hx := by
  exact ConcreteCategory.congr_hom
    (Iso.inv_hom_id (neighborhoodPointComplementRelativeHomologyIso U x hU hxU (2 * d))) _

/-- Collect rational coefficients at equal prime points before taking support.
Source: Fulton, Intersection Theory, second edition, §1.5. -/
def collectPrimes {ι : Type*} [Fintype ι] {Z : Scheme} (p : ι → Z) (a : ι → ℚ) : Z →₀ ℚ :=
  ∑ i, Finsupp.single (p i) (a i)

example (Z : Scheme) (p : Z) :
    collectPrimes (fun _ : Bool => p) (fun b => if b then (2 : ℚ) else -2) = 0 := by
  classical
  simp [collectPrimes]

/-- The actual cycle associated to the collected finitely supported coefficients.
Source: Fulton, Intersection Theory, second edition, §1.5. -/
def collectedCycle {Z : Scheme} (b : Z →₀ ℚ) : AlgebraicCycle Z ℚ :=
  ∑ p ∈ b.support, Function.locallyFinsuppWithin.single p (b p)

private theorem collectedCycle_apply {Z : Scheme} (b : Z →₀ ℚ) (p : Z) :
    collectedCycle b p = b p := by
  classical
  simp only [collectedCycle, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.single_apply]
  by_cases hp : p ∈ b.support
  · rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hqp
      simp [Ne.symm hqp]
    · exact fun h => (h hp).elim
  · have hz := Finsupp.notMem_support_iff.mp hp
    rw [hz]
    apply Finset.sum_eq_zero
    intro q hq
    have hqp : q ≠ p := fun h => hp (h ▸ hq)
    simp [Ne.symm hqp]

example {Z : Scheme} (p : Z) : collectedCycle (Finsupp.single p (3 : ℚ)) p = (3 : ℚ) := by
  classical
  rw [collectedCycle_apply, Finsupp.single_eq_same]

/-- Analytic support of a single prime, with coefficient one.
Source: Fulton, Intersection Theory, second edition, §19.1. -/
def primeSupport {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (p : Z) :
    Set (a3b4_an q) :=
  a3b4_cycleSupport q (Function.locallyFinsuppWithin.single p (1 : ℚ))

example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (p : Z) (x : a3b4_an q) :
    x ∈ primeSupport q p ↔ x.underlying ∈ closure ({p} : Set Z) := by
  classical
  simp [primeSupport, a3b4_cycleSupport]

private theorem primeSupport_subset {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) (b : Z →₀ ℚ) (p : b.support) :
    primeSupport q p.1 ⊆ a3b4_cycleSupport q (collectedCycle b) := by
  classical
  intro x hx
  have hp : b p.1 ≠ 0 := Finsupp.mem_support_iff.mp p.2
  have hc : collectedCycle b p.1 ≠ 0 := by rw [collectedCycle_apply]; exact hp
  have hxp : x.underlying ∈ closure ({p.1} : Set Z) := by
    simpa [primeSupport, a3b4_cycleSupport] using hx
  exact Set.mem_iUnion₂.mpr ⟨p.1, hc, hxp⟩

/-- Assemble only the surviving collected primes through the supported-classes API.
No inclusion is requested for a zero coefficient.
Source: Hatcher, Algebraic Topology, §3.1; `SupportedClasses.weightedSum`. -/
def assembledClass {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    (b : Z →₀ ℚ) (n : ℕ)
    (c : ∀ p : b.support, CohomologyWithSupport ℚ (a3b4_an q) (primeSupport q p.1) n) :
    CohomologyWithSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (collectedCycle b)) n :=
  SupportedClasses.weightedSum (a3b4_an q) n (fun p : b.support => primeSupport q p.1)
    (a3b4_cycleSupport q (collectedCycle b)) (fun p => b p.1)
    (fun p _ => primeSupport_subset q b p) c

example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (b : Z →₀ ℚ) (n : ℕ) :
    assembledClass q b n (fun _ => 0) = 0 := by
  classical
  simp [assembledClass, SupportedClasses.weightedSum]

/-- Points where one surviving prime is holomorphically regular and separated
from the other surviving primes. Intersections elsewhere are retained.
Source: Fulton, Intersection Theory, second edition, §19.1; Borel–Haefliger,
La classe d'homologie fondamentale d'un espace analytique (1961), §2. -/
def regularSeparatedLocus {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (b : Z →₀ ℚ) (k : ℕ) : Set (a3b4_an q) :=
  {x | ∃ p : b.support, x ∈ primeSupport q p.1 ∧
    (∀ t : b.support, t ≠ p → x ∉ primeSupport q t.1) ∧
    ∃ (r : ℕ) (e : OpenPartialHomeomorph (a3b4_an q) ((Fin r → ℂ) × (Fin k → ℂ))),
      a3b4_IsHolChart q e ∧ x ∈ e.source ∧
        ∀ y ∈ e.source, y ∈ primeSupport q p.1 ↔ (e y).2 = 0}

example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q] (k : ℕ) :
    regularSeparatedLocus q (0 : Z →₀ ℚ) k = ∅ := by
  ext x
  simp [regularSeparatedLocus]

end AlgebraicGeometry.SingularCycles
