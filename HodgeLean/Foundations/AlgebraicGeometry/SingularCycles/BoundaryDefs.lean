import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs
import HodgeLean.Adapters.NormalConeB4aClassUniqueBoundary

/-! # Algebraic boundaries for retained finite maps

The target open is intersected with its actual smooth locus. Its inverse image
is removed only inside the collected source support. Components over the
removed locus remain in an explicit coefficient summand.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
open scoped Classical
namespace AlgebraicGeometry.SingularCycles

/-- Intersect a target open with the scheme-theoretic smooth locus.
Source: Stacks Project, Tag 01V7; Mathlib `Scheme.Hom.smoothLocus`. -/
def retainedOpen {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (U : Z.Opens) : Z.Opens := U ⊓ q.smoothLocus

example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    (U : Z.Opens) : retainedOpen q U = U := by
  simp [retainedOpen, q.smoothLocus_eq_top]

/-- The actual closed target set excluded by the retained open.
Source: EGA IV, 6.9.1; Stacks Project, Tag 052B. -/
def targetBoundary {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (U : Z.Opens) : Closeds Z := (retainedOpen q U).compl

example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] : targetBoundary q ⊥ = ⊤ := by
  ext x
  simp [targetBoundary, retainedOpen]

/-- The intrinsic bad target set: singular target points and images of non-flat source points.
Source: EGA IV, 6.9.1; Stacks Project, Tags 052B and 01V7. -/
def actualBadLocus {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (f : X ⟶ Z) : Set Z :=
  (q.smoothLocus : Set Z)ᶜ ∪ f '' {x | ¬ (f.stalkMap x).hom.Flat}

example {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    (f : X ⟶ Z) [Flat f] : actualBadLocus q f = ∅ := by
  ext z
  simp only [actualBadLocus, q.smoothLocus_eq_top, Opens.coe_top,
    Set.compl_univ, Set.empty_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_exists, not_and]
  intro x hx
  exact (hx (Flat.stalkMap f x)).elim

/-- The canonical retained open, defined without a supplied choice of open subset.
Source: EGA IV, 6.9.1; Stacks Project, Tag 052B. -/
def actualGoodOpen {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (f : X ⟶ Z) : Z.Opens :=
  ⟨interior (actualBadLocus q f)ᶜ, isOpen_interior⟩

example {X Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFinitePresentation q] (f : X ⟶ Z) (z : Z)
    (hz : z ∈ actualGoodOpen q f) : z ∉ actualBadLocus q f :=
  interior_subset hz

/-- Collected coefficients whose generic points map into the excluded target.
No component is discarded by a codimension convention.
Source: Fulton, Intersection Theory, second edition, §§1.5 and 1.7. -/
def boundaryPart {X Z : Scheme.{0}} (f : X ⟶ Z)
    (D : Closeds Z) (b : X →₀ ℚ) : X →₀ ℚ := b.filter (fun x => f x ∈ D)

example {X Z : Scheme.{0}} (f : X ⟶ Z) (b : X →₀ ℚ) :
    boundaryPart f ⊤ b = b := by
  ext x
  change (if f x ∈ (⊤ : Closeds Z) then b x else (0 : ℚ)) = b x
  exact if_pos (Set.mem_univ _)

/-- The entire inverse-image bad set inside the algebraic cycle support,
including intersections of retained components with the bad set.
Source: Fulton, Intersection Theory, second edition, §19.1;
`a3b4a_classAlgebraicSupport`. -/
def sourceBoundary {X Z : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ℂ))
    [QuasiCompact s] (f : X ⟶ Z) (D : Closeds Z) (b : X →₀ ℚ) : Closeds X :=
  a3b4a_classAlgebraicSupport s (collectedCycle b) ⊓ D.preimage f.continuous

example {X Z : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact s]
    (f : X ⟶ Z) (b : X →₀ ℚ) : sourceBoundary s f ⊥ b = ⊥ := by
  ext x
  simp [sourceBoundary]

/-- Restrict the actual supported class to the complement of the algebraic boundary.
Source: Hatcher, Algebraic Topology, §3.1; `a3b4_neighborhoodPairMap`. -/
def boundaryRestriction {X Z : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ℂ))
    [QuasiCompact s] (f : X ⟶ Z) (D : Closeds Z) (b : X →₀ ℚ) (k : ℕ) :=
  relativeCohomologyMap ℚ ((2 : ℕ) * k)
    (a3b4_neighborhoodPairMap (M := a3b4_an s)
      (Point.underlying ⁻¹' (sourceBoundary s f D b : Set X))ᶜ
      (a3b4_cycleSupport s (collectedCycle b)))

example {X Z : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact s]
    (f : X ⟶ Z) (D : Closeds Z) (b : X →₀ ℚ) (k : ℕ) :
    boundaryRestriction s f D b k (0 : _) = (0 : _) := map_zero _

/-- Finitely supported coefficients of the actual unreduced inverse-image cycle.
Finiteness comes from the finite-type complex source, before any bad component is selected.
Source: Fulton, Intersection Theory, second edition, §§1.5 and 1.7;
`ccm3_flatPullbackPrime` and `a3b2_support_finite`. -/
def inverseCoefficients {X Z : Over (Spec (CommRingCat.of ℂ))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : X ⟶ Z) (x : Z.left) : X.left →₀ ℚ := by
  letI := a3b4_compactSpace X.hom
  exact Finsupp.ofSupportFinite (ccm3_flatPullbackPrime f.left x)
    (a3b2_support_finite (ccm3_flatPullbackPrime f.left x))

example (x : Spec (CommRingCat.of ℂ)) :
    inverseCoefficients (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of ℂ))))) x ≠ 0 := by
  intro h
  apply ccm3_flatPullbackPrime_ne_zero
    (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of ℂ))))) x
  ext z
  exact congrArg (fun b => b z) h

end AlgebraicGeometry.SingularCycles
