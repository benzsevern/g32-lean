import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedProofs

/-! # Ramified generic chart and collected component obligations

Finite flat maps are tested on actual smooth complex point charts. The local
coefficient is the unreduced inverse-image stalk length. Rational assembly
collects equal primes and imposes local normalization on the regular separated locus.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

/-- The local complex degree of a finite flat map equals its fibre stalk length.
Source: Fulton, Intersection Theory, second edition, §§1.7 and 19.1;
Stacks Project, Tags 02MB and 0B01; Borel–Haefliger (1961), §2. -/
theorem finite_flat_local_degree {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [Smooth X.hom] [Smooth Z.hom]
    [T1Space (ComplexPoint X)] (f : X ⟶ Z) [IsFinite f.left] [Flat f.left]
    (d : ℕ) (x : ComplexPoint X)
    (eX : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (eZ : OpenPartialHomeomorph (ComplexPoint Z) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (heX : a3b4_IsHolChart X.hom eX) (heZ : a3b4_IsHolChart Z.hom eZ)
    (hx : x ∈ (pointChart eX).source) (hz : Point.map f x ∈ (pointChart eZ).source)
    (U : Set (ComplexPoint X)) (hU : IsOpen U) (hxU : x ∈ U)
    (hisol : ∀ z ∈ U, Point.map f z = Point.map f x → z = x)
    (y : (ccm3_inverseIdeal f.left (Point.map f x).underlying).subscheme)
    (hy : (ccm3_inverseIdeal f.left (Point.map f x).underlying).subschemeι y = x.underlying)
    (hfin : ccm3_genericLength f.left (Point.map f x).underlying y < ⊤) :
    relativeHomologyMap ℚ (2 * d) (isolatedPairMap (TopCat.ofHom (Point.continuousMap f)) U x hisol)
      (neighborhoodOrientation d (pointChart eX) x hx U hU hxU) =
      (genericMultiplicity f.left (Point.map f x).underlying y hfin : ℚ) • localClassOfChart d (pointChart eZ) (Point.map f x) hz := finite_flat_local_degree_aux f d x eX eZ heX heZ hx hz U hU hxU hisol y hy hfin

example := finite_flat_local_degree_wrong_sign

/-- Ramified pullback of the normalized local coclass has the stalk-length factor.
Source: Fulton, Intersection Theory, second edition, §19.1;
Hatcher, Algebraic Topology, §3.1, evaluation naturality. -/
theorem finite_flat_local_coclass {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [Smooth X.hom] [Smooth Z.hom]
    [T1Space (ComplexPoint X)] (f : X ⟶ Z) [IsFinite f.left] [Flat f.left]
    (d : ℕ) (x : ComplexPoint X)
    (eX : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (eZ : OpenPartialHomeomorph (ComplexPoint Z) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (heX : a3b4_IsHolChart X.hom eX) (heZ : a3b4_IsHolChart Z.hom eZ)
    (hx : x ∈ (pointChart eX).source) (hz : Point.map f x ∈ (pointChart eZ).source)
    (U : Set (ComplexPoint X)) (hU : IsOpen U) (hxU : x ∈ U)
    (hisol : ∀ z ∈ U, Point.map f z = Point.map f x → z = x)
    (y : (ccm3_inverseIdeal f.left (Point.map f x).underlying).subscheme)
    (hy : (ccm3_inverseIdeal f.left (Point.map f x).underlying).subschemeι y = x.underlying)
    (hfin : ccm3_genericLength f.left (Point.map f x).underlying y < ⊤)
    (hsource : neighborhoodOrientation d (pointChart eX) x hx U hU hxU ≠ 0)
    (htarget : localClassOfChart d (pointChart eZ) (Point.map f x) hz ≠ 0) :
    relativeCohomologyMap ℚ (2 * d) (isolatedPairMap (TopCat.ofHom (Point.continuousMap f)) U x hisol)
      (normalizedRelativeCoclass (localClassOfChart d (pointChart eZ) (Point.map f x) hz) htarget) =
      (genericMultiplicity f.left (Point.map f x).underlying y hfin : ℚ) • normalizedRelativeCoclass
        (neighborhoodOrientation d (pointChart eX) x hx U hU hxU) hsource := finite_flat_local_coclass_aux f d x eX eZ heX heZ hx hz U hU hxU hisol y hy hfin hsource htarget

example := finite_flat_local_coclass_wrong_factor

/-- Prime collection adds repeated occurrences before deleting zero coefficients.
Source: Fulton, Intersection Theory, second edition, §1.5. -/
theorem collected_coefficients {ι : Type*} [Fintype ι] {Z : Scheme}
    (p : ι → Z) (a : ι → ℚ) (z : Z) :
    collectedCycle (collectPrimes p a) z = ∑ i, if p i = z then a i else 0 := collected_coefficients_aux p a z

example := collected_coefficients_wrong_last

/-- Proper pushforward retains the generic residue degree of every surviving prime.
Source: Stacks Project, Tag 02R4; Fulton, Intersection Theory, second edition, §1.4. -/
theorem proper_collected_pushforward {X Z : Scheme} (f : X ⟶ Z) [IsProper f]
    {N : Type*} [DecidableEq N] (wx : X → N) (wz : Z → N)
    (b : X →₀ ℚ) :
    AlgebraicCycle.map f wx wz (collectedCycle b) =
      ∑ x ∈ b.support, Function.locallyFinsuppWithin.single (f x)
        (if wx x = wz (f x) then (f.residueDegree x : ℚ) * b x else 0) := proper_collected_pushforward_aux f wx wz b

example := proper_collected_pushforward_wrong_dimension

/-- The support is computed after collection, so cancellation removes a prime.
Source: Fulton, Intersection Theory, second edition, §§1.5 and 19.1. -/
theorem collected_support {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (b : Z →₀ ℚ) :
    a3b4_cycleSupport q (collectedCycle b) = ⋃ p : b.support, primeSupport q p.1 := collected_support_aux q b

example := collected_support_wrong_union

/-- Forgetting support of the collected assembly retains each surviving weight.
Source: Hatcher, Algebraic Topology, §3.1;
`SupportedClasses.forget_weightedSum_aux` applied after prime collection. -/
theorem assembled_forget {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    (b : Z →₀ ℚ) (n : ℕ)
    (c : ∀ p : b.support, CohomologyWithSupport ℚ (a3b4_an q) (primeSupport q p.1) n) :
    forgetSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (collectedCycle b)) n
        (assembledClass q b n c) =
      ∑ p : b.support, b p.1 • forgetSupport ℚ (a3b4_an q) (primeSupport q p.1) n (c p) := assembled_forget_aux q b n c

example := assembled_forget_wrong_weight

/-- The collected assembly is locally normalized on the regular separated locus.
Source: Fulton, Intersection Theory, second edition, §19.1; Borel–Haefliger
(1961), §2; `SupportedCycleClasses.weightedSum_restrict_single`. -/
theorem assembled_normalized_on_locus {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (b : Z →₀ ℚ) (k : ℕ)
    (c : ∀ p : b.support, CohomologyWithSupport ℚ (a3b4_an q) (primeSupport q p.1) (2 * k))
    (hc : ∀ p : b.support, a3b4_IsCycleClass q
      (Function.locallyFinsuppWithin.single p.1 (1 : ℚ)) k (c p))
    (r : ℕ) (e : OpenPartialHomeomorph (a3b4_an q) ((Fin r → ℂ) × (Fin k → ℂ)))
    (he : a3b4_IsHolChart q e)
    (hflat : ∀ z ∈ e.source, z ∈ a3b4_cycleSupport q (collectedCycle b) ↔ (e z).2 = 0)
    (x : a3b4_an q) (hx : x ∈ e.source) (hxL : x ∈ regularSeparatedLocus q b k) :
    ∃ (W : Set (a3b4_an q)) (hW : W ⊆ e.source),
      IsOpen W ∧ x ∈ W ∧
      W ∩ a3b4_cycleSupport q (collectedCycle b) ⊆ regularSeparatedLocus q b k ∧
      relativeCohomologyMap ℚ (2 * k)
        (a3b4_neighborhoodPairMap W (a3b4_cycleSupport q (collectedCycle b)))
        (assembledClass q b (2 * k) c) =
      a3b4_multiplicity q (collectedCycle b) x •
        chartNormalProjectionCoclass (Fin r → ℂ) k e
          (a3b4_cycleSupport q (collectedCycle b)) hflat W hW := assembled_normalized_on_locus_aux q b k c hc r e he hflat x hx hxL

example := assembled_normalized_on_locus_wrong_unit

end AlgebraicGeometry.SingularCycles
