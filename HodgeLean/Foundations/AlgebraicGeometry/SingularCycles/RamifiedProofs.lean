import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedChecks
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedAssembly
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDuality
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeRegularParameters
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeParameterChart

/-! # Ramified generic chart and collected component obligations

Finite flat maps are tested on actual smooth complex point charts. The local
coefficient is the unreduced inverse-image stalk length. Rational assembly
collects equal primes and imposes local normalization on the regular separated locus.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem collectedCycle_coefficient {Z : Scheme} (b : Z →₀ ℚ) (p : Z) :
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


/-- The local complex degree of a finite flat map equals its fibre stalk length.
Source: Fulton, Intersection Theory, second edition, §§1.7 and 19.1;
Stacks Project, Tags 02MB and 0B01; Borel–Haefliger (1961), §2. -/
theorem finite_flat_local_degree_aux {X Z : Over (Spec ↧ℂ)}
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
      (genericMultiplicity f.left (Point.map f x).underlying y hfin : ℚ) • localClassOfChart d (pointChart eZ) (Point.map f x) hz := by
  obtain ⟨A, hA, hxA, g, η, hη, hxη, hη0, _hηsource, hvalues, hreg, hgen⟩ :=
    exists_centered_regular_parameter_chart Z d eZ heZ (Point.map f x) hz
  let m := genericMultiplicity f.left (Point.map f x).underlying y hfin
  have hm : pointFibreLength f.left x.underlying = (m : ℕ∞) := by
    have h := genericMultiplicity_eq_pointFibreLength f.left (Point.map f x).underlying y
      (by rw [hy]; rfl) hfin
    rw [hy] at h
    exact h.symm
  have hdegree := local_degree_from_regular_parameter_chart f d x eX η heX hx hη hxη hη0
    U hU hxU hisol A hA hxA g hvalues hreg hgen m hm
  rw [holomorphic_point_chart_orientation_independent Z d η eZ hη heZ
    (Point.map f x) hxη hz] at hdegree
  exact hdegree

example := finite_flat_local_degree_wrong_sign

/-- Ramified pullback of the normalized local coclass has the stalk-length factor.
Source: Fulton, Intersection Theory, second edition, §19.1;
Hatcher, Algebraic Topology, §3.1, evaluation naturality. -/
theorem finite_flat_local_coclass_aux {X Z : Over (Spec ↧ℂ)}
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
        (neighborhoodOrientation d (pointChart eX) x hx U hU hxU) hsource := by
  apply normalizedCoclass_pullback_of_generator
    (2 * d) _ _ hsource _ htarget
    (span_neighborhoodOrientation_eq_top d (pointChart eX) x hx U hU hxU)
  exact finite_flat_local_degree_aux f d x eX eZ heX heZ hx hz U hU hxU hisol y hy hfin

example := finite_flat_local_coclass_wrong_factor

/-- Prime collection adds repeated occurrences before deleting zero coefficients.
Source: Fulton, Intersection Theory, second edition, §1.5. -/
theorem collected_coefficients_aux {ι : Type*} [Fintype ι] {Z : Scheme}
    (p : ι → Z) (a : ι → ℚ) (z : Z) :
    collectedCycle (collectPrimes p a) z = ∑ i, if p i = z then a i else 0 := by
  classical
  rw [collectedCycle_coefficient]
  simp [collectPrimes, Finsupp.single_apply, eq_comm]

example := collected_coefficients_wrong_last

/-- Proper pushforward retains the generic residue degree of every surviving prime.
Source: Stacks Project, Tag 02R4; Fulton, Intersection Theory, second edition, §1.4. -/
theorem proper_collected_pushforward_aux {X Z : Scheme} (f : X ⟶ Z) [IsProper f]
    {N : Type*} [DecidableEq N] (wx : X → N) (wz : Z → N)
    (b : X →₀ ℚ) :
    AlgebraicCycle.map f wx wz (collectedCycle b) =
      ∑ x ∈ b.support, Function.locallyFinsuppWithin.single (f x)
        (if wx x = wz (f x) then (f.residueDegree x : ℚ) * b x else 0) := by
  classical
  ext z
  simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply,
    collectedCycle_coefficient, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply, Function.locallyFinsuppWithin.single_apply]
  rw [finsum_mem_def]
  rw [finsum_eq_finsetSum_of_support_subset (s := b.support)]
  · apply Finset.sum_congr rfl
    intro x hx
    by_cases hf : f x = z
    · subst z
      by_cases hw : wx x = wz (f x) <;>
        simp [hw, AlgebraicCycle.mapCoeff, mul_comm]
    · have hf' : z ≠ f x := Ne.symm hf
      simp [hf, hf']
  · intro x hx
    by_contra hn
    have hb : b x = 0 := Finsupp.notMem_support_iff.mp hn
    simp [Set.indicator_apply, hb] at hx

example := proper_collected_pushforward_wrong_dimension

/-- The support is computed after collection, so cancellation removes a prime.
Source: Fulton, Intersection Theory, second edition, §§1.5 and 19.1. -/
theorem collected_support_aux {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (b : Z →₀ ℚ) :
    a3b4_cycleSupport q (collectedCycle b) = ⋃ p : b.support, primeSupport q p.1 := by
  classical
  ext x
  simp only [a3b4_cycleSupport, Set.mem_preimage, Set.mem_iUnion,
    Function.mem_support, collectedCycle_coefficient]
  constructor
  · rintro ⟨p, hp, hx⟩
    exact ⟨⟨p, Finsupp.mem_support_iff.mpr hp⟩, by
      simpa [primeSupport, a3b4_cycleSupport] using hx⟩
  · rintro ⟨p, hx⟩
    exact ⟨p.1, Finsupp.mem_support_iff.mp p.2, by
      simpa [primeSupport, a3b4_cycleSupport] using hx⟩

example := collected_support_wrong_union

/-- Forgetting support of the collected assembly retains each surviving weight.
Source: Hatcher, Algebraic Topology, §3.1;
`SupportedClasses.forget_weightedSum_aux` applied after prime collection. -/
theorem assembled_forget_aux {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    (b : Z →₀ ℚ) (n : ℕ)
    (c : ∀ p : b.support, CohomologyWithSupport ℚ (a3b4_an q) (primeSupport q p.1) n) :
    forgetSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (collectedCycle b)) n
        (assembledClass q b n c) =
      ∑ p : b.support, b p.1 • forgetSupport ℚ (a3b4_an q) (primeSupport q p.1) n (c p) := by
  exact SupportedClasses.forget_weightedSum_aux _ _ _ _ _ _ _

example := assembled_forget_wrong_weight

/-- The collected assembly is locally normalized on the regular separated locus.
Source: Fulton, Intersection Theory, second edition, §19.1; Borel–Haefliger
(1961), §2; `SupportedCycleClasses.weightedSum_restrict_single`. -/
theorem assembled_normalized_on_locus_aux {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
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
          (a3b4_cycleSupport q (collectedCycle b)) hflat W hW := by
  classical
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  obtain ⟨p, hxp, hoffx, rp, ep, hep, hxep, hflatp⟩ := hxL
  let S := fun t : b.support => primeSupport q t.1
  let T := a3b4_cycleSupport q (collectedCycle b)
  have hST : ∀ t : b.support, S t ⊆ T := by
    intro t y hy
    rw [show T = ⋃ t : b.support, S t from collected_support_aux q b]
    exact Set.mem_iUnion.mpr ⟨t, hy⟩
  have ha : b p.1 ≠ 0 := Finsupp.mem_support_iff.mp p.2
  obtain ⟨V, hxV, hoff⟩ := separatedPrime_neighborhood q b p x hoffx
  have hlocal : ∀ y ∈ (V : Set (a3b4_an q)), y ∈ T ↔ y ∈ S p := by
    intro y hy
    constructor
    · intro hyT
      rw [show T = ⋃ t : b.support, S t from collected_support_aux q b] at hyT
      obtain ⟨t, hyt⟩ := Set.mem_iUnion.mp hyT
      by_cases ht : t = p
      · exact ht ▸ hyt
      · exact (hoff t ht y hy hyt).elim
    · exact fun h => hST p h
  let e' := e.restrOpen (V : Set (a3b4_an q)) V.isOpen
  have he' : a3b4_IsHolChart q e' := by
    constructor
    · intro j
      exact anrem_isHolFun_restrict (f4_analytification (Over.mk q))
        (fun _ h => h.1) (he.1 j)
    · intro j
      exact anrem_isHolFun_restrict (f4_analytification (Over.mk q))
        (fun _ h => h.1) (he.2 j)
  have hflat' : ∀ y ∈ e'.source, y ∈ S p ↔ (e' y).2 = 0 := by
    intro y hy
    exact (hlocal y hy.2).symm.trans (hflat y hy.1)
  obtain ⟨W, hWe', hWo, hxW, hnorm⟩ := hc p r e' hflat' x ⟨hx, hxV⟩ hxp he'
  change relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap W (S p)) (c p) =
    a3b4_multiplicity q (Function.locallyFinsuppWithin.single p.1 (1 : ℚ)) x •
      chartNormalProjectionCoclass (Fin r → ℂ) k e' (S p) hflat' W hWe' at hnorm
  have hWe : W ⊆ e.source := fun _ hy => (hWe' hy).1
  have hWA : W ⊆ (V : Set (a3b4_an q)) := fun _ hy => (hWe' hy).2
  have hmult : a3b4_multiplicity q (collectedCycle b) x = b p.1 := by
    rw [a3b4a_classMultiplicity_eq_component q (collectedCycle b) p.1
      (by change collectedCycle b p.1 ≠ 0; rwa [collectedCycle_coefficient]) x
      (by simpa [primeSupport, a3b4_cycleSupport] using hxp)]
    · exact collectedCycle_coefficient b p.1
    · intro t ht hne
      have ht' : t ∈ b.support := by
        apply Finsupp.mem_support_iff.mpr
        simpa only [Function.mem_support, collectedCycle_coefficient] using ht
      have := hoffx ⟨t, ht'⟩ (fun h => hne (congrArg Subtype.val h))
      simpa [primeSupport, a3b4_cycleSupport] using this
  have hunit := prime_multiplicity_at q p.1 x hxp
  refine ⟨W, hWe, hWo, hxW, ?_, ?_⟩
  · intro y hy
    have hyp : y ∈ S p := (hlocal y (hWA hy.1)).mp hy.2
    exact ⟨p, hyp, fun t ht => hoff t ht y (hWA hy.1), r, e', he', hWe' hy.1, hflat'⟩
  · change relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap W T)
      (SupportedClasses.weightedSum (a3b4_an q) (2 * k) S T
        (fun t : b.support => b t.1) (fun t _ => hST t) c) = _
    rw [SupportedCycleClasses.weightedSum_restrict_single _ _ _ _ _ _ _ p ha W
      (fun t ht y hy => hoff t ht y (hWA hy)), hnorm, hunit, one_smul,
      SupportedCycleClasses.localSupportMap_normalCoclass r k W (S p) T
        (fun y _ hy => hST p hy) e' e hflat' hflat hWe' hWe (fun _ _ => rfl), hmult]

example := assembled_normalized_on_locus_wrong_unit

end AlgebraicGeometry.SingularCycles
